-- Prove2me | Definitions.Def_NondualStable_Optimization_Bundle
-- name    : NondualStable_Optimization_Bundle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:13.117739+00:00
-- url     : https://prove2.me/theorems/0c8d9177-247b-4341-991b-fcd4a9e8f713
-- title:
--   First-order histories and operational Stable Movement Bundle Method
-- statement:
--   An oracle answer at $x$ consists of the value $f(x)$ and a vector $g$ with $\|g\|_{q^*}\le G$ satisfying the subgradient inequality against every feasible point. The oracle may depend on the complete previous query-and-answer history. Its measurable interface is expressed on each finite history length.
--
--   The bundle is the maximum of every stored affine oracle cut. Initialization queries zero, stores that cut and sets $U=f(0)$, $x_{\rm best}=0$ and $\ell=f(0)-2GR$. A phase freezes its starting bundle index, lower bound, gap $\Gamma$ and levels
--   $$h^-=\ell+\Gamma/4,\qquad h^+=\ell+3\Gamma/4.$$
--   Before querying a center, a model solver supplies a feasible point and certified lower/upper values of width at most $\Gamma/32$. The lower-bound stopping test is performed first. Otherwise a center is queried, the best value is updated and its cut is stored, including on serious steps. Both phase-ending branches restart the phase. Termination is tested against the actual certified gap between phases, as in the outer loop of Algorithm 1. The approximate-center contract requires reference sequences and their movement bounds only along prefixes of the actual queried requests within each phase; it imposes no stability condition on unrelated request sequences.
--
--   Selectors take only the request prefix, allowing online dependence on previous requests. The macro-step solver and provider are mathematical analysis interfaces; they grant no free instructions to the real machine. No termination or complexity property is a field of an execution.
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed pp. 5–8/PDF pp. 6–9, Section 2, Algorithm 1, (4)–(7); printed pp. 19–20/PDF pp. 20–21, Appendix D

import Definitions.Def_NondualStable_Optimization_Geometry

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

structure Answer (d : ℕ) where
  val : ℝ
  grad : Vec d

structure Observation (d : ℕ) where
  point : Vec d
  answer : Answer d

abbrev History (d : ℕ) := List (Observation d)
abbrev Oracle (d : ℕ) := History d → Vec d → Answer d

def ValidOracle {d : ℕ} (p q : ℝ≥0∞) (G R : ℝ) (f : Vec d → ℝ)
    (O : Oracle d) : Prop :=
  ∀ h x, x ∈ ball p R →
    (O h x).val = f x ∧ lpNorm (dual q) (O h x).grad ≤ G ∧
    ∀ y ∈ ball p R, f x + dotProduct (O h x).grad (y - x) ≤ f y

def OracleMeasurable {d : ℕ} (O : Oracle d) : Prop :=
  ∀ n, Measurable (fun a : (Fin n → Vec d × (ℝ × Vec d)) × Vec d =>
    let h := (List.finRange n).map (fun i =>
      (⟨(a.1 i).1, ⟨(a.1 i).2.1, (a.1 i).2.2⟩⟩ : Observation d))
    ((O h a.2).val, (O h a.2).grad))

noncomputable def cut {d : ℕ} (o : Observation d) (x : Vec d) : ℝ :=
  o.answer.val + dotProduct o.answer.grad (x - o.point)

/-- A maximum of every stored affine cut. The empty history is used only off-domain. -/
noncomputable def bundle {d : ℕ} (h : History d) (x : Vec d) : ℝ :=
  match h with
  | [] => 0
  | o :: os => os.foldl (fun a b => max a (cut b x)) (cut o x)

structure Phase where
  lower : ℝ
  gap : ℝ
  start : ℕ

noncomputable def low (φ : Phase) : ℝ := φ.lower + φ.gap / 4
noncomputable def high (φ : Phase) : ℝ := φ.lower + 3 * φ.gap / 4

structure BundleState (d : ℕ) where
  history : History d
  lower : ℝ
  upper : ℝ
  best : Vec d
  phase : Option Phase
  done : Bool

noncomputable def activePhase {d : ℕ} (s : BundleState d) : Phase :=
  s.phase.getD ⟨s.lower, s.upper - s.lower, s.history.length⟩

def levelBody {d : ℕ} (p : ℝ≥0∞) (R : ℝ) (s : BundleState d) : Set (Vec d) :=
  {x | x ∈ ball p R ∧ bundle s.history x ≤ low (activePhase s)}

/-- Requests already seen in the current phase, including the current body.
The frozen start index is the bundle size when this phase began. -/
noncomputable def phaseBodies {d : ℕ} (p : ℝ≥0∞) (R : ℝ) (s : BundleState d) : List (Set (Vec d)) :=
  let φ := activePhase s
  (List.range (s.history.length - φ.start + 1)).map (fun k =>
    {x | x ∈ ball p R ∧ bundle (s.history.take (φ.start + k)) x ≤ low φ})

def requestPrefix {d : ℕ} (K : ℕ → Set (Vec d)) (t : ℕ) : List (Set (Vec d)) :=
  (List.range (t + 1)).map K

structure ModelCertificate (d : ℕ) where
  a : ℝ
  b : ℝ
  y : Vec d

def Certified {d : ℕ} (p : ℝ≥0∞) (R : ℝ) (s : BundleState d)
    (c : ModelCertificate d) : Prop :=
  c.y ∈ ball p R ∧
  (∀ x ∈ ball p R, c.a ≤ bundle s.history x) ∧
  bundle s.history c.y ≤ c.b ∧ c.b - c.a ≤ (activePhase s).gap / 32

abbrev ModelSolver (d : ℕ) := BundleState d → ModelCertificate d
abbrev CenterProvider (d : ℕ) := BundleState d → Vec d

def ValidModelSolver {d : ℕ} (p : ℝ≥0∞) (R : ℝ) (S : ModelSolver d) : Prop :=
  ∀ s, s.history ≠ [] → 0 < (activePhase s).gap → Certified p R s (S s)

def FeasibleProvider {d : ℕ} (p : ℝ≥0∞) (R : ℝ)
    (_S : ModelSolver d) (A : CenterProvider d) : Prop :=
  ∀ s, Body p R (levelBody p R s) → A s ∈ levelBody p R s

noncomputable def bundleInit {d : ℕ} (G R : ℝ) (O : Oracle d) : BundleState d :=
  let a := O [] 0
  ⟨[⟨0, a⟩], a.val - 2 * G * R, a.val, 0, none, false⟩

/-- Algorithm 1, lines 2–13. The model solver is an analysis interface, not
a primitive in the costed machine. Both serious and null steps store the new cut. -/
noncomputable def bundleStep {d : ℕ} (ε : ℝ) (O : Oracle d)
    (S : ModelSolver d) (A : CenterProvider d) (s : BundleState d) : BundleState d := by
  classical
  exact if s.done then s else
    if s.phase = none ∧ s.upper - s.lower ≤ ε then {s with done := true} else
    let φ := activePhase s
    let c := S s
    if φ.lower + φ.gap / 8 ≤ c.a then
      {s with lower := max s.lower c.a, phase := none}
    else
      let z := A s
      let a := O s.history z
      let better := a.val < s.upper
      {s with
        history := s.history ++ [⟨z, a⟩]
        upper := if better then a.val else s.upper
        best := if better then z else s.best
        phase := if a.val ≤ high φ then none else some φ}

noncomputable def bundleRun {d : ℕ} (G R ε : ℝ) (O : Oracle d)
    (S : ModelSolver d) (A : CenterProvider d) (n : ℕ) : BundleState d :=
  (bundleStep ε O S A)^[n] (bundleInit G R O)

def CertifiedOutput {d : ℕ} (p : ℝ≥0∞) (R ε : ℝ) (f : Vec d → ℝ)
    (s : BundleState d) : Prop :=
  s.best ∈ ball p R ∧ s.upper = f s.best ∧
  (∀ x ∈ ball p R, s.lower ≤ f x) ∧ f s.best ≤ s.lower + ε

def StableSelector {d : ℕ} (p q : ℝ≥0∞) (R ρ A : ℝ) (k : ℕ)
    (C : List (Set (Vec d)) → Vec d) : Prop :=
  (∀ H : ℕ, ∀ K : ℕ → Set (Vec d), Nested p R H K →
    ∀ t ≤ H, C (requestPrefix K t) ∈ K t) ∧
  ∀ H : ℕ, 1 ≤ H → ∀ K : ℕ → Set (Vec d), Nested p R H K →
    movement q H (fun t => C (requestPrefix K t)) ≤
      A * R * (H : ℝ) ^ (1 - ρ) * (logFactor d H) ^ k

/-- The branch on which Algorithm 1 actually requests a center. The outer
accuracy test is applied only between phases, as in lines 2 and 12. -/
def CenterQuery {d : ℕ} (ε : ℝ) (S : ModelSolver d) (s : BundleState d) : Prop :=
  s.done = false ∧ (s.phase ≠ none ∨ ε < s.upper - s.lower) ∧
    (S s).a < (activePhase s).lower + (activePhase s).gap / 8

/-- Lemma 6 assumes a reference sequence only along each actual phase.
It need not extend to a selector stable on other nested request sequences.
The reference sequence is fixed before its prefix length is chosen. -/
def ApproximateProvider {d : ℕ} (p q : ℝ≥0∞) (G R ε ρ B : ℝ) (k : ℕ)
    (O : Oracle d) (S : ModelSolver d) (A : CenterProvider d) : Prop :=
  ∀ n : ℕ,
    let s := fun t => bundleRun G R ε O S A (n + t)
    (s 0).phase = none →
    ∃ z : ℕ → Vec d, ∀ N : ℕ,
      (∀ t ≤ N, CenterQuery ε S (s t) ∧ activePhase (s t) = activePhase (s 0)) →
      (∀ t ≤ N, z t ∈ levelBody p R (s t) ∧ A (s t) ∈ levelBody p R (s t) ∧
        lpNorm q (A (s t) - z t) ≤ (activePhase (s 0)).gap / (16 * G)) ∧
      (1 ≤ N → movement q N z ≤
        B * R * (N : ℝ) ^ (1 - ρ) * (logFactor d N) ^ k)

end NondualStable.Optimization


