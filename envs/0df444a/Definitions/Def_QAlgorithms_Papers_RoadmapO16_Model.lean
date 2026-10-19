-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapO16_Model
-- name    : QAlgorithms_Papers_RoadmapO16_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:29:24.126776+00:00
-- url     : https://prove2.me/theorems/58375be5-d8e6-468e-816a-4c9562e95b8d
-- title:
--   Fast Convex Optimization with Quantum Gradient Methods: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Fast Convex Optimization with Quantum Gradient Methods, arXiv:2503.17356v2, https://arxiv.org/abs/2503.17356v2. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_NoisyOptimizationPrograms
/-!
# Fast zeroth-order nonsmooth convex optimization
Source: arXiv:2503.17356v2, Theorem 2.1 (PDF p.6), formal specifications
B.3 (pp.29–30) and C.1 (pp.32–34), Lemma A.1 (pp.22–23).
Local definitions below are submitted for definition review. They supply adaptive,
grid-preserving execution, without assuming successful subgradient estimates.
-/

noncomputable section

open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapO16

open QAlgorithms.ValueAccess QAlgorithms.NoisyOptimization

abbrev Point (d : ℕ) := Fin d → ℝ

/-- The selected p-norm, including infinity (PDF pp.4,18). -/
def pNorm {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (v : Point d) : ℝ :=
  ‖(WithLp.toLp p v : PiLp p (fun _ : Fin d => ℝ))‖

/-- Holder conjugate, including the endpoints. -/
def dualExponent (p : ℝ≥0∞) : ℝ≥0∞ :=
  if p = 1 then ∞ else if p = ∞ then 1 else ENNReal.ofReal (p.toReal / (p.toReal - 1))

/-- Diameter computed from the feasible set, not an independent radius. -/
def diameter {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (X : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  Metric.diam ((fun v => (WithLp.toLp p (WithLp.ofLp v) : PiLp p (fun _ : Fin d => ℝ))) '' X)

/-- Ambient convexity and Lipschitz control in B.3/C.1 and Lemma A.1. -/
def Objective {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (G : ℝ) (f : Point d → ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧ ∀ x y, |f x - f y| ≤ G * pNorm p (x - y)

/-- Attained constrained optimum (OPT, PDF p.3). -/
def Optimum {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (f : Point d → ℝ)
    (xstar : Point d) : Prop :=
  WithLp.toLp 2 xstar ∈ X ∧ ∀ x, WithLp.toLp 2 x ∈ X → f xstar ≤ f x

/-- The radius sqrt(D_Phi(xstar,x1)) is constructed from Phi (C.1, p.32). -/
def mirrorRadius {d : ℕ} (D : MirrorProjectionDomain (EuclideanSpace ℝ (Fin d)))
    (xstar x1 : Point d) : ℝ :=
  Real.sqrt (bregmanDiv D.mirror.Phi (WithLp.toLp 2 xstar) (WithLp.toLp 2 x1))

/-- Strong convexity on X intersect P, in the chosen WithLp norm (p.32). -/
def MirrorStrong {d : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (D : MirrorProjectionDomain (EuclideanSpace ℝ (Fin d))) (mu : ℝ) : Prop :=
  StrongConvexOn
    {v : PiLp p (fun _ : Fin d => ℝ) |
      WithLp.toLp 2 (WithLp.ofLp v) ∈ D.mirror.feasible ∩ D.mirror.domain}
    mu (fun v => D.mirror.Phi (WithLp.toLp 2 (WithLp.ofLp v)))

/-- Compiled Lemma-A.1 calls at each classical center. The actual Jordan output law
and exact grid index are specified by the frozen compilation's realizes field.
No subgradient accuracy or probability conclusion is a field of this structure. -/
structure SubgradientImplementation (d b : ℕ) (G theta rho r1 : ℝ) where
  gridSize : ℕ
  gridSize_pos : 0 < gridSize
  stateSize : ℕ
  repeats : ℕ
  encoding : FixedPointEncoding b
  jordan : Point d → JordanCompilation d b repeats (Fin gridSize) (Fin stateSize)
  roundAt : Point d → OptimizationRound d (Fin gridSize × Qubits b) (Fin stateSize)
  aligned : ∀ x,
    (roundAt x).procedure = (jordan x).procedure ∧
    (jordan x).grid.x = x ∧ (jordan x).L = G ∧ (jordan x).delta = theta ∧
    (jordan x).rho = rho ∧ (jordan x).grid.r1 = r1 ∧ (jordan x).encoding = encoding

/-- Definition-1 binary access on each translated finite grid. The grid index is
preserved on ALL value-register inputs, with strict error less than theta.
Both the unitary and its adjoint are available. -/
def ValidAccess {d b : ℕ} {G theta rho r1 : ℝ}
    (S : SubgradientImplementation d b G theta rho r1) (f : Point d → ℝ)
    (U : Point d → Matrix (Fin S.gridSize × Qubits b) (Fin S.gridSize × Qubits b) ℂ)
    (centers : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  letI : NeZero S.gridSize := ⟨(Nat.ne_of_gt S.gridSize_pos)⟩
  ∀ x, WithLp.toLp 2 x ∈ centers →
    IsApproxBinaryValueOracle (S.jordan x).grid.point S.encoding.value true f theta (U x)

/-- Adaptive average-iterate loop. Resources 0,1,2 count oracle calls (including
adjoints), quantum gates, and supplied geometry operations. The next oracle call
uses the current branch's center; independence of iterations is not assumed. -/
def runLeaves {d b : ℕ} {G theta rho r1 : ℝ}
    (S : SubgradientImplementation d b G theta rho r1)
    (U : Point d → Matrix (Fin S.gridSize × Qubits b) (Fin S.gridSize × Qubits b) ℂ)
    (nextOps : Point d → Point d → List (Point d → Point d)) (T : ℕ) :
    ℕ → Point d → Point d → List (OptimizationLeaf d)
  | 0, _, total => [(((T : ℝ)⁻¹ • total, 0), 1)]
  | fuel + 1, x, total =>
      (List.finRange (S.roundAt x).procedure.seeds).flatMap fun seed =>
        (List.finRange S.stateSize).flatMap fun z =>
          let P := S.roundAt x
          let g := P.procedure.decode seed z
          let ops := nextOps x g
          let xn := ops.foldl (fun v op => op v) x
          let weight := (P.procedure.seeds : ℝ)⁻¹ *
            prob (act ((P.procedure.circuit seed).unitary (fun _ => U x))
              (P.procedure.initial seed)) z
          (runLeaves S U nextOps T fuel xn (total + x)).map fun leaf =>
            ((leaf.1.1, leaf.1.2 + fun j =>
              if j = 0 then (P.gates seed).queryCount 0
              else if j = 1 then (P.gates seed).gateCount else ops.length), weight * leaf.2)

/-- Classical feasible epsilon-optimal output with probability at least 2/3. -/
def Successful {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (f : Point d → ℝ)
    (xstar : Point d) (eps : ℝ) (leaves : List (OptimizationLeaf d)) : Prop :=
  (open Classical in
    (leaves.map fun leaf =>
      if WithLp.toLp 2 leaf.1.1 ∈ X ∧ f leaf.1.1 - f xstar ≤ eps then leaf.2 else 0).sum) ≥ 2 / 3

/-- Bounds on positive-probability branches. Binary word length and inverse
precision enter the suppressed arithmetic factors; geometry costs stay explicit. -/
def ResourceBound {d : ℕ} (C : ℝ) (power b T nextCost : ℕ)
    (G R theta : ℝ) (leaves : List (OptimizationLeaf d)) : Prop :=
  let logs := max 1 ((b : ℝ) + Real.log (2 + d + T) +
    |Real.log theta| + |Real.log G| + |Real.log R|)
  ∀ leaf ∈ leaves, 0 < leaf.2 →
    (leaf.1.2 0 : ℝ) ≤ C * T * max 1 (Real.log (3 * d * T)) ∧
    (leaf.1.2 1 : ℝ) ≤ C * d * T * logs ^ power ∧
    leaf.1.2 2 ≤ T * nextCost

/-- Zero-query feasible start, evaluated before divisions at degenerate inputs. -/
def startLeaves {d : ℕ} (x1 : Point d) : List (OptimizationLeaf d) :=
  [((x1, 0), 1)]

/-- Failure probability per call, conditional on past outcomes (pp.30,34). -/
def failureBudget (T : ℕ) : ℝ := 1 / (3 * (T : ℝ))

/-- Full independent-K noise budget on p.30, correcting the printed B.3 precision. -/
def ProjectedPrecision (d T : ℕ) (G R K eps theta : ℝ) : Prop :=
  let rho := failureBudget T
  let r1 := eps / (6 * G * Real.sqrt d)
  IsPermittedPrecision false d T theta G R K rho r1 0 0 0 eps

/-- All four terms from pp.33–34, also imposing Lemma-A.1's domain guard. -/
def MirrorPrecision (d T : ℕ) (G R K mu vartheta varthetaDual eps theta : ℝ) : Prop :=
  let rho := failureBudget T
  let r1 := eps / (6 * G * vartheta)
  IsPermittedPrecision true d T theta G R K rho r1 mu vartheta varthetaDual eps

/-- B.3: supplied geometry; the algorithm constructor precedes the unknown
objective, optimum and oracles. Only the numerical radius is supplied to it. -/
def ProjectedContract (C : ℝ) (power : ℕ) : Prop :=
  ∀ (d b : ℕ) (H : GeometryImplementation d) (x1 : Point d)
    (G eps : ℝ) (enc : FixedPointEncoding b) (projectionCost : ℕ),
    Bornology.IsBounded H.euclideanSet →
    WithLp.toLp 2 x1 ∈ H.euclideanSet →
    (∀ y, (H.euclideanOps y).length ≤ projectionCost) →
    0 ≤ G → 0 < eps → eps < 1 →
    ∃ construct : (R theta : ℝ) → Option
      (SubgradientImplementation d b G theta
        (failureBudget (projectedIterations G R eps)) (eps / (6 * G * Real.sqrt d))),
    ∀ (f : Point d → ℝ) (xstar : Point d), Objective 2 G f →
    Optimum H.euclideanSet f xstar →
    let R := pNorm 2 (x1 - xstar)
    let K := diameter 2 H.euclideanSet
    if 0 < d ∧ 0 < G ∧ 0 < R ∧ eps < G * R ∧ eps < G * K then
      ∀ theta : ℝ, ProjectedPrecision d (projectedIterations G R eps) G R K eps theta →
        ∃ S, construct R theta = some S ∧ S.encoding = enc ∧
          ∀ U, ValidAccess S f U H.euclideanSet →
            let T := projectedIterations G R eps
            let eta := R / (G * Real.sqrt T)
            let ops := fun (x g : Point d) =>
              [fun (_ : Point d) => x - eta • g] ++
                (H.euclideanOps (WithLp.toLp 2 (x - eta • g))).map
                  (fun op v => WithLp.ofLp (op (WithLp.toLp 2 v)))
            let leaves := runLeaves S U ops T T x1 0
            Successful H.euclideanSet f xstar eps leaves ∧
              ResourceBound C power b T (projectionCost + 1) G R theta leaves
    else Successful H.euclideanSet f xstar eps (startLeaves x1)

/-- C.1: chosen p-norm; full Definition-4 mirror assumptions in the domain.
The constructor precedes f, xstar and U. R is computed from the Bregman divergence.
No full ambient interior of X is required. -/
def MirrorContract (C : ℝ) (power : ℕ) : Prop :=
  ∀ (d b : ℕ) (p : ℝ≥0∞) (_ : Fact (1 ≤ p)) (_ : Fact (1 ≤ dualExponent p)),
    p ≠ 2 →
    ∀ (D : MirrorProjectionDomain (EuclideanSpace ℝ (Fin d))) (x1 : Point d)
      (G mu vartheta varthetaDual eps : ℝ) (enc : FixedPointEncoding b)
      (updateCost : ℕ)
      (nextOps : ℝ → Point d → Point d → List (Point d → Point d)),
    IsClosed D.mirror.feasible → Bornology.IsBounded D.mirror.feasible →
    Convex ℝ D.mirror.feasible →
    WithLp.toLp 2 x1 ∈ D.mirror.feasible ∩ D.mirror.domain →
    MirrorStrong p D mu → 0 < mu →
    1 ≤ vartheta → vartheta ≤ d → 1 ≤ varthetaDual → varthetaDual ≤ d →
    vartheta * varthetaDual ≤ d →
    (∀ v : Point d, pNorm p v ≤ vartheta * ‖v‖) →
    (∀ v : Point d, pNorm (dualExponent p) v ≤ varthetaDual * ‖v‖) →
    (∀ eta x g, WithLp.toLp 2 x ∈ D.mirror.domain →
      (nextOps eta x g).foldl (fun v op => op v) x = mirrorNextPoint D eta x g) →
    (∀ eta x g, (nextOps eta x g).length ≤ updateCost) →
    0 ≤ G → 0 < eps → eps < 1 →
    ∃ construct : (R theta : ℝ) → Option
      (SubgradientImplementation d b G theta
        (failureBudget (mirrorIterations G R mu eps)) (eps / (6 * G * vartheta))),
    ∀ (f : Point d → ℝ) (xstar : Point d), Objective p G f →
    Optimum D.mirror.feasible f xstar → WithLp.toLp 2 xstar ∈ D.mirror.domain →
    let R := mirrorRadius D xstar x1
    let K := diameter p D.mirror.feasible
    if 0 < d ∧ 0 < G ∧ 0 < R ∧ eps < G * R * Real.sqrt (2 / mu) ∧ eps < G * K then
      ∀ theta : ℝ,
        MirrorPrecision d (mirrorIterations G R mu eps) G R K mu vartheta varthetaDual eps theta →
        ∃ S, construct R theta = some S ∧ S.encoding = enc ∧
          ∀ U, ValidAccess S f U (D.mirror.feasible ∩ D.mirror.domain) →
            let T := mirrorIterations G R mu eps
            let eta := R / G * Real.sqrt (mu / T)
            let leaves := runLeaves S U (nextOps eta) T T x1 0
            Successful D.mirror.feasible f xstar eps leaves ∧
              ResourceBound C power b T updateCost G R theta leaves
    else Successful D.mirror.feasible f xstar eps (startLeaves x1)


example {d b : ℕ} {G theta rho r1 : ℝ}
    (S : SubgradientImplementation d b G theta rho r1)
    (U : Point d → Matrix (Fin S.gridSize × Qubits b) (Fin S.gridSize × Qubits b) ℂ)
    (ops : Point d → Point d → List (Point d → Point d)) (T : ℕ) (x total : Point d) :
    runLeaves S U ops T 0 x total = [(((T : ℝ)⁻¹ • total, 0), 1)] := rfl

example {d : ℕ} (x : Point d) : startLeaves x = [((x, 0), 1)] := rfl

end QAlgorithms.Papers.RoadmapO16


