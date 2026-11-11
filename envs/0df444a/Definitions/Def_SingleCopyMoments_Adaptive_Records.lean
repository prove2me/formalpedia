-- Prove2me | Definitions.Def_SingleCopyMoments_Adaptive_Records
-- name    : SingleCopyMoments_Adaptive_Records
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T09:48:28.238739+00:00
-- url     : https://prove2.me/theorems/71d501d5-c5ba-48f5-adb7-a5d4d799b7a1
-- title:
--   Original experiment, rank-one representation, retained matrices and ordered cycles
-- statement:
--   A rank-one refinement supplies a measurable unit vector at each round, seed, past, and outcome. Its density representation must equal the underlying POVM effects when integrated against that POVM's reference kernel on $I/d$. This is an analysis representation of a protocol; the goal still quantifies over every published protocol without any refinement premise. The reference law is that original protocol on $I/d$.
--
--   The physical input is $\rho_\theta(g)$ on its density-matrix domain and $I/d$ as an explicit dummy elsewhere. The prior's support property makes the dummy branch null. The ensemble and joint laws first draw $g$ once from the physical prior and then run all $T$ rounds on that same state, retaining the seed in the record. Set
--
--   $$S_n=\sum_{i\le n}P_i,\quad G_\kappa=\{\|S_T\|_{op}<\kappa\},\quad\widehat Y_i=\frac{P_i-I/d}{f_i},\quad Y_i=1_{\{\|S_{i-1}\|_{op}<\kappa\}}\widehat Y_i.$$
--
--   The retained sum includes the threshold-crossing observation. The actual experiment always runs all rounds. Chains sum ordered injective tuples, $A_{s,N}=\sum Y_{i_1}\cdots Y_{i_s}$, and cycles are their complex traces. Raw cycles use $\widehat Y$. Products preserve order and the sums vanish when $s>N$. The numeric constant predicate specifies precisely the prefactor domination used to choose the order-independent $A=A(K)$ in (7.31); it contains no stochastic conclusion. The lower-closure parameter predicate records (7.1) and (7.44).
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), §5.4 rank-one refinement, printed p. 20 (PDF p. 22); §7.2–§7.4, (7.16)–(7.17), (7.22), (7.28), (7.31), (7.44), printed pp. 35–46 (PDF pp. 37–48). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Ensemble

open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder
noncomputable section

namespace SingleCopyMoments.Adaptive

/-- Supply an explicit dummy only outside the physical cutoff's support. -/
def physicalInput {d r : ℕ} (hd : 0 < d) (α θ : ℝ) (g : Latent d r) : State d := by
  classical
  exact if h : ProjectiveMeasurementEquilibration.IsDensityMatrix (hardMatrix α θ g) then
    ⟨hardMatrix α θ g, h⟩ else canonicalState d hd

def historyPrefix {d : ℕ} {P : Protocol d} (H : Record P) (n : ℕ) : Record P :=
  (H.1, fun i => if i < n then H.2 i else Sum.inl ())

/-- A rank-one density representation of a protocol's POVMs, not a restriction
on the main theorem. The reference kernel is the same POVM at I/d. -/
structure Refinement {d : ℕ} (hd : 0 < d) (P : Protocol d) where
  vector : ℕ → Record P → P.Outcome → (Fin d → ℂ)
  measurable_vector : ∀ i, Measurable (Function.uncurry (vector i))
  unit_vector : ∀ i H y, vectorSq (vector i H y) = 1
  effect_eq : ∀ i H A, MeasurableSet A →
    (P.measurement i H).effect A = (d : ℝ) •
      ∫ y in A, outer (vector i H y) ∂(P.step i (canonicalState d hd, H))

def observedVector {d : ℕ} {hd : 0 < d} {P : Protocol d} (R : Refinement hd P)
    (i : ℕ) (H : Record P) : Fin d → ℂ :=
  match H.2 i with
  | Sum.inr y => R.vector i (historyPrefix H i) y
  | Sum.inl _ => fun j => if j.val = 0 then 1 else 0

def projectors {d : ℕ} {hd : 0 < d} {P : Protocol d} (R : Refinement hd P)
    (N : ℕ) (H : Record P) : FrozenHistory d N := fun i => outer (observedVector R i.val H)

def projectorSum {d N : ℕ} (H : FrozenHistory d N) : Op d := ∑ i, H i

def goodRecords {d : ℕ} {hd : 0 < d} {P : Protocol d} (R : Refinement hd P)
    (T : ℕ) (κ : ℝ) : Set (Record P) := {H | opNorm (projectorSum (projectors R T H)) < κ}

def referenceLaw {d : ℕ} (hd : 0 < d) (P : Protocol d) (T : ℕ) :=
  law P (canonicalState d hd) T

def ensembleLaw {d : ℕ} (hd : 0 < d) (P : Protocol d) (r : ℕ) (α θ : ℝ) (T : ℕ) :=
  (prior d r α θ).bind (fun g => law P (physicalInput hd α θ g) T)

def jointLaw {d : ℕ} (hd : 0 < d) (P : Protocol d) (r : ℕ) (α θ : ℝ) (T : ℕ) :
    Measure (Latent d r × Record P) :=
  (prior d r α θ).bind (fun g =>
    (law P (physicalInput hd α θ g) T).map (fun H => (g,H)))

def densityAt {d : ℕ} {hd : 0 < d} {P : Protocol d} (R : Refinement hd P)
    (r : ℕ) (α θ : ℝ) (T : ℕ) (H : Record P) : ℝ :=
  recordDensity r α θ (projectors R T H)

def derivativeIntegral {d : ℕ} {hd : 0 < d} {P : Protocol d} (R : Refinement hd P)
    (r : ℕ) (α θ : ℝ) (T : ℕ) (κ : ℝ) : ℝ :=
  ∫ H in goodRecords R T κ, |deriv (fun u => densityAt R r α u T H) θ|
    ∂referenceLaw hd P T

/-- Equivalent TV formula for the constructed densities against the fixed reference law. -/
def endpointTV {d : ℕ} {hd : 0 < d} {P : Protocol d} (R : Refinement hd P)
    (r : ℕ) (α : ℝ) (T : ℕ) : ℝ :=
  (1/2 : ℝ) * ∫ H, |densityAt R r α 0 T H - densityAt R r α (Real.pi / r) T H|
    ∂referenceLaw hd P T

def rawMatrix {d r : ℕ} (α θ : ℝ) (g : Latent d r) (P : Op d) : Op d :=
  (1 / factor α θ g P) • (P - unitOp d)

def retainedMatrix {d r N : ℕ} (α θ κ : ℝ) (g : Latent d r)
    (H : FrozenHistory d N) (i : Fin N) : Op d := by
  classical
  exact if opNorm (∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), H j) < κ then
    rawMatrix α θ g (H i) else 0

/-- Ordered injective tuples, with multiplication in tuple order, even for complex matrices. -/
def chain {d N : ℕ} (Y : Fin N → Op d) (s : ℕ) : Op d := by
  classical
  exact ∑ f : Fin s ↪ Fin N, ((List.ofFn fun j => Y (f j)).prod)

def cycle {d N : ℕ} (Y : Fin N → Op d) (s : ℕ) : ℂ := (chain Y s).trace

def retainedChain {d : ℕ} {hd : 0 < d} {P : Protocol d} (R : Refinement hd P)
    (r : ℕ) (α θ κ : ℝ) (N s : ℕ) (w : Latent d r × Record P) : Op d :=
  chain (retainedMatrix α θ κ w.1 (projectors R N w.2)) s

def retainedCycle {d : ℕ} {hd : 0 < d} {P : Protocol d} (R : Refinement hd P)
    (r : ℕ) (α θ κ : ℝ) (N s : ℕ) (w : Latent d r × Record P) : ℂ :=
  (retainedChain R r α θ κ N s w).trace

def rawCycle {d r N : ℕ} (α θ : ℝ) (H : FrozenHistory d N)
    (s : ℕ) (g : Latent d r) : ℂ := cycle (fun i => rawMatrix α θ g (H i)) s

def chainHeight (s : ℕ) : ℕ := 1 + Nat.log 2 s

def matrixConstant (κ : ℝ) : ℝ := 2 * (κ + 2)

def tailScale (A : ℝ) (h : ℕ) : ℝ := 1 / (32 * A * ((h : ℝ)+1) * Real.log 2)

/-- Numeric prefactor domination used to choose the order-independent constant in (7.31). -/
def CycleConstant (κ A : ℝ) : Prop :=
  1 ≤ A ∧ ∀ ℓ : ℕ, 2 ≤ ℓ →
    Real.sqrt (2*(ℓ : ℝ)^2*((ℓ : ℝ)-1)^(2*ℓ-2) *
      (2*(matrixConstant κ)^2)^(ℓ-1)) ≤ Real.exp (A*ℓ*Real.log ((ℓ : ℝ)+1))

def LowerParameters (t : ℕ) (α A : ℝ) : Prop :=
  CycleConstant (2*((level t : ℝ)+1)) A ∧ 0 < α ∧ α ≤ 1/100 ∧ α ≤ 1/(8 * (2*((level t : ℝ)+1))) ∧
    α ≤ ((2^(level t - 1) + 1 : ℕ) : ℝ) * Real.exp (-4 / tailScale A (level t)) /
      (12 * matrixConstant (2*((level t : ℝ)+1)))

def oneStepMatrix {d r : ℕ} {hd : 0 < d} {P : Protocol d} (R : Refinement hd P)
    (α θ κ : ℝ) (g : Latent d r) (i : ℕ) (H : Record P) (retained : Bool)
    (y : P.Outcome) : Op d := by
  classical
  exact if retained ∧ ¬ opNorm (projectorSum (projectors R i H)) < κ then 0
    else rawMatrix α θ g (outer (R.vector i H y))

end SingleCopyMoments.Adaptive


