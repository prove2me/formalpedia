-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
-- name    : QAlgorithms_Papers_Independent_Information100_P04
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:25:43.755924+00:00
-- url     : https://prove2.me/theorems/f717f512-c8b0-43e6-8922-fc5b98f00d93
-- title:
--   Definitions for On PPT entanglement distillation
-- statement:
--   The objects the formalized statements of *On PPT entanglement distillation* (arXiv:2610.12454) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `gamma`: Partial transpose on the second party in the fixed product basis (p.5).
--   - `absOp`: Absolute operator; for Hermitian H this is sqrt(H^2) (p.11).
--   - `copies`: Bipartite tensor powers grouped as A^n:B^n; at n=0 this is the scalar identity (p.9).
--   - `Measurement`: Finite POVMs, with normalized total effect and PSD effects (pp.10–11). Zero effects are harmless placeholders and omitted from each score.
--   - `ell`: The ordinary measured score, eq.(38), with zero-probability terms omitted (p.12).
--   - `weightedScore`: The weighted objective in eq.(35), with absolute operators before their sum (p.11).
--   - `ellTilde`: The auxiliary measured score in eq.(35), over strictly positive weights (p.11). On POVMs and states its set of objectives is nonempty and bounded above, as proved on pp.11–13.
--   - `L`: L in eqs.(9),(39), optimized over all finite POVMs (pp.5,12). The one-outcome measurement gives zero and eq.(41) bounds this real supremum.
--   - `LTilde`: Auxiliary L-tilde in eq.(39), with the same nonempty bounded-supremum convention (p.12).
--   - `LLevel`: Normalized L levels, indexed by positive block lengths n+1 (p.5).
--   - `LTildeLevel`: Positive-block L-tilde levels (p.12).
--   - `IsPPTChannel`: PPT channels: both Lambda and its partial-transpose conjugate are channels (pp.5,9). For trace-preserving Lambda the conjugate is automatically trace preserving, so this is exactly the source's complete-positivity criterion.
--   - `bellProjector`: Normalized Bell projection Phi_d, eq.(7) (p.5).
--   - `bellOverlap`: Optimal Bell overlap in the OPERATIONAL definition (7), PDF p.5. The optimization is over actual PPT channels, independently of the equivalent SDP (25). For density matrices and positive integer ranks the set is nonempty and bounded by one.
--   - `outputRank`: Integer output rank at rate R, eq.(8) (p.5). For R>=0 this is positive, also at n=0.
--   - `Achievable`: Vanishing-error achievable rates via the operational Bell overlap in (7) (pp.5,9). This is the operational form of (24); at R=0 the rank is one and the overlap is one.
--   - `distillable`: PPT distillable entanglement, the supremum of vanishing-error achievable rates (pp.5,9). For finite-dimensional density matrices this set contains zero and is bounded by log min(dA,dB).
--   - `IsPPT`: A PPT state in the source's convention, including normalization (p.5).
--   - `entropyTerm`: An extended-real relative-entropy summand: 0 log 0 is zero; positive mass over zero is +infty (p.11).
--   - `binaryD`: Binary relative entropy in bits. Callers keep b strictly inside (0,1), allowing a=0,1 (p.9).
--   - `dualScore`: Dual objective of eq.(36); positive-probability zero denominators remain +infty (p.11).
--   - `negativeProjector`: Negative spectral projector in eq.(60), using functional calculus on the Hermitian partial transpose (p.15).
--   - `negativeRank`: Negative spectral data: count r and Euclidean length s of the strictly negative eigenvalues (pp.12–13).
--   - `negativeLength`: The scalar s in eq.(45) (p.12).
--   - `spectralC`: c=max(1,lambda_max(P^Gamma)), p.15. Supremum is finite and nonempty on nonzero local spaces.
--   - `spectralZ`: z=-lambda_min(P^Gamma), p.15, positive when the negativity is positive.
--   - `spectralEffect`: The effect constructed by eq.(60), rather than an independent hypothesis (p.15).
--   - `principalMarginal`: AB marginal of a state on AA':BB' (p.12).
--   - `ancillaryMarginal`: A'B' marginal with the same bipartition convention (p.12).
--   - `wernerP0`: Symmetric Werner projector P0=(I+F)/2, eq.(21) (p.7).
--   - `wernerP1`: Antisymmetric Werner projector P1=(I-F)/2, eq.(21) (p.7).
--   - `werner`: Werner state with antisymmetric weight p; statements impose d>=2 and 0<=p<=1 (p.7).
--   - `wernerU`: Scalars u and q in Section VI.A (p.27).
--   - `wernerQ`: q=d/(d+1) (p.27).
--   - `wernerA`: The threshold effect A=P1+u P0 (p.27).
--   - `wernerJ0`: J0 of (125), evaluated only at 0<mu<=1 in the theorem (p.27).
--   - `wernerJ1`: J1 of (125), evaluated away from mu=0 where it is infinite (p.27).
--   - `wernerLambda`: Optimal lambda from Proposition 19; the threshold endpoint is specified directly (p.28).
--   - `wernerMeasurement`: Three-ray POVM (128). Zero rays at endpoints are omitted in all scores (p.28).
--   - `qubitK`: The explicit qubit form (84), PDF p.20; positivity is Hilbert--Schmidt positivity.
--   - `bellTwo`: Bell projection on two copies of a qubit with trivial second party, PDF p.20.
--   - `hsQuadratic`: Hilbert--Schmidt quadratic form; real for self-adjoint superoperators, PDF p.6.
--   - `productOperators`: Tensor product in the grouped A:B convention used by copies (pp.9,27).
--   - `thresholdEffect`: The threshold effect Q_(n,k) of eq.(122), including k=0 (p.27).
--   - `binomialTail`: Binomial upper-tail probability, with the full endpoint convention k=0 (p.27).
--   - `typeProjector`: Physical and partially transposed type projectors (pp.27,29). The number of distinguished factors is exactly i.
--   - `collectiveSlope`: The rational slope s in eq.(131), PDF p.29.
--   - `collectiveCoefficient`: The exact quadratic coefficient in eq.(132), not its rounded decimal (p.29).
--   - `IsRationalMatrix`: Rational complex matrix entries, sufficient to record the exact certificate's rationality (p.29).
--   - `collectiveAcceptance`: The fixed 24-copy acceptance polynomial (p.29).
--   - `collectiveCurve`: The achievable fixed-block curve, set to zero on its nonaccepting side (p.29).
--   - `physicalType`: Type probabilities for Werner tensor powers (p.29).
--   - `typeTransform`: Signed type transform (133), p.29. Summation uses l<=i; choose(k,l)=0 for l>k. This avoids replacing out-of-range binomial coefficients by truncated natural subtraction.
--   - `typePolytope`: The compact signed type polytope in (134), p.29.
--   - `IsTypeVertex`: Nonzero vertices, in the equivalent midpoint-extremality characterization for convex sets (p.29).
--   - `LPFeasible`: Finite feasible columns of the all-vertex LP; no preselected subset is built in (p.29).
--   - `LPObjective`: Linear objective of (134), already divided by the positive block length m (p.29).
--   - `runningLevel`: Running maxima of positive L levels (p.29), including level 1 at index zero.
--   - `stripBeta`: Hirschman's probability density (17), PDF p.7. Theorems impose 0<theta<1.
--   - `innerWeight`: Inner strip boundary weight (D1), PDF pp.34–35.
--   - `outerWeight`: Outer strip boundary weight (D1), PDF pp.34–35.
--   - `periodized`: Angular periodization relative to dpsi/(2pi), eq.(D4), PDF p.35.
--   - `periodizedPartial`: Finite symmetric partial sums used to assert uniform convergence on one period (p.35).
--   - `innerFourier`: Inner angular Fourier series in (D6), p.35.
--   - `outerFourier`: Outer angular Fourier series in (D6), p.35.
--   - `innerDensity`: Positive-arclength inner density (D5),(18); positive radius only (p.35).
--   - `outerDensity`: Positive-arclength outer density (D5),(18) (p.35).
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, https://arxiv.org/abs/2610.12454v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity

/-! Paper-local definitions for arXiv:2610.12454v1. All page references are PDF pages.
Finite measurements may contain zero effects; the scores omit their zero-probability terms.
Deleting zero effects gives precisely the source's convention. All logarithms below are in bits.
Negativity is reused from QAlgorithms.Entanglement.negativity. That definition transposes
A; its matrix is the full transpose of gamma rho, so the trace norm equals the paper's
second-party convention (pp.4,5,12). All operator partial transposes below still act on B.
No definition from a frozen module is modified. -/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Partial transpose on the second party in the fixed product basis (p.5). -/
def gamma {A B : Type*} (X : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ := fun i j => X (i.1, j.2) (j.1, i.2)

/-- Absolute operator; for Hermitian H this is sqrt(H^2) (p.11). -/
def absOp {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) : Matrix I I ℂ :=
  cfc Real.sqrt (Xᴴ * X)

/-- Bipartite tensor powers grouped as A^n:B^n; at n=0 this is the scalar identity (p.9). -/
def copies {A B : Type*} (X : Matrix (A × B) (A × B) ℂ) (n : ℕ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ :=
  fun i j => ∏ k, X (i.1 k, i.2 k) (j.1 k, j.2 k)

/-- Finite POVMs, with normalized total effect and PSD effects (pp.10–11).
Zero effects are harmless placeholders and omitted from each score. -/
structure Measurement (I : Type*) [Fintype I] [DecidableEq I] where
  outcomes : ℕ
  positive : 0 < outcomes
  effect : Fin outcomes → Matrix I I ℂ
  valid : IsPOVM effect

/-- The ordinary measured score, eq.(38), with zero-probability terms omitted (p.12). -/
def ell {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {k : ℕ} (rho : Matrix (A × B) (A × B) ℂ)
    (E : Fin k → Matrix (A × B) (A × B) ℂ) : ℝ :=
  ∑ j, let p := effectProb (E j) rho
    if 0 < p then p * Real.logb 2 (p / specNorm (gamma (E j))) else 0

/-- The weighted objective in eq.(35), with absolute operators before their sum (p.11). -/
def weightedScore {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {k : ℕ} (rho : Matrix (A × B) (A × B) ℂ)
    (E : Fin k → Matrix (A × B) (A × B) ℂ) (y : Fin k → ℝ) : ℝ :=
  (∑ j, effectProb (E j) rho * Real.logb 2 (y j)) -
    Real.logb 2 (specNorm (∑ j, (y j : ℂ) • absOp (gamma (E j))))

/-- The auxiliary measured score in eq.(35), over strictly positive weights (p.11).
On POVMs and states its set of objectives is nonempty and bounded above, as proved on pp.11–13. -/
def ellTilde {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {k : ℕ} (rho : Matrix (A × B) (A × B) ℂ)
    (E : Fin k → Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {v | ∃ y : Fin k → ℝ, (∀ j, 0 < y j) ∧ v = weightedScore rho E y}

/-- L in eqs.(9),(39), optimized over all finite POVMs (pp.5,12).
The one-outcome measurement gives zero and eq.(41) bounds this real supremum. -/
def L {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {v | ∃ M : Measurement (A × B), v = ell rho M.effect}

/-- Auxiliary L-tilde in eq.(39), with the same nonempty bounded-supremum convention (p.12). -/
def LTilde {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {v | ∃ M : Measurement (A × B), v = ellTilde rho M.effect}

/-- Normalized L levels, indexed by positive block lengths n+1 (p.5). -/
def LLevel {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) : ℝ := L (copies rho (n+1)) / (n+1 : ℝ)

/-- Positive-block L-tilde levels (p.12). -/
def LTildeLevel {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) : ℝ := LTilde (copies rho (n+1)) / (n+1 : ℝ)

/-- PPT channels: both Lambda and its partial-transpose conjugate are channels (pp.5,9).
For trace-preserving Lambda the conjugate is automatically trace preserving, so this is
exactly the source's complete-positivity criterion. -/
def IsPPTChannel {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (Phi : Superop (A × B) (C × D)) : Prop :=
  IsChannel Phi ∧ IsChannel (gamma ∘ Phi ∘ gamma)

/-- Normalized Bell projection Phi_d, eq.(7) (p.5). -/
def bellProjector (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun i j => if i.1 = i.2 ∧ j.1 = j.2 then (d:ℂ)⁻¹ else 0

/-- Optimal Bell overlap in the OPERATIONAL definition (7), PDF p.5.
The optimization is over actual PPT channels, independently of the equivalent SDP (25).
For density matrices and positive integer ranks the set is nonempty and bounded by one. -/
def bellOverlap {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (d : ℕ) : ℝ :=
  sSup {v | ∃ Phi : Superop (A × B) (Fin d × Fin d),
    IsPPTChannel Phi ∧ v = effectProb (bellProjector d) (Phi rho)}

/-- Integer output rank at rate R, eq.(8) (p.5). For R>=0 this is positive, also at n=0. -/
def outputRank (n : ℕ) (R : ℝ) : ℕ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R))

/-- Vanishing-error achievable rates via the operational Bell overlap in (7) (pp.5,9).
This is the operational form of (24); at R=0 the rank is one and the overlap is one. -/
def Achievable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (R : ℝ) : Prop :=
  0 ≤ R ∧ Tendsto (fun n => bellOverlap (copies rho (n+1)) (outputRank (n+1) R))
    atTop (nhds 1)

/-- PPT distillable entanglement, the supremum of vanishing-error achievable rates (pp.5,9).
For finite-dimensional density matrices this set contains zero and is bounded by log min(dA,dB). -/
def distillable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ := sSup {R | Achievable rho R}

/-- A PPT state in the source's convention, including normalization (p.5). -/
def IsPPT {A B : Type*} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : Prop :=
  IsDensityMatrix rho ∧ (gamma rho).PosSemidef

/-- An extended-real relative-entropy summand: 0 log 0 is zero; positive mass over zero is +infty (p.11). -/
def entropyTerm (p q : ℝ) : EReal :=
  if p = 0 then 0 else if q = 0 then ⊤ else ((p * Real.logb 2 (p/q) : ℝ) : EReal)

/-- Binary relative entropy in bits. Callers keep b strictly inside (0,1), allowing a=0,1 (p.9). -/
def binaryD (a b : ℝ) : ℝ :=
  a * Real.logb 2 (a/b) + (1-a) * Real.logb 2 ((1-a)/(1-b))

/-- Dual objective of eq.(36); positive-probability zero denominators remain +infty (p.11). -/
def dualScore {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {k : ℕ} (rho sigma : Matrix (A × B) (A × B) ℂ)
    (E : Fin k → Matrix (A × B) (A × B) ℂ) : EReal :=
  ∑ j, entropyTerm (effectProb (E j) rho) (effectProb (absOp (gamma (E j))) sigma)

/-- Negative spectral projector in eq.(60), using functional calculus on the Hermitian partial transpose (p.15). -/
def negativeProjector {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ :=
  cfc (fun x : ℝ => if x < 0 then 1 else 0) (gamma rho)

/-- Negative spectral data: count r and Euclidean length s of the strictly negative eigenvalues (pp.12–13). -/
def negativeRank {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℕ :=
  (Finset.univ.filter fun k => ascEigenvalues (gamma rho) k < 0).card

/-- The scalar s in eq.(45) (p.12). -/
def negativeLength {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  Real.sqrt (∑ k, (min (ascEigenvalues (gamma rho) k) 0)^2)

/-- c=max(1,lambda_max(P^Gamma)), p.15. Supremum is finite and nonempty on nonzero local spaces. -/
def spectralC {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  max 1 (sSup (Set.range (ascEigenvalues (gamma (negativeProjector rho)))))

/-- z=-lambda_min(P^Gamma), p.15, positive when the negativity is positive. -/
def spectralZ {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  -sInf (Set.range (ascEigenvalues (gamma (negativeProjector rho))))

/-- The effect constructed by eq.(60), rather than an independent hypothesis (p.15). -/
def spectralEffect {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ :=
  (((spectralC rho + spectralZ rho)⁻¹ : ℝ) : ℂ) •
    ((spectralC rho : ℂ) • 1 - gamma (negativeProjector rho))

/-- AB marginal of a state on AA':BB' (p.12). -/
def principalMarginal {A B C D : Type*} [Fintype C] [Fintype D]
    (rho : Matrix ((A × C) × (B × D)) ((A × C) × (B × D)) ℂ) :
    Matrix (A × B) (A × B) ℂ := fun i j => ∑ c, ∑ d, rho ((i.1,c),(i.2,d)) ((j.1,c),(j.2,d))

/-- A'B' marginal with the same bipartition convention (p.12). -/
def ancillaryMarginal {A B C D : Type*} [Fintype A] [Fintype B]
    (rho : Matrix ((A × C) × (B × D)) ((A × C) × (B × D)) ℂ) :
    Matrix (C × D) (C × D) ℂ := fun i j => ∑ a, ∑ b, rho ((a,i.1),(b,i.2)) ((a,j.1),(b,j.2))

/-- Symmetric Werner projector P0=(I+F)/2, eq.(21) (p.7). -/
def wernerP0 (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (1/2 : ℂ) • (1 + fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0)

/-- Antisymmetric Werner projector P1=(I-F)/2, eq.(21) (p.7). -/
def wernerP1 (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := 1 - wernerP0 d

/-- Werner state with antisymmetric weight p; statements impose d>=2 and 0<=p<=1 (p.7). -/
def werner (d : ℕ) (p : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ((2*(1-p)/((d:ℝ)*(d+1)) : ℝ) : ℂ) • wernerP0 d +
    ((2*p/((d:ℝ)*(d-1)) : ℝ) : ℂ) • wernerP1 d

/-- Scalars u and q in Section VI.A (p.27). -/
def wernerU (d : ℕ) : ℝ := ((d:ℝ)-1)/(d+1)

/-- q=d/(d+1) (p.27). -/
def wernerQ (d : ℕ) : ℝ := (d:ℝ)/(d+1)

/-- The threshold effect A=P1+u P0 (p.27). -/
def wernerA (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  wernerP1 d + (wernerU d : ℂ) • wernerP0 d

/-- J0 of (125), evaluated only at 0<mu<=1 in the theorem (p.27). -/
def wernerJ0 (d : ℕ) (p mu : ℝ) : ℝ :=
  (1-p)*Real.logb 2 ((1-p)/(((d:ℝ)+1-d*mu)/2)) +
    p*Real.logb 2 (p/(((d:ℝ)-1-(d-2)*mu)/2))

/-- J1 of (125), evaluated away from mu=0 where it is infinite (p.27). -/
def wernerJ1 (d : ℕ) (p mu : ℝ) : ℝ :=
  let t := p + wernerU d*(1-p)
  (1-wernerU d)*(1-p)*Real.logb 2 ((1-p)/(((d:ℝ)+1-d*mu)/2)) +
    t*Real.logb 2 (t/(mu*wernerQ d))

/-- Optimal lambda from Proposition 19; the threshold endpoint is specified directly (p.28). -/
def wernerLambda (d : ℕ) (p mu : ℝ) : ℝ :=
  if p = 1/2 then 1 else
    deriv (wernerJ0 d p) mu / (deriv (wernerJ0 d p) mu - deriv (wernerJ1 d p) mu)

/-- Three-ray POVM (128). Zero rays at endpoints are omitted in all scores (p.28). -/
def wernerMeasurement (d : ℕ) (lam : ℝ) : Fin 3 → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ![(1 - (wernerU d * lam : ℝ) : ℂ) • wernerP0 d,
    ((1-lam : ℝ) : ℂ) • wernerP1 d, (lam : ℂ) • wernerA d]

/-- Local definitions have concrete sanity tests; double partial transpose restores every entry (p.5). -/
example {A B : Type*} (X : Matrix (A × B) (A × B) ℂ) : gamma (gamma X) = X := rfl

example {A B : Type*} (X : Matrix (A × B) (A × B) ℂ)
    (i j : (Fin 0 → A) × (Fin 0 → B)) : copies X 0 i j = 1 := by
  simp [copies]

example (q : ℝ) : entropyTerm 0 q = 0 := by simp [entropyTerm]

example (p : ℝ) (h : p ≠ 0) : entropyTerm p 0 = ⊤ := by simp [entropyTerm, h]

example : wernerU 3 = 1/2 ∧ wernerQ 3 = 3/4 := by norm_num [wernerU, wernerQ]

/-- The explicit qubit form (84), PDF p.20; positivity is Hilbert--Schmidt positivity. -/
def qubitK (X : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  (3/2 : ℂ) • X - (X.trace/2) • 1

/-- Bell projection on two copies of a qubit with trivial second party, PDF p.20. -/
def bellTwo : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℂ :=
  fun i j => if i 0 = i 1 ∧ j 0 = j 1 then 1/2 else 0

/-- Hilbert--Schmidt quadratic form; real for self-adjoint superoperators, PDF p.6. -/
def hsQuadratic {I : Type*} [Fintype I]
    (K : Superop I I) (X : Matrix I I ℂ) : ℝ := (Xᴴ * K X).trace.re

/-- Tensor product in the grouped A:B convention used by copies (pp.9,27). -/
def productOperators {A B : Type*} {n : ℕ}
    (E : Fin n → Matrix (A × B) (A × B) ℂ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ :=
  fun i j => ∏ k, E k (i.1 k,i.2 k) (j.1 k,j.2 k)

/-- The threshold effect Q_(n,k) of eq.(122), including k=0 (p.27). -/
def thresholdEffect (d n k : ℕ) :
    Matrix ((Fin n → Fin d) × (Fin n → Fin d))
      ((Fin n → Fin d) × (Fin n → Fin d)) ℂ :=
  ∑ x : Fin n → Bool, if k ≤ (Finset.univ.filter fun j => x j = true).card then
    productOperators (fun j => if x j then wernerA d else 1 - wernerA d) else 0

/-- Binomial upper-tail probability, with the full endpoint convention k=0 (p.27). -/
def binomialTail (n k : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), if k ≤ j then (n.choose j : ℝ)*u^j*(1-u)^(n-j) else 0

/-- Physical and partially transposed type projectors (pp.27,29).
The number of distinguished factors is exactly i. -/
def typeProjector {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (P0 P1 : Matrix (A × B) (A × B) ℂ) (n i : ℕ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ :=
  ∑ x : Fin n → Bool, if (Finset.univ.filter fun j => x j = true).card = i then
    productOperators (fun j => if x j then P1 else P0) else 0

/-- The rational slope s in eq.(131), PDF p.29. -/
def collectiveSlope : ℝ := 4118621179428546867727313 / 1283031261738279119093760

/-- The exact quadratic coefficient in eq.(132), not its rounded decimal (p.29). -/
def collectiveCoefficient : ℝ := collectiveSlope^2 / (48*(2/5)*(3/5)*Real.log 2)

/-- Rational complex matrix entries, sufficient to record the exact certificate's rationality (p.29). -/
def IsRationalMatrix {I : Type*} (X : Matrix I I ℂ) : Prop :=
  ∀ i j, ∃ a b : ℚ, X i j = (a:ℂ) + Complex.I*(b:ℂ)

/-- The fixed 24-copy acceptance polynomial (p.29). -/
def collectiveAcceptance
    (E : Matrix ((Fin 24 → Fin 3) × (Fin 24 → Fin 3))
      ((Fin 24 → Fin 3) × (Fin 24 → Fin 3)) ℂ) (p : ℝ) : ℝ :=
  effectProb E (copies (werner 3 p) 24)

/-- The achievable fixed-block curve, set to zero on its nonaccepting side (p.29). -/
def collectiveCurve
    (E : Matrix ((Fin 24 → Fin 3) × (Fin 24 → Fin 3))
      ((Fin 24 → Fin 3) × (Fin 24 → Fin 3)) ℂ) (p : ℝ) : ℝ :=
  if 2/5 < collectiveAcceptance E p then binaryD (collectiveAcceptance E p) (2/5) / 24 else 0

/-- Type probabilities for Werner tensor powers (p.29). -/
def physicalType (p : ℝ) (m : ℕ) (i : Fin (m+1)) : ℝ :=
  (m.choose i.val : ℝ)*p^i.val*(1-p)^(m-i.val)

/-- Signed type transform (133), p.29. Summation uses l<=i; choose(k,l)=0 for l>k.
This avoids replacing out-of-range binomial coefficients by truncated natural subtraction. -/
def typeTransform (d m : ℕ) (k i : Fin (m+1)) : ℝ :=
  (2:ℝ)^(-(m:ℤ)) * ∑ l ∈ Finset.range (i.val+1),
    (-1:ℝ)^l * ((d:ℝ)-1)^l * ((d:ℝ)+1)^(k.val-l) *
      (k.val.choose l : ℝ) * ((m-k.val).choose (i.val-l) : ℝ)

/-- The compact signed type polytope in (134), p.29. -/
def typePolytope (d m : ℕ) : Set (Fin (m+1) → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ ∀ k, |∑ i, typeTransform d m k i * v i| ≤ 1}

/-- Nonzero vertices, in the equivalent midpoint-extremality characterization for convex sets (p.29). -/
def IsTypeVertex (d m : ℕ) (v : Fin (m+1) → ℝ) : Prop :=
  v ≠ 0 ∧ v ∈ typePolytope d m ∧
    ∀ x ∈ typePolytope d m, ∀ y ∈ typePolytope d m,
      (1/2:ℝ) • (x+y) = v → x = v ∧ y = v

/-- Finite feasible columns of the all-vertex LP; no preselected subset is built in (p.29). -/
def LPFeasible (d m k : ℕ) (lam : Fin k → ℝ) (v : Fin k → Fin (m+1) → ℝ) : Prop :=
  (∀ j, 0 ≤ lam j ∧ IsTypeVertex d m (v j)) ∧ ∀ i, ∑ j, lam j*v j i = 1

/-- Linear objective of (134), already divided by the positive block length m (p.29). -/
def LPObjective (p : ℝ) (m k : ℕ) (lam : Fin k → ℝ) (v : Fin k → Fin (m+1) → ℝ) : ℝ :=
  (∑ j, let a := ∑ i, physicalType p m i * v j i
    lam j * a * Real.logb 2 a) / m

/-- Running maxima of positive L levels (p.29), including level 1 at index zero. -/
def runningLevel {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) : ℝ :=
  sSup {x | ∃ k ≤ n, x = LLevel rho k}

example : typeTransform 3 1 0 0 = 1/2 ∧ typeTransform 3 1 0 1 = 1/2 ∧
    typeTransform 3 1 1 0 = 2 ∧ typeTransform 3 1 1 1 = -1 := by
  norm_num [typeTransform, Finset.sum_range_succ]

example : bellTwo (fun _ => false) (fun _ => true) = 1/2 := by simp [bellTwo]

example {A B : Type*} (X : Matrix (A × B) (A × B) ℂ)
    (i j : (Fin 0 → A) × (Fin 0 → B)) :
    productOperators (fun _ : Fin 0 => X) i j = 1 := by simp [productOperators]

open MeasureTheory

/-- Hirschman's probability density (17), PDF p.7. Theorems impose 0<theta<1. -/
def stripBeta (theta s : ℝ) : ℝ :=
  Real.sin (Real.pi*theta) /
    (2*theta*(Real.cosh (Real.pi*s)+Real.cos (Real.pi*theta)))

/-- Inner strip boundary weight (D1), PDF pp.34–35. -/
def innerWeight (theta s : ℝ) : ℝ := (1-theta)*stripBeta (1-theta) s

/-- Outer strip boundary weight (D1), PDF pp.34–35. -/
def outerWeight (theta s : ℝ) : ℝ := theta*stripBeta theta s

/-- Angular periodization relative to dpsi/(2pi), eq.(D4), PDF p.35. -/
def periodized (h : ℝ → ℝ) (ell phi psi : ℝ) : ℝ :=
  (2*Real.pi/ell) * ∑' m : ℤ, h ((psi-phi+2*Real.pi*m)/ell)

/-- Finite symmetric partial sums used to assert uniform convergence on one period (p.35). -/
def periodizedPartial (h : ℝ → ℝ) (ell phi : ℝ) (n : ℕ) (psi : ℝ) : ℝ :=
  (2*Real.pi/ell) * ∑ m ∈ Finset.Icc (-(n:ℤ)) (n:ℤ),
    h ((psi-phi+2*Real.pi*m)/ell)

/-- Inner angular Fourier series in (D6), p.35. -/
def innerFourier (a b r phi psi : ℝ) : ℝ :=
  1 - Real.log (r/a)/Real.log (b/a) + 2 * ∑' j : ℕ,
    (a/r)^(j+1) * (1-(r/b)^(2*(j+1))) / (1-(a/b)^(2*(j+1))) *
      Real.cos ((j+1:ℕ)*(psi-phi))

/-- Outer angular Fourier series in (D6), p.35. -/
def outerFourier (a b r phi psi : ℝ) : ℝ :=
  Real.log (r/a)/Real.log (b/a) + 2 * ∑' j : ℕ,
    (r/b)^(j+1) * (1-(a/r)^(2*(j+1))) / (1-(a/b)^(2*(j+1))) *
      Real.cos ((j+1:ℕ)*(psi-phi))

/-- Positive-arclength inner density (D5),(18); positive radius only (p.35). -/
def innerDensity (a b r phi psi : ℝ) : ℝ :=
  periodized (innerWeight (Real.log (r/a)/Real.log (b/a))) (Real.log (b/a)) phi psi /
    (2*Real.pi*a)

/-- Positive-arclength outer density (D5),(18) (p.35). -/
def outerDensity (a b r phi psi : ℝ) : ℝ :=
  periodized (outerWeight (Real.log (r/a)/Real.log (b/a))) (Real.log (b/a)) phi psi /
    (2*Real.pi*b)

example (theta : ℝ) : innerWeight theta 0 = (1-theta)*stripBeta (1-theta) 0 := rfl

end QAlgorithms.Papers.Independent.Information100.P04


