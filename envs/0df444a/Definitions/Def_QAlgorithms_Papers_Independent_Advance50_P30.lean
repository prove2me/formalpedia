-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P30
-- name    : QAlgorithms_Papers_Independent_Advance50_P30
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T10:51:41.466125+00:00
-- url     : https://prove2.me/theorems/324ac893-e73e-4d9e-a284-db06920286e0
-- title:
--   Definitions for Unconditional privacy over channels which cannot convey quantum information
-- statement:
--   The objects the formalized statements of *Unconditional privacy over channels which cannot convey quantum information* (arXiv:quant-ph/0702077) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `DensityState`: PDF p.11: the space of normalized, positive single-site mixed states.
--   - `joinCopies`: PDF p.13: regroup the first k coordinates and the discarded suffix.
--   - `reduceCopies`: PDF pp.11,13: partial trace, retaining the first k sites.
--   - `InvariantCopyState`: PDF p.11: operator invariance; no pure symmetric-support restriction.
--   - `defectTensor`: PDF p.12, Eq.(10): a spanning tensor with arbitrary amplitudes on S and copies of theta elsewhere. Allowing |S| ≤ r gives the same span as exactly r when r ≤ n: extra defect slots can be filled with theta.
--   - `AlmostPure`: PDF p.12, Definition 1: unit vectors in Sym intersect span(V), with the source's domain r ≤ n. The span is a complex linear span, not V itself.
--   - `AlmostMixed`: PDF pp.12--13: convex mixtures of normalized almost-power projectors.
--   - `discardReferences`: PDF p.15: trace out every reference factor of paired sites.
--   - `AlmostAlong`: PDF pp.15--16: mixed almost-power along sigma is the reduction of a mixture along a unit purification of sigma. Mixtures are allowed because conditioning the purification measure on its single-site reduction can mix purifications. Equal purifications differ by a reference unitary; this leaves the reduced convex class unchanged. No concentration inequality is a field.
--   - `empiricalFrequency`: PDF pp.12,19: normalized empirical distribution on the stated alphabet. The n=0 totalized value is zero; concentration statements require n>0.
--   - `l1`: PDF pp.12,17: full classical L1 norm, with no factor one half.
--   - `tensorEffect`: PDF p.12: exact product POVM effect on a specified outcome string.
--   - `iidEvent`: PDF pp.12,14: the actual joint Born probability of an event under E^tensor n.
--   - `chernoffError`: PDF pp.12,14,19, Eq.(22): generalized Chernoff error function in bits.
--   - `deFinettiError`: PDF pp.11,22: exponential finite de Finetti error on mixed states; the squared single-site dimension is inside the exponent.
--   - `Spectral`: PDF pp.17--20: the genuine finite spectral measurement of an observable. Nonzero orthogonal projections and distinct real eigenvalues give its spectral alphabet; its cardinality is at most dim H.
--   - `Spectral.operator`: PDF p.17: reconstruct the Hermitian operator from its spectral measurement.
--   - `HSDecomposition`: PDF pp.17--18, Eq.(18): arbitrary real signed coefficients in a Hermitian Hilbert--Schmidt orthonormal decomposition. There is no positivity constraint on the coefficients and no operator-norm equality assumption.
--   - `HSDecomposition.operator`: PDF pp.17--18: the observable is computed from its decomposition.
--   - `Outcomes`: PDF pp.19--21: all outcomes of the disjoint indirect and direct blocks.
--   - `tensorBlockEffect`: PDF pp.19--22: tensor effect of precisely L_1^mp tensor ... tensor L_t^mp tensor M^q. The flattening puts all indirect blocks first.
--   - `estimationEvent`: PDF pp.21--22: P' and P'' are evaluated from the input state, never chosen as couplings. Events involving one block automatically use its marginal.
--   - `indirectMean`: PDF p.20, Eq.(25): sum of coefficient-weighted, normalized block means.
--   - `directMean`: PDF pp.20,22: the direct mean, normalized by the actual direct-block size.
--   - `samplingError`: PDF p.22, Eq.(36): the classical sampling allowance in full L1 convention.
-- source:
--   Unconditional privacy over channels which cannot convey quantum information, arXiv:quant-ph/0702077v1, https://arxiv.org/abs/quant-ph/0702077v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

/-!
Horodecki et al., arXiv:quant-ph/0702077v1. Page numbers are PDF pages.
Accepted register/vector/permutation definitions are imported. Paper-local
constructions implement the appendix's finite experiments.
All trace norms are full Schatten 1-norms. Entropy and logb 2 are in bits;
Real.exp and Real.log in de Finetti and sampling terms are natural.
Operational security claims and ambiguous printed specializations are deferred
in the unit's HARD.md; no passive-capacity surrogate is asserted here.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P30

open QAlgorithms MeasureTheory
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)
open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)
open QAlgorithms.Papers.Independent.Information100.P69 (permute)
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.11,21: the finite-coordinate extended norm is continuous for the
matrix product topology, as on the underlying finite function space. -/
local instance matrixContinuousENorm (I : Type) [Fintype I] : ContinuousENorm (Op I) :=
  inferInstanceAs (ContinuousENorm (I → I → ℂ))

/-- PDF pp.11,15: ordinary Borel measurable finite matrix coordinates. -/
local instance matrixMeasurable (I : Type) : MeasurableSpace (Op I) := borel _

/-- The measurable structure used by the integrals is the matrix Borel structure. -/
local instance matrixBorel (I : Type) : BorelSpace (Op I) := ⟨rfl⟩

/-- PDF p.14, Theorem 2: the unit-vector parameter space has its Borel structure. -/
local instance vectorMeasurable (I : Type) : MeasurableSpace (Vec I) := borel _

/-- PDF p.14: the Borel structure on pure-state directions, before taking the unit subtype. -/
local instance vectorBorel (I : Type) : BorelSpace (Vec I) := ⟨rfl⟩

/-- PDF p.11: the space of normalized, positive single-site mixed states. -/
abbrev DensityState (I : Type) [Fintype I] := {rho : Op I // IsDensityMatrix rho}

/-- PDF p.13: regroup the first k coordinates and the discarded suffix. -/
def joinCopies {I : Type} {n k : ℕ} (_h : k ≤ n)
    (x : Copies I k) (z : Copies I (n - k)) : Copies I n :=
  fun i => if hi : i.val < k then x ⟨i.val, hi⟩ else z ⟨i.val - k, by omega⟩

/-- PDF pp.11,13: partial trace, retaining the first k sites. -/
def reduceCopies {I : Type} [Fintype I] {n : ℕ} (rho : Op (Copies I n))
    (k : ℕ) (h : k ≤ n) : Op (Copies I k) :=
  fun x y => ∑ z : Copies I (n - k), rho (joinCopies h x z) (joinCopies h y z)

/-- PDF p.11: operator invariance; no pure symmetric-support restriction. -/
def InvariantCopyState {I : Type} {n : ℕ} (rho : Op (Copies I n)) : Prop :=
  ∀ pi : Equiv.Perm (Fin n), permute pi rho = rho

/-- PDF p.12, Eq.(10): a spanning tensor with arbitrary amplitudes on S and
copies of theta elsewhere. Allowing |S| ≤ r gives the same span as exactly r
when r ≤ n: extra defect slots can be filled with theta. -/
def defectTensor {I : Type} {n : ℕ} (theta : Vec I) (S : Finset (Fin n))
    (chi : (S → I) → ℂ) : Vec (Copies I n) :=
  WithLp.toLp 2 fun x => (∏ i ∈ Finset.univ \ S, theta (x i)) * chi (fun i => x i)

/-- PDF p.12, Definition 1: unit vectors in Sym intersect span(V), with the
source's domain r ≤ n. The span is a complex linear span, not V itself. -/
def AlmostPure {I : Type} [Fintype I] (theta : Vec I) (n r : ℕ)
    (psi : Vec (Copies I n)) : Prop :=
  r ≤ n ∧ IsState theta ∧ IsState psi ∧
    (∀ (pi : Equiv.Perm (Fin n)) (x : Copies I n), psi (x ∘ pi) = psi x) ∧
    psi ∈ Submodule.span ℂ {v | ∃ (S : Finset (Fin n)) (chi : (S → I) → ℂ),
      S.card ≤ r ∧ v = defectTensor theta S chi}

/-- PDF pp.12--13: convex mixtures of normalized almost-power projectors. -/
def AlmostMixed {I : Type} [Fintype I] (theta : Vec I) (n r : ℕ)
    (rho : Op (Copies I n)) : Prop :=
  IsDensityMatrix rho ∧ rho ∈ convexHull ℝ
    {A | ∃ psi : Vec (Copies I n), AlmostPure theta n r psi ∧ A = pureDensity psi}

/-- PDF p.15: trace out every reference factor of paired sites. -/
def discardReferences {I : Type} [Fintype I] {n : ℕ}
    (rho : Op (Copies (I × I) n)) : Op (Copies I n) :=
  fun x y => ∑ z : Copies I n,
    rho (fun i => (x i, z i)) (fun i => (y i, z i))

/-- PDF pp.15--16: mixed almost-power along sigma is the reduction of a
mixture along a unit purification of sigma. Mixtures are allowed because
conditioning the purification measure on its single-site reduction can mix
purifications. Equal purifications differ by a reference unitary; this leaves
the reduced convex class unchanged. No concentration inequality is a field. -/
def AlmostAlong {I : Type} [Fintype I] (sigma : DensityState I) (n r : ℕ)
    (rho : Op (Copies I n)) : Prop :=
  IsDensityMatrix rho ∧ ∃ theta : Vec (I × I), IsState theta ∧
    traceRight (pureDensity theta) = sigma.val ∧
    ∃ omega : Op (Copies (I × I) n), AlmostMixed theta n r omega ∧
      discardReferences omega = rho

/-- PDF pp.12,19: normalized empirical distribution on the stated alphabet.
The n=0 totalized value is zero; concentration statements require n>0. -/
def empiricalFrequency {W : Type} [Fintype W] {n : ℕ} (out : Fin n → W) (w : W) : ℝ :=
  ((Finset.univ.filter fun i => out i = w).card : ℝ) / (n : ℝ)

/-- PDF pp.12,17: full classical L1 norm, with no factor one half. -/
def l1 {W : Type} [Fintype W] (p q : W → ℝ) : ℝ :=
  ∑ w, |p w - q w|

/-- PDF p.12: exact product POVM effect on a specified outcome string. -/
def tensorEffect {I W : Type} {n : ℕ} (E : W → Op I)
    (out : Fin n → W) : Op (Copies I n) :=
  fun x y => ∏ i, E (out i) (x i) (y i)

/-- PDF pp.12,14: the actual joint Born probability of an event under E^tensor n. -/
def iidEvent {I W : Type} [Fintype I] [Fintype W] {n : ℕ}
    (rho : Op (Copies I n)) (E : W → Op I) (event : (Fin n → W) → Prop) : ℝ :=
  ∑ out, if event out then effectProb (tensorEffect E out) rho else 0

/-- PDF pp.12,14,19, Eq.(22): generalized Chernoff error function in bits. -/
def chernoffError (delta : ℝ) (n r w : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(n : ℝ) * (delta ^ 2 / 4 - binEntropy2 ((r : ℝ) / n)) +
    (w : ℝ) * Real.logb 2 ((n : ℝ) / 2 + 1))

/-- PDF pp.11,22: exponential finite de Finetti error on mixed states;
the squared single-site dimension is inside the exponent. -/
def deFinettiError (n k r d : ℕ) : ℝ :=
  2 * Real.exp (-((k : ℝ) * ((r : ℝ) + 1)) / (2 * ((n : ℝ) + k)) +
    (d : ℝ) ^ 2 / 2 * Real.log k)

/-- PDF pp.17--20: the genuine finite spectral measurement of an observable.
Nonzero orthogonal projections and distinct real eigenvalues give its spectral
alphabet; its cardinality is at most dim H. -/
structure Spectral (I : Type) [Fintype I] [DecidableEq I] where
  count : ℕ
  count_pos : 0 < count
  count_le : count ≤ Fintype.card I
  effect : Fin count → Op I
  value : Fin count → ℝ
  povm : IsPOVM effect
  idempotent : ∀ j, effect j * effect j = effect j
  orthogonal : ∀ j k, j ≠ k → effect j * effect k = 0
  nonzero : ∀ j, effect j ≠ 0
  distinct : Function.Injective value

/-- PDF p.17: reconstruct the Hermitian operator from its spectral measurement. -/
def Spectral.operator {I : Type} [Fintype I] [DecidableEq I] (S : Spectral I) : Op I :=
  ∑ j, (S.value j : ℂ) • S.effect j

/-- PDF pp.17--18, Eq.(18): arbitrary real signed coefficients in a Hermitian
Hilbert--Schmidt orthonormal decomposition. There is no positivity constraint
on the coefficients and no operator-norm equality assumption. -/
structure HSDecomposition (I : Type) [Fintype I] [DecidableEq I] (t : ℕ) where
  intermediate : Fin t → Spectral I
  coeff : Fin t → ℝ
  orthonormal : ∀ i j,
    ((intermediate i).operator * (intermediate j).operatorᴴ).trace =
      if i = j then 1 else 0

/-- PDF pp.17--18: the observable is computed from its decomposition. -/
def HSDecomposition.operator {I : Type} [Fintype I] [DecidableEq I] {t : ℕ}
    (D : HSDecomposition I t) : Op I :=
  ∑ i, (D.coeff i : ℂ) • (D.intermediate i).operator

/-- PDF pp.19--21: all outcomes of the disjoint indirect and direct blocks. -/
abbrev Outcomes {I : Type} [Fintype I] [DecidableEq I] {t : ℕ}
    (D : HSDecomposition I t) (S : Spectral I) (mp q : ℕ) :=
  ((i : Fin t) → Fin mp → Fin (D.intermediate i).count) × (Fin q → Fin S.count)

/-- PDF pp.19--22: tensor effect of precisely L_1^mp tensor ... tensor
L_t^mp tensor M^q. The flattening puts all indirect blocks first. -/
def tensorBlockEffect {I : Type} [Fintype I] [DecidableEq I] {t : ℕ}
    (D : HSDecomposition I t) (S : Spectral I) (mp q : ℕ)
    (out : Outcomes D S mp q) : Op (Copies I (t * mp + q)) :=
  fun x y =>
    (∏ i : Fin t, ∏ j : Fin mp,
      (D.intermediate i).effect (out.1 i j)
        (x (Fin.castAdd q (finProdFinEquiv (i, j))))
        (y (Fin.castAdd q (finProdFinEquiv (i, j))))) *
    ∏ j : Fin q, S.effect (out.2 j)
      (x (Fin.natAdd (t * mp) j)) (y (Fin.natAdd (t * mp) j))

/-- PDF pp.21--22: P' and P'' are evaluated from the input state, never chosen
as couplings. Events involving one block automatically use its marginal. -/
def estimationEvent {I : Type} [Fintype I] [DecidableEq I] {t : ℕ}
    (D : HSDecomposition I t) (S : Spectral I) (mp q : ℕ)
    (rho : Op (Copies I (t * mp + q))) (event : Outcomes D S mp q → Prop) : ℝ :=
  ∑ out, if event out then effectProb (tensorBlockEffect D S mp q out) rho else 0

/-- PDF p.20, Eq.(25): sum of coefficient-weighted, normalized block means. -/
def indirectMean {I : Type} [Fintype I] [DecidableEq I] {t : ℕ}
    (D : HSDecomposition I t) {S : Spectral I} {mp q : ℕ}
    (out : Outcomes D S mp q) : ℝ :=
  ∑ i, D.coeff i * ((∑ j, (D.intermediate i).value (out.1 i j)) / (mp : ℝ))

/-- PDF pp.20,22: the direct mean, normalized by the actual direct-block size. -/
def directMean {I : Type} [Fintype I] [DecidableEq I] {t : ℕ}
    {D : HSDecomposition I t} (S : Spectral I) {mp q : ℕ}
    (out : Outcomes D S mp q) : ℝ :=
  (∑ j, S.value (out.2 j)) / (q : ℝ)

/-- PDF p.22, Eq.(36): the classical sampling allowance in full L1 convention. -/
def samplingError (delta : ℝ) (m d : ℕ) (hs : ℝ) : ℝ :=
  (d : ℝ) * Real.exp (-((m : ℝ) * delta ^ 2) / (8 * (d : ℝ) * hs ^ 2))

/-- Sanity: PDF p.12, empty tensor product is the scalar identity. -/
example {I W : Type} (E : W → Op I) (out : Fin 0 → W)
    (x y : Copies I 0) : tensorEffect E out x y = 1 := by
  simp [tensorEffect]

/-- Sanity: PDF p.19, a single outcome has frequency one, including normalization. -/
example {W : Type} [Fintype W] (w : W) :
    empiricalFrequency (fun _ : Fin 1 => w) w = 1 := by
  simp [empiricalFrequency]

/-- Sanity: PDF p.17, this is full L1, not half of it. -/
example : l1 (![1, 0] : Fin 2 → ℝ) ![0, 1] = 2 := by
  norm_num [l1, Fin.sum_univ_two]

/-- Sanity: PDF p.19, zero defect and n=2,w=2,delta=0 give 4. -/
example : chernoffError 0 2 0 2 = 4 := by
  norm_num [chernoffError, binEntropy2,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]

end QAlgorithms.Papers.Independent.Advance50.P30


