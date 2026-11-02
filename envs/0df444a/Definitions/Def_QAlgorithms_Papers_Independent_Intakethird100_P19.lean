-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P19
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T07:29:51.451747+00:00
-- url     : https://prove2.me/theorems/791e7bb7-2fac-4fe8-8778-bb1acfdc50d6
-- title:
--   Definitions for Entanglement manipulation and distillability beyond LOCC
-- statement:
--   The objects the formalized statements of *Entanglement manipulation and distillability beyond LOCC* (arXiv:1711.03835) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `UnitBipartiteKet`: PDF p.4: a normalized pure ket. Results require positive local dimensions.
--   - `UnitBipartiteKet.rho`: PDF p.4: the pure density represented by a unit ket.
--   - `SeparableState`: PDF p.4: normalized states in the full separable positive cone.
--   - `squaredSchmidtCoefficient`: PDF p.4: decreasing squared Schmidt coefficients, with zero padding on Alice. The reduced density is always Hermitian, so the frozen helper's non-Hermitian fallback is never used.
--   - `schmidtAt`: PDF p.4: coefficients outside the local dimension are zero.
--   - `finiteSchmidtRank`: PDF p.4: Schmidt rank counts strictly positive squared coefficients.
--   - `traceBilinearDual`: PDF p.5: trace-bilinear dual, computed on every matrix unit.
--   - `sourceOutputChoi`: PDF p.5: unnormalized Choi operator, output factor first.
--   - `partyGroupedChoi`: PDF p.5: regroup Choi factors across Alice-out Alice-in : Bob-out Bob-in.
--   - `NE`: PDF p.6, Definition 2.1: preserve the entire cone, without ancillary closure.
--   - `DNE`: PDF p.6, Definition 2.2: the dual need not be trace preserving.
--   - `PPTPositive`: PDF p.4: the PPT positive cone includes subnormalized and zero operators.
--   - `PPTPreserving`: PDF p.6, Definition 2.1: PPT preservation, distinct from PPT Choi.
--   - `SEP`: PDF p.5: separable CP map, without a TP assumption.
--   - `ChoiPPT`: PDF pp.5-6: PPT of the Choi operator across grouped parties.
--   - `partyAmplification`: PDF p.6: identity amplification preserves off-diagonal ancilla blocks. The enlarged cut is A E : B F.
--   - `KNE`: PDF p.6, Definition 2.3: k-dimensional ancilla at each party.
--   - `KPPT`: PDF p.6, Definition 2.4: preserve the amplified PPT cone.
--   - `CompleteNE`: PDF p.6: complete non-entangling, independent of Choi separability.
--   - `CompletePPT`: PDF p.6: complete PPT preservation, independent of PPT Choi.
--   - `tensorMaps`: PDF pp.15-16: two maps on two copies, regrouped across Alice:Bob.
--   - `noiseRobustness`: PDF p.8, Eq.(3): fixed separable-noise robustness; an empty set gives infinity.
--   - `standardStateRobustness`: PDF p.8, Eqs.(2)-(3): standard robustness, using separable noise. For normalized finite states the feasible set is nonempty and bounded below. This definition is not generalized robustness.
--   - `RenyiOrder`: PDF p.9: extended order; its inversion sends zero to infinity.
--   - `schmidtRenyi`: PDF p.9: all four entropy branches, in bits and using squared coefficients.
--   - `petzStateDivergence`: PDF p.10: Petz divergence in bits on states; support violations give infinity.
--   - `relativeRenyi`: PDF p.10: infimum over every separable density, without a full-rank restriction.
--   - `Witness`: PDF pp.6-7: Hermitian and nonnegative on the separable cone. Zero and positive semidefinite witnesses are permitted.
--   - `frobenius`: PDF p.16: Frobenius norm, not operator norm.
--   - `binaryMeasurePrepare`: PDF p.5, Eq.(1): measure-and-prepare on all operators.
--   - `witnessMap`: PDF pp.16-17, Eq.(21): the constructed map, including the factor 2I.
--   - `Undetected`: PDF p.18, Definition 2.5: inequalities on the regrouped unnormalized Choi.
--   - `swapOperator`: PDF p.4: the swap (flip) operator.
--   - `betaWernerState`: PDF p.21, Eq.(29): the source Werner parameterization.
--   - `antisymmetricDensity`: PDF p.14: the specific input for the unbounded negativity ratio.
--   - `negativityMap`: PDF p.14, Eq.(15): the specific PPT-preserving map in Theorem 10.
--   - `Coisometry`: PDF p.21: rectangular coisometry, not a square idempotent.
--   - `localCoisometryCompression`: PDF p.22: unnormalized compression, which may be zero.
--   - `compressChoi`: PDF p.21, Eq.(28): Choi compression, regrouped by party.
--   - `rankThreeKet`: PDF p.23: canonical rank-three detector in the first three coordinates.
--   - `rankThreeMap`: PDF p.23: Eq.(21) with the rank-three partially transposed projector.
--   - `powerDividedDifference`: PDF p.28, Eq.(46): divided difference with the diagonal derivative branch.
--   - `partyCopies`: PDF p.15: n copies encoded by fixed local tuple enumerations. The cut is A^n:B^n; the empty tensor product at n=0 is 1.
--   - `LOCCDistillable`: PDF p.15: deterministic LOCC distillation in trace norm. Finite approximants also describe distillation using the closure of LOCC: the error tends to zero.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, https://arxiv.org/abs/1711.03835v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

/-!
Statements from Chitambar, de Vicente, Girard and Gour, arXiv:1711.03835v2.
All citations use PDF pages. Exact accepted interfaces are imported; local
definitions specialize the finite product-basis model where accepted interfaces differ. No claim concerns the infinite-dimensional objectives of arXiv:2007.14270.
Lemma 8 is corrected as its proof requires. Theorem 16 and its tensor-rank
consequence are excluded for the counterexample recorded in HARD.md.
-/

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter
open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

-- Exact accepted interfaces; no local aliases or duplicate definitions.
open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)
open QAlgorithms.Papers.Independent.Information100.P19 (Bip)
open QAlgorithms.Papers.Independent.Information100.P69 (CP)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- PDF p.4: a normalized pure ket. Results require positive local dimensions. -/
structure UnitBipartiteKet (a b : ℕ) where
  ket : EuclideanSpace ℂ (Fin a × Fin b)
  normalized : ‖ket‖ = 1

/-- PDF p.4: the pure density represented by a unit ket. -/
def UnitBipartiteKet.rho {a b : ℕ} (psi : UnitBipartiteKet a b) : Bip a b := pureDensity psi.ket

/-- PDF p.4: normalized states in the full separable positive cone. -/
def SeparableState {A B : Type} [Fintype A] [Fintype B]
    (X : Op (A × B)) : Prop := IsDensityMatrix X ∧ IsSeparablePositive X

/-- PDF p.4: decreasing squared Schmidt coefficients, with zero padding on Alice.
The reduced density is always Hermitian, so the frozen helper's non-Hermitian
fallback is never used. -/
def squaredSchmidtCoefficient {a b : ℕ} (psi : EuclideanSpace ℂ (Fin a × Fin b)) (i : Fin a) : ℝ :=
  ascEigenvalues (traceRight (pureDensity psi))
    (Fin.cast (Fintype.card_fin a).symm i.rev)

/-- PDF p.4: coefficients outside the local dimension are zero. -/
def schmidtAt {a b : ℕ} (psi : EuclideanSpace ℂ (Fin a × Fin b)) (j : ℕ) : ℝ :=
  if h : j < a then squaredSchmidtCoefficient psi ⟨j, h⟩ else 0

/-- PDF p.4: Schmidt rank counts strictly positive squared coefficients. -/
def finiteSchmidtRank {a b : ℕ} (psi : EuclideanSpace ℂ (Fin a × Fin b)) : ℕ :=
  (Finset.univ.filter fun i => 0 < squaredSchmidtCoefficient psi i).card

/-- PDF p.5: trace-bilinear dual, computed on every matrix unit. -/
def traceBilinearDual {I J : Type} [Fintype I] [Fintype J] (L : Superop I J) : Superop J I :=
  fun Y i j => (L (Matrix.single j i 1) * Y).trace

/-- PDF p.5: unnormalized Choi operator, output factor first. -/
def sourceOutputChoi {I J : Type} [Fintype I] (L : Superop I J) : Op (J × I) :=
  (QAlgorithms.Papers.Independent.Information100.P69.choi L).submatrix Prod.swap Prod.swap

/-- PDF p.5: regroup Choi factors across Alice-out Alice-in : Bob-out Bob-in. -/
def partyGroupedChoi {A B C D : Type} [Fintype A] [Fintype B]
    (L : Superop (A × B) (C × D)) : Op ((C × A) × (D × B)) :=
  (sourceOutputChoi L).submatrix (fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2)))

/-- PDF p.6, Definition 2.1: preserve the entire cone, without ancillary closure. -/
def NE {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (L : Superop (A × B) (C × D)) : Prop :=
  CP L ∧ ∀ X, IsSeparablePositive X → IsSeparablePositive (L X)

/-- PDF p.6, Definition 2.2: the dual need not be trace preserving. -/
def DNE {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (L : Superop (A × B) (C × D)) : Prop := NE L ∧ NE (traceBilinearDual L)

/-- PDF p.4: the PPT positive cone includes subnormalized and zero operators. -/
def PPTPositive {A B : Type} [Fintype A] [Fintype B] (X : Op (A × B)) : Prop :=
  X.PosSemidef ∧ (partialTransposeFirst X).PosSemidef

/-- PDF p.6, Definition 2.1: PPT preservation, distinct from PPT Choi. -/
def PPTPreserving {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (L : Superop (A × B) (C × D)) : Prop :=
  CP L ∧ ∀ X, PPTPositive X → PPTPositive (L X)

/-- PDF p.5: separable CP map, without a TP assumption. -/
def SEP {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (L : Superop (A × B) (C × D)) : Prop := CP L ∧ IsSeparablePositive (partyGroupedChoi L)

/-- PDF pp.5-6: PPT of the Choi operator across grouped parties. -/
def ChoiPPT {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (L : Superop (A × B) (C × D)) : Prop := CP L ∧ PPTPositive (partyGroupedChoi L)

/-- PDF p.6: identity amplification preserves off-diagonal ancilla blocks.
The enlarged cut is A E : B F. -/
def partyAmplification {A B C D E F : Type} (L : Superop (A × B) (C × D)) :
    Superop ((A × E) × (B × F)) ((C × E) × (D × F)) :=
  fun X p q => L (fun i j => X ((i.1, p.1.2), (i.2, p.2.2))
    ((j.1, q.1.2), (j.2, q.2.2))) (p.1.1, p.2.1) (q.1.1, q.2.1)

/-- PDF p.6, Definition 2.3: k-dimensional ancilla at each party. -/
def KNE {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (k : ℕ) (L : Superop (A × B) (C × D)) : Prop :=
  0 < k ∧ CP L ∧ NE (partyAmplification (E := Fin k) (F := Fin k) L)

/-- PDF p.6, Definition 2.4: preserve the amplified PPT cone. -/
def KPPT {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (k : ℕ) (L : Superop (A × B) (C × D)) : Prop :=
  0 < k ∧ CP L ∧ PPTPreserving (partyAmplification (E := Fin k) (F := Fin k) L)

/-- PDF p.6: complete non-entangling, independent of Choi separability. -/
def CompleteNE {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (L : Superop (A × B) (C × D)) : Prop := ∀ k : ℕ, 0 < k → KNE k L

/-- PDF p.6: complete PPT preservation, independent of PPT Choi. -/
def CompletePPT {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (L : Superop (A × B) (C × D)) : Prop := ∀ k : ℕ, 0 < k → KPPT k L

/-- PDF pp.15-16: two maps on two copies, regrouped across Alice:Bob. -/
def tensorMaps {A B C D E F G H : Type}
    [Fintype A] [Fintype B] [Fintype E] [Fintype F]
    (L : Superop (A × B) (C × D)) (M : Superop (E × F) (G × H)) :
    Superop ((A × E) × (B × F)) ((C × G) × (D × H)) :=
  fun X p q => ∑ i : A × B, ∑ j : A × B, ∑ s : E × F, ∑ t : E × F,
    X ((i.1, s.1), (i.2, s.2)) ((j.1, t.1), (j.2, t.2)) *
      L (Matrix.single i j 1) (p.1.1, p.2.1) (q.1.1, q.2.1) *
      M (Matrix.single s t 1) (p.1.2, p.2.2) (q.1.2, q.2.2)

/-- PDF p.8, Eq.(3): fixed separable-noise robustness; an empty set gives infinity. -/
def noiseRobustness {A B : Type} [Fintype A] [Fintype B]
    (rho sigma : Op (A × B)) : ℝ≥0∞ :=
  sInf {s | ∃ t : ℝ, 0 ≤ t ∧ s = ENNReal.ofReal t ∧
    SeparableState sigma ∧ IsSeparablePositive (rho + (t : ℂ) • sigma)}

/-- PDF p.8, Eqs.(2)-(3): standard robustness, using separable noise.
For normalized finite states the feasible set is nonempty and bounded below.
This definition is not generalized robustness. -/
def standardStateRobustness {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B)) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ ∃ sigma : Op (A × B), SeparableState sigma ∧
    IsSeparablePositive (rho + (s : ℂ) • sigma)}

/-- PDF p.9: extended order; its inversion sends zero to infinity. -/
abbrev RenyiOrder := ℝ≥0∞

/-- PDF p.9: all four entropy branches, in bits and using squared coefficients. -/
def schmidtRenyi {a b : ℕ} (alpha : RenyiOrder)
    (psi : EuclideanSpace ℂ (Fin a × Fin b)) : ℝ :=
  if alpha = ⊤ then -Real.logb 2 (schmidtAt psi 0)
  else if alpha = 0 then Real.logb 2 (finiteSchmidtRank psi)
  else if alpha = 1 then -∑ i, squaredSchmidtCoefficient psi i * Real.logb 2 (squaredSchmidtCoefficient psi i)
  else Real.logb 2 (∑ i, Real.rpow (squaredSchmidtCoefficient psi i) alpha.toReal) / (1 - alpha.toReal)

/-- PDF p.10: Petz divergence in bits on states; support violations give infinity. -/
def petzStateDivergence {I : Type} [Fintype I] (alpha : ℝ) (rho sigma : Op I) : ℝ≥0∞ :=
  if h : IsDensityMatrix rho ∧ IsDensityMatrix sigma then
    if alpha = 1 then
      QuantumLoss.umegakiEntropy rho sigma h.1 h.2 / ENNReal.ofReal (Real.log 2)
    else if 1 < alpha ∧ ¬ SupportIncluded rho sigma then ⊤
    else
      let z := (supportPower rho alpha * supportPower sigma (1 - alpha)).trace.re
      if 0 < z then ENNReal.ofReal (Real.logb 2 z / (alpha - 1)) else ⊤
  else ⊤

/-- PDF p.10: infimum over every separable density, without a full-rank restriction. -/
def relativeRenyi {A B : Type} [Fintype A] [Fintype B]
    (alpha : ℝ) (rho : Op (A × B)) : ℝ≥0∞ :=
  sInf {v | ∃ sigma : Op (A × B), SeparableState sigma ∧ v = petzStateDivergence alpha rho sigma}

/-- PDF pp.6-7: Hermitian and nonnegative on the separable cone.
Zero and positive semidefinite witnesses are permitted. -/
def Witness {A B : Type} [Fintype A] [Fintype B] (W : Op (A × B)) : Prop :=
  W.IsHermitian ∧ ∀ X, IsSeparablePositive X → 0 ≤ (W * X).trace.re

/-- PDF p.16: Frobenius norm, not operator norm. -/
def frobenius {I : Type} [Fintype I] (W : Op I) : ℝ :=
  Real.sqrt (∑ i, ∑ j, Complex.normSq (W i j))

/-- PDF p.5, Eq.(1): measure-and-prepare on all operators. -/
def binaryMeasurePrepare {I J : Type} [Fintype I]
    (A : Op I) (rho sigma : Op J) : Superop I J :=
  fun X => (A * X).trace • rho + ((1 - A) * X).trace • sigma

/-- PDF pp.16-17, Eq.(21): the constructed map, including the factor 2I. -/
def witnessMap {a b : ℕ} (W : Bip a b) : Superop (Fin a × Fin b) (Fin 2 × Fin 2) :=
  binaryMeasurePrepare ((1 / 3 : ℂ) • (W + (2 : ℂ) • 1)) ((1 / 4 : ℂ) • 1) (epr 2)

/-- PDF p.18, Definition 2.5: inequalities on the regrouped unnormalized Choi. -/
def Undetected {a b c d n : ℕ}
    (W : Fin n → Op ((Fin c × Fin a) × (Fin d × Fin b)))
    (L : Superop (Fin a × Fin b) (Fin c × Fin d)) : Prop :=
  CP L ∧ ∀ i, 0 ≤ (W i * partyGroupedChoi L).trace.re

/-- PDF p.4: the swap (flip) operator. -/
def swapOperator (d : ℕ) : Bip d d := fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- PDF p.21, Eq.(29): the source Werner parameterization. -/
def betaWernerState (d : ℕ) (beta : ℝ) : Bip d d :=
  (((d : ℂ) ^ 2 - ((beta + 1 : ℝ) : ℂ))⁻¹ : ℂ) •
    (1 - (((beta + 1) / d : ℝ) : ℂ) • swapOperator d)

/-- PDF p.14: the specific input for the unbounded negativity ratio. -/
def antisymmetricDensity (d : ℕ) : Bip d d :=
  (((d : ℂ) * ((d - 1 : ℕ) : ℂ))⁻¹ : ℂ) • (1 - swapOperator d)

/-- PDF p.14, Eq.(15): the specific PPT-preserving map in Theorem 10. -/
def negativityMap (d : ℕ) : Superop (Fin d × Fin d) (Fin d × Fin d) :=
  binaryMeasurePrepare (((d + 1 : ℂ)⁻¹ : ℂ) • ((d : ℂ) • 1 + swapOperator d))
    (((d : ℂ) ^ 2)⁻¹ • 1) (epr d)

/-- PDF p.21: rectangular coisometry, not a square idempotent. -/
def Coisometry {k d : ℕ} (P : Matrix (Fin k) (Fin d) ℂ) : Prop := P * Pᴴ = 1

/-- PDF p.22: unnormalized compression, which may be zero. -/
def localCoisometryCompression {k d : ℕ} (P Q : Matrix (Fin k) (Fin d) ℂ) (X : Bip d d) : Bip k k :=
  Matrix.kronecker P Q * X * (Matrix.kronecker P Q)ᴴ

/-- PDF p.21, Eq.(28): Choi compression, regrouped by party. -/
def compressChoi {d k : ℕ} (L : Superop (Fin d × Fin d) (Fin d × Fin d))
    (P Q : Matrix (Fin k) (Fin d) ℂ) : Op ((Fin d × Fin k) × (Fin d × Fin k)) :=
  let T := Matrix.kronecker (Matrix.kronecker (1 : Op (Fin d)) P)
    (Matrix.kronecker (1 : Op (Fin d)) Q)
  T * partyGroupedChoi L * Tᴴ

/-- PDF p.23: canonical rank-three detector in the first three coordinates. -/
def rankThreeKet (d : ℕ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 ∧ p.1.val < 3 then ((Real.sqrt 3)⁻¹ : ℂ) else 0

/-- PDF p.23: Eq.(21) with the rank-three partially transposed projector. -/
def rankThreeMap (d : ℕ) : Superop (Fin d × Fin d) (Fin 2 × Fin 2) :=
  witnessMap (partialTransposeFirst (pureDensity (rankThreeKet d)))

/-- PDF p.28, Eq.(46): divided difference with the diagonal derivative branch. -/
def powerDividedDifference (alpha x y : ℝ) : ℝ :=
  if x = y then (1 - alpha) * Real.rpow x (-alpha)
  else (Real.rpow x (1 - alpha) - Real.rpow y (1 - alpha)) / (x - y)

/-- PDF p.15: n copies encoded by fixed local tuple enumerations.
The cut is A^n:B^n; the empty tensor product at n=0 is 1. -/
def partyCopies {a b : ℕ} (rho : Bip a b) (n : ℕ) :
    Bip (Fintype.card (Fin n → Fin a)) (Fintype.card (Fin n → Fin b)) :=
  fun p q => ∏ j : Fin n,
    rho ((Fintype.equivFin (Fin n → Fin a)).symm p.1 j,
      (Fintype.equivFin (Fin n → Fin b)).symm p.2 j)
    ((Fintype.equivFin (Fin n → Fin a)).symm q.1 j,
      (Fintype.equivFin (Fin n → Fin b)).symm q.2 j)

/-- PDF p.15: deterministic LOCC distillation in trace norm. Finite approximants
also describe distillation using the closure of LOCC: the error tends to zero. -/
def LOCCDistillable {a b : ℕ} (rho : Bip a b) : Prop :=
  IsDensityMatrix rho ∧ ∃ L : (n : ℕ) →
    Superop (Fin (Fintype.card (Fin (n + 1) → Fin a)) ×
      Fin (Fintype.card (Fin (n + 1) → Fin b))) (Fin 2 × Fin 2),
    (∀ n, FiniteLOCC (L n) ∧ IsChannel (L n)) ∧
    Tendsto (fun n => traceNorm (L n (partyCopies rho (n + 1)) - epr 2)) atTop (nhds 0)

/-- Sanity: rank-one currency is a scalar density. PDF p.4. -/
example : epr 1 (0, 0) (0, 0) = 1 := by simp [epr]

/-- Sanity: Bell entries have the source normalization. PDF p.4. -/
example : epr 2 (0, 0) (1, 1) = 1 / 2 := by norm_num [epr]

/-- Sanity: zero is in the PPT cone. PDF p.4. -/
example {A B : Type} [Fintype A] [Fintype B] : PPTPositive (0 : Op (A × B)) :=
  ⟨Matrix.PosSemidef.zero, Matrix.PosSemidef.zero⟩

/-- Sanity: zero is a permitted witness. PDF p.7. -/
example {A B : Type} [Fintype A] [Fintype B] : Witness (0 : Op (A × B)) := by
  refine ⟨Matrix.isHermitian_zero, ?_⟩
  intro X hX
  simp

/-- Sanity: a zero effect prepares only the second state. PDF p.5. -/
example {I J : Type} [Fintype I] (rho sigma : Op J) (X : Op I) :
    binaryMeasurePrepare 0 rho sigma X = X.trace • sigma := by simp [binaryMeasurePrepare]

/-- Sanity: amplified identity acts on off-diagonal blocks too. PDF p.6. -/
example {A B E F : Type} (X : Op ((A × E) × (B × F))) :
    partyAmplification (fun Y : Op (A × B) => Y) X = X := rfl

/-- Sanity: the diagonal derivative at alpha=2, x=1. PDF pp.28-30. -/
example : powerDividedDifference 2 1 1 = -1 := by norm_num [powerDividedDifference]

/-- Sanity: zero copies give the scalar identity. PDF p.15. -/
example {a b : ℕ} (rho : Bip a b)
    (p q : Fin (Fintype.card (Fin 0 → Fin a)) × Fin (Fintype.card (Fin 0 → Fin b))) :
    partyCopies rho 0 p q = 1 := by simp [partyCopies]

/-- Sanity: absent Schmidt coefficients are zero. PDF p.4. -/
example {a b : ℕ} (psi : EuclideanSpace ℂ (Fin a × Fin b)) :
    schmidtAt psi a = 0 := by simp [schmidtAt]

/-- Sanity: zero relative order corresponds to infinite Schmidt entropy order. PDF p.10. -/
example : (ENNReal.ofReal (0 : ℝ))⁻¹ = (⊤ : RenyiOrder) := by simp

/-- Sanity: the zero map is CP without being trace preserving. PDF p.5. -/
example {I J : Type} [Fintype I] [Fintype J] :
    CP (fun _ : Op I => (0 : Op J)) := by
  refine ⟨0, Fin.elim0, ?_⟩
  intro X
  simp [krausApply]

/-- Sanity: the identity's trace-bilinear dual is the identity. PDF p.5. -/
example {I : Type} [Fintype I] (Y : Op I) : traceBilinearDual (fun X : Op I => X) Y = Y := by
  ext i j
  simp [traceBilinearDual, Matrix.trace_single_mul]

/-- Sanity: the zero map has zero unnormalized Choi representation. PDF p.5. -/
example {I J : Type} [Fintype I] :
    sourceOutputChoi (fun _ : Op I => (0 : Op J)) = 0 := rfl

/-- Sanity: the support power at zero preserves the zero kernel. PDF p.10. -/
example {I : Type} [Fintype I] : supportPower (0 : Op I) 0 = 0 := by
  simp [supportPower, cfc_zero]

/-- Sanity: the identity support projector is the identity. PDF p.10. -/
example {I : Type} [Fintype I] : supportPower (1 : Op I) 0 = 1 := by
  simp [supportPower, cfc_one]

/-- Sanity: the zero witness has zero Frobenius norm. PDF p.16. -/
example {I : Type} [Fintype I] : frobenius (0 : Op I) = 0 := by
  simp [frobenius]

/-- Sanity: the identity is a full-dimensional coisometry. PDF p.21. -/
example (d : ℕ) : Coisometry (1 : Matrix (Fin d) (Fin d) ℂ) := by
  simp [Coisometry]

/-- Sanity: the central Werner parameter gives the maximally mixed state. PDF p.21. -/
example (d : ℕ) : betaWernerState d (-1) = (((d : ℂ) ^ 2)⁻¹ : ℂ) • (1 : Bip d d) := by
  simp [betaWernerState]

end QAlgorithms.Papers.Independent.Intakethird100.P19


