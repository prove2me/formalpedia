-- Prove2me | Definitions.Def_OAIQ042S011
-- name    : OAIQ042S011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:53:41.057369+00:00
-- url     : https://prove2.me/theorems/15dfb6df-6cc3-4337-aa10-57316c4dcb30
-- title:
--   Definitions bundle OAIQ042S011 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 161 declarations of OpenAI's Lean: 19 definitions, 1 inductive type or structure and 141 theorems. The definitions and types are `OAI.CriticalStrip.Diagram.VacuumPolynomialData`, `OAI.CriticalStrip.Diagram.VacuumPolynomialData.W`, `OAI.CriticalStrip.Diagram.archCandidate`, `OAI.CriticalStrip.Diagram.archEvaluate`, `OAI.CriticalStrip.Diagram.archPolynomialAt`, `OAI.CriticalStrip.Diagram.archRoot`, `OAI.CriticalStrip.Diagram.archRootScalar`, `OAI.CriticalStrip.Diagram.deletionMap`, `OAI.CriticalStrip.Diagram.firstZeroRaw`, `OAI.CriticalStrip.Diagram.laurentResidual`, `OAI.CriticalStrip.Diagram.mergeMap`, `OAI.CriticalStrip.Diagram.movingBoxes`, `OAI.CriticalStrip.Diagram.movingStep`, `OAI.CriticalStrip.Diagram.nodalExchangePolynomial`, `OAI.CriticalStrip.Diagram.northSource`, `OAI.CriticalStrip.Diagram.rawRestricted`, `OAI.CriticalStrip.Diagram.reducedNodalDatum`, `OAI.CriticalStrip.Diagram.scalarArchNumerator`, `OAI.CriticalStrip.Diagram.vacuumData_zero`, `OAI.CriticalStrip.HoneycombBranch.exitWeight`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: `StripMass_ArchRoots`, `StripMass_AugmentedTail`, `StripMass_BottomPadding`, `StripMass_FirstFlatSpecialization`, `StripMass_FirstThree`, `StripMass_FluxWindow`, `StripMass_InterpolantCovariance`, `StripMass_LastRow`, `StripMass_LaurentNumerator`, `StripMass_MergePairCandidate`, `StripMass_NodalEmpty`, `StripMass_NodalExchange`, `StripMass_NodalRegularity`, `StripMass_NodalScalarDeletion`, `StripMass_NodalTorusValue`, `StripMass_PairSelfNode`, `StripMass_ResidualEvaluation`, `StripMass_ResidualParityCoefficients`, `StripMass_RestrictedDiagrams`, `StripMass_ScalarBridge`, `StripMass_ScalarDeleteContinuation`, `StripMass_ScalarFlat`, `StripMass_ScalarMergeTrig`, `StripMass_Specialization`, `StripMass_SpecializationPolynomial`, `StripMass_SplitGluing`, `StripMass_SwapVacancy`, `StripMass_ThreeBoxBraidPolynomial`, `StripMass_TopPadding`, `StripMass_VacuumDegree`.
--
--   **Imports.** It imports the bundles `OAIQ042S005`, `OAIQ042S006`, `OAIQ042S007` and `OAIQ042S008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ042S013` and `OAIQ042S014`; the proofs of `OAI.CriticalStrip.Diagram.nextScalar_homogeneous_of_ne` and `OAI.CriticalStrip.Diagram.scalarValue_homogeneous_ne_zero`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ042S005
import Definitions.Def_OAIQ042S006
import Definitions.Def_OAIQ042S007
import Definitions.Def_OAIQ042S008

section
-- module Solutions.OAIQ042_SS.StripMass_BottomPadding
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Circuit.compactWiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open Finset


theorem det_flat_bottom {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜)
    (hw : w 0 = identityWeights ∨ w 0 = deletionWeights) :
    (1-restrictedColumn w).det = (1-restrictedColumn (fun i => w i.succ)).det := by
  classical
  let e := Pairing.nonemptyBottomSplit n
  let M := (restrictedColumn w).submatrix e e
  have hblock : M.toBlocks₁₁ = restrictedColumn (fun i => w i.succ) := by
    ext q p
    exact column_padBottom w p.val q.val
  have hdet : (1-restrictedColumn w).det = (1-M).det := by
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv]
    rfl
  rw [hdet]
  rcases hw with hi | hd
  · rw [det_one_sub_zero_rows M, hblock]
    intro q p
    exact column_identity_bottom_row w hi (e p).val q.val.val (not_not.mp q.property)
  · rw [det_one_sub_zero_cols M, hblock]
    intro q p
    exact column_deletion_bottom_col w hd p.val.val (e q).val (not_not.mp p.property)


end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TopPadding
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Circuit.compactWiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open Finset

theorem normalizedVacuum_unique {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) (hw : VacuumRegular w)
    (v : Pairing n → 𝕜) (hv : IsNormalizedStationary w v) :
    v = normalizedVacuum w := by
  classical
  let x : NonemptyPairing n → 𝕜 := fun p => v p.val
  let Q := restrictedColumn w
  have heq : (1-Q).mulVec x = injectionColumn w := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    funext p
    have hp := congrFun hv.2 p.val
    rw [column_mulVec_nonempty, hv.1, mul_one] at hp
    change x p - Q.mulVec x p = injectionColumn w p
    exact (eq_sub_iff_add_eq.mpr (hp.trans (by rfl))).symm
  have hx : x = (1-Q)⁻¹.mulVec (injectionColumn w) := by
    rw [← heq, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hw), Matrix.one_mulVec]
  funext p
  by_cases hp : p = empty n
  · subst p; simpa [normalizedVacuum] using hv.1
  · let p' : NonemptyPairing n := ⟨p,hp⟩
    change x p' = attachEmpty ((1-Q)⁻¹.mulVec (injectionColumn w)) p'.val
    rw [attachEmpty_nonempty]
    exact congrFun hx p'

end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RestrictedDiagrams
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Circuit.compactWiring_symm _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph _root_.OAI.CriticalStrip.Diagram.gateWiring_symm _root_.OAI.CriticalStrip.Diagram.tileAdjDecidable _root_.OAI.CriticalStrip.Diagram.tileOccupiedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
def rawRestricted {R : Type*} [CommRing R] {n : ℕ} (w : Fin n → Tile → R) :
    Matrix (NonemptyPairing n) (NonemptyPairing n) R :=
  (rawColumn w).submatrix Subtype.val Subtype.val

theorem column_eq_raw {R : Type*} [CommRing R] {n : ℕ} (w : Fin n → Weights R) :
    column w = rawColumn (fun i => (w i).tile) := rfl

theorem rawColumn_scale {R : Type*} [CommRing R] {n : ℕ}
    (w : Fin n → Tile → R) (a : Fin n → R) :
    rawColumn (fun i t => a i * w i t) = (∏ i, a i) • rawColumn w := by
  classical
  ext q p
  simp only [rawColumn, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> simp [Finset.prod_mul_distrib]

theorem rawColumn_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (w : Fin n → Tile → R) :
    (rawColumn w).map f = rawColumn (fun i t => f (w i t)) := by
  classical
  ext q p
  simp only [Matrix.map_apply, rawColumn, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> simp

theorem rawRestricted_scale {R : Type*} [CommRing R] {n : ℕ}
    (w : Fin n → Tile → R) (a : Fin n → R) :
    rawRestricted (fun i t => a i * w i t) = (∏ i, a i) • rawRestricted w := by
  unfold rawRestricted
  rw [rawColumn_scale]
  rfl

theorem rawRestricted_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (w : Fin n → Tile → R) :
    (rawRestricted w).map f = rawRestricted (fun i t => f (w i t)) := by
  unfold rawRestricted
  rw [← rawColumn_map]
  rfl

theorem cleared_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (g : R →+* S) (num : Fin n → Tile → R) (a : Fin n → R)
    (w : Fin n → Weights S)
    (h : ∀ i t, g (num i t) = g (a i) * (w i).tile t) :
    (((∏ i, a i) • 1 - rawRestricted num).map g) =
      (∏ i, g (a i)) • (1 - restrictedColumn w) := by
    have hraw : (rawRestricted num).map g =
        (∏ i, g (a i)) • restrictedColumn w := by
      rw [rawRestricted_map]
      simp_rw [h]
      rw [rawRestricted_scale]
      rfl
    ext p q
    have hh := congrFun (congrFun hraw p) q
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hh
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, map_sub, map_mul, map_prod, Matrix.one_apply]
    rw [hh]
    split_ifs <;> simp
    ring

 

theorem regular_of_cleared_specialization {R K F : Type*}
    [CommRing R] [Field K] [Field F] {n : ℕ}
    (f : R →+* K) (hf : Function.Injective f) (e : R →+* F)
    (a : Fin n → R) (num : Fin n → Tile → R)
    (wa : Fin n → Weights K) (we : Fin n → Weights F)
    (ha : ∀ i, e (a i) ≠ 0)
    (hnuma : ∀ i t, f (num i t) = f (a i) * (wa i).tile t)
    (hnume : ∀ i t, e (num i t) = e (a i) * (we i).tile t)
    (he : VacuumRegular we) : VacuumRegular wa := by
  classical
  let A : Matrix (NonemptyPairing n) (NonemptyPairing n) R :=
    (∏ i, a i) • 1 - rawRestricted num
  have hAe : e A.det ≠ 0 := by
    rw [e.map_det]
    change (A.map e).det ≠ 0
    rw [show A.map e = _ from cleared_map e num a we hnume, Matrix.det_smul]
    apply mul_ne_zero
    · exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun i _ => ha i))
    · exact he
  have hA : A.det ≠ 0 := by
    intro h
    exact hAe (by rw [h, map_zero])
  have hAf : f A.det ≠ 0 := by
    intro h
    exact hA (hf (by simpa using h))
  rw [f.map_det] at hAf
  change (A.map f).det ≠ 0 at hAf
  rw [show A.map f = _ from cleared_map f num a wa hnuma, Matrix.det_smul] at hAf
  exact (mul_ne_zero_iff.mp hAf).2



end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LastRow
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Circuit.compactWiring_symm _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph _root_.OAI.CriticalStrip.Diagram.gateWiring_symm _root_.OAI.CriticalStrip.Diagram.tileAdjDecidable _root_.OAI.CriticalStrip.Diagram.tileOccupiedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset


theorem rawColumn_last_factor {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (r : Tile → K) (q p : Pairing (n+1)) :
    rawColumn (Fin.snoc w r) q p =
      lastCoefficient w q p * r (lastTile p q) := by
  classical
  unfold rawColumn
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => Tile))
    (fun tt : Tile × Configuration n =>
      if Realizes p q (Fin.snoc tt.2 tt.1)
      then ∏ i : Fin (n+1), ((Fin.snoc w r : Fin (n+1) → Tile → K) i) ((Fin.snoc tt.2 tt.1 : Configuration (n+1)) i) else 0)
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (lastTile p q)]
  · simp only [lastCoefficient, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp [Fin.prod_univ_castSucc]
  · intro a ha hne
    apply Finset.sum_eq_zero
    intro t _
    have hnot : ¬ Realizes p q (Fin.snoc t a) := by
      intro h
      have hh := h.last_eq
      simp only [Fin.snoc_last] at hh
      exact hne hh
    simp [hnot]
  · simp



theorem rawColumn_lastValue {K L : Type*} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (w : Fin n → Tile → K) (d c C : K)
    (b s t : L) (r : Tile → L) (P : Pairing (n+1) → Polynomial K)
    (hv : r .vacant = b + f C) (hc : r .cap = 2 * f d * t)
    (hu : r .vertical₀ = 2 * f d * s) (hb : r .diagonal₁ = b - f c)
    (hst : 2 * s * t = b - f c) :
    (rawColumn (Fin.snoc (fun i a => f (w i a)) r)).mulVec (lastValue f b s P) =
      lastValue f b s (lastTransform w d c C P) := by
  classical
  funext q
  simp only [Matrix.mulVec, dotProduct, rawColumn_last_factor, lastCoefficient_map]
  have he (p : Pairing (n+1)) :
      f (lastCoefficient w q p) * r (lastTile p q) * lastValue f b s P p =
        if q.Occupied (Fin.last n) then
          s * (Polynomial.C (lastCoefficient w q p) * lastFactor d c C p q * P p).eval₂ f b
        else (Polynomial.C (lastCoefficient w q p) * lastFactor d c C p q * P p).eval₂ f b := by
    by_cases hp : p.Occupied (Fin.last n) <;> by_cases hq : q.Occupied (Fin.last n)
    all_goals simp [lastTile, lastValue, lastFactor, hp, hq, hv, hc, hu, hb, map_ofNat]
    all_goals try ring_nf
    calc
      _ = f (lastCoefficient w q p) * f d * (2*s*t) * (P p).eval₂ f b := by ring
      _ = _ := by rw [hst]; ring
  simp_rw [he]
  by_cases hq : q.Occupied (Fin.last n)
  · simp [lastValue, hq, lastTransform, Polynomial.eval₂_finsetSum, Finset.mul_sum]
  · simp [lastValue, hq, lastTransform, Polynomial.eval₂_finsetSum]

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_AugmentedTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset



theorem scalarPolynomial_delete_mul {K : Type*} [Field K] [CharZero K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) (x y : K) (a : Fin n → K)
    (hxy : x ≠ y) (ha : Function.Injective a)
    (hzero : discriminant (f dd) x y = 0)
    (hD : ∀ i j, i ≠ j → ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
      discriminant (f dd) (twoCons x y a i) (twoCons x y a j) ≠ 0) :
    (∏ i : Fin n, (x-a i)*(y-a i)) *
        MvPolynomial.eval₂Hom f (twoCons x y a) (scalarPolynomial (n+2) dd rr hdd) =
      (x+y+f rr) * (∏ i : Fin n, discriminant (f dd) x (a i) * discriminant (f dd) y (a i)) *
        MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) := by
  have h := scalarNumerator_delete f n dd rr x y a hzero hD
  rw [scalarNumerator_eq_vandermonde (n+2) dd rr hdd,
    scalarNumerator_eq_vandermonde n dd rr hdd] at h
  simp only [map_mul, map_sourceVandermonde, MvPolynomial.eval₂Hom_X',
    sourceVandermonde_twoCons] at h
  apply mul_left_cancel₀ (mul_ne_zero (sub_ne_zero.mpr hxy) (sourceVandermonde_ne_zero a ha))
  calc
    _ = ((x-y) * (∏ i : Fin n, (x-a i)*(y-a i)) * sourceVandermonde a) *
        MvPolynomial.eval₂Hom f (twoCons x y a) (scalarPolynomial (n+2) dd rr hdd) := by ring
    _ = _ := h
    _ = _ := by ring

 

theorem scalarPolynomial_delete_roots {K : Type*} [Field K] [CharZero K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) (x y γ σ : K) (a : Fin n → K)
    (ha : Function.Injective (twoCons x y a))
    (hxroot : ∀ z, discriminant (f dd) x z = (z-y)*(z-γ))
    (hyroot : ∀ z, discriminant (f dd) y z = (z-x)*(z-σ))
    (hD : ∀ i j, i ≠ j → ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
      discriminant (f dd) (twoCons x y a i) (twoCons x y a j) ≠ 0) :
    MvPolynomial.eval₂Hom f (twoCons x y a) (scalarPolynomial (n+2) dd rr hdd) =
      (x+y+f rr) * (∏ i : Fin n, (a i-γ)*(a i-σ)) *
        MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) := by
  have hxy : x ≠ y := by
    simpa only [twoCons_zero,twoCons_one] using ha.ne (Fin.zero_ne_one (n := n))
  have hai : Function.Injective a := by
    intro i j he
    have hs := ha (show twoCons x y a i.succ.succ = twoCons x y a j.succ.succ by simpa using he)
    simpa only [Fin.succ_inj] using hs
  have hx : ∀ i, x-a i ≠ 0 := by
    intro i
    apply sub_ne_zero.mpr
    simpa only [twoCons_zero,twoCons_succ_succ] using ha.ne (Fin.succ_ne_zero i.succ).symm
  have hy : ∀ i, y-a i ≠ 0 := by
    intro i
    apply sub_ne_zero.mpr
    simpa only [twoCons_one,twoCons_succ_succ] using ha.ne (Fin.succ_succ_ne_one i).symm
  have hA : (∏ i : Fin n, (x-a i)*(y-a i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => mul_ne_zero (hx i) (hy i))
  have h := scalarPolynomial_delete_mul f n dd rr hdd x y a hxy hai (by simp [hxroot]) hD
  have hB : (∏ i : Fin n, discriminant (f dd) x (a i) * discriminant (f dd) y (a i)) =
      (∏ i : Fin n, (x-a i)*(y-a i)) * ∏ i : Fin n, (a i-γ)*(a i-σ) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [hxroot,hyroot]
    ring
  rw [hB] at h
  apply mul_left_cancel₀ hA
  calc
    _ = _ := h
    _ = _ := by ring

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxBraidPolynomial
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

theorem braid_numerator_7 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 7 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 34 := by
  rw [coefficient_7, coefficient_34]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq]
  all_goals ring

theorem braid_numerator_8 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 8 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 33 := by
  rw [coefficient_8, coefficient_33]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq]
  all_goals ring

theorem braid_numerator_9 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 9 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 32 := by
  rw [coefficient_9, coefficient_32]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_33 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 33 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 8 := by
  rw [coefficient_33, coefficient_8]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq]
  all_goals ring

theorem braid_numerator_34 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 34 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 7 := by
  rw [coefficient_34, coefficient_7]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq]
  all_goals ring

theorem braid_numerator_35 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 35 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 41 := by
  rw [coefficient_35, coefficient_41]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_36 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 36 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 25 := by
  rw [coefficient_36, coefficient_25]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_37 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 37 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 19 := by
  rw [coefficient_37, coefficient_19]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_38 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 38 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 42 := by
  rw [coefficient_38, coefficient_42]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring

theorem braid_numerator_39 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 39 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 39 := by
  rw [coefficient_39, coefficient_39]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_40 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 40 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 17 := by
  rw [coefficient_40, coefficient_17]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_38 hq]
  all_goals ring

theorem braid_numerator_41 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 41 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 35 := by
  rw [coefficient_41, coefficient_35]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_42 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 42 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 38 := by
  rw [coefficient_42, coefficient_38]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SwapVacancy
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical
open Finset

lemma localR_empty_row {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (p : Pairing n) : localR a w (empty n) p=if p=empty n then 1 else 0 := by
  unfold localR
  simp only [Matrix.sum_apply,Matrix.smul_apply,optionMatrix,Pairing.tileStep_empty_iff]
  by_cases hp : p=empty n
  · simp [hp,Weights.tile]
  · simp [hp]

lemma localR_mulVec_empty {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (v : Pairing n → K) : (localR a w).mulVec v (empty n)=v (empty n) := by
  simp [Matrix.mulVec,dotProduct,localR_empty_row]



def mergeMap {n m : ℕ} (r : ℕ) (hr : r+2≤n+1) :
    Matrix (Pairing (n+1)) (Pairing n) (SpectralField m) :=
  localR (PartialColumn.rowPosition r hr) (mergeWeights (constF m phase)) *
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r+1,by omega⟩))

 
def deletionMap {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    Matrix (Pairing (n+2)) (Pairing n) (SpectralField m) :=
  localR (PartialColumn.rowPosition r hr) deletionWeights *
    (functionMatrix (Pairing.map (Fin.succAboveOrderEmb (⟨r+1,by omega⟩ : Fin (n+2)))) *
      functionMatrix (Pairing.map (Fin.succAboveOrderEmb (⟨r,by omega⟩ : Fin (n+1)))))

lemma mergeMap_mulVec_empty {n m : ℕ} (r : ℕ) (hr : r+2≤n+1)
    (v : Pairing n → SpectralField m) :
    (mergeMap r hr).mulVec v (empty (n+1))=v (empty n) := by
  simp only [mergeMap]
  let E : Matrix (Pairing (n+1)) (Pairing n) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r+1,by omega⟩))
  let S := localR (PartialColumn.rowPosition r hr) (mergeWeights (constF m phase))
  calc
    _ = S.mulVec (E.mulVec v) (empty (n+1)) :=
      congrFun (Matrix.mulVec_mulVec v S E).symm _
    _ = E.mulVec v (empty (n+1)) := localR_mulVec_empty _ _ _
    _ = _ := functionMatrix_map_mulVec_empty _ _
lemma deletionMap_mulVec_empty {n m : ℕ} (r : ℕ) (hr : r+2≤n+2)
    (v : Pairing n → SpectralField m) :
    (deletionMap r hr).mulVec v (empty (n+2))=v (empty n) := by
  simp only [deletionMap]
  let E₁ : Matrix (Pairing (n+2)) (Pairing (n+1)) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r+1,by omega⟩))
  let E₀ : Matrix (Pairing (n+1)) (Pairing n) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r,by omega⟩))
  let S := localR (PartialColumn.rowPosition r hr) (deletionWeights : Weights (SpectralField m))
  calc
    _ = S.mulVec ((E₁*E₀).mulVec v) (empty (n+2)) :=
      congrFun (Matrix.mulVec_mulVec v S (E₁*E₀)).symm _
    _ = (E₁*E₀).mulVec v (empty (n+2)) := localR_mulVec_empty _ _ _
    _ = E₁.mulVec (E₀.mulVec v) (empty (n+2)) :=
      congrFun (Matrix.mulVec_mulVec v E₁ E₀).symm _
    _ = E₀.mulVec v (empty (n+1)) := functionMatrix_map_mulVec_empty _ _
    _ = _ := functionMatrix_map_mulVec_empty _ _


end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalRegularity
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical









def movingBoxes {n : ℕ} (i : Fin n) : ℕ → Matrix (Pairing (n+1)) (Pairing (n+1)) (SpectralField n)
  | 0 => 1
  | k+1 => if h : i.val < k ∧ k < n then
      localR (PartialColumn.rowPosition k (by omega))
        (torusWeights (constF n phase^3*(variableF i/variableF ⟨k,h.2⟩))) * movingBoxes i k
    else movingBoxes i k

lemma movingBoxes_initial {n : ℕ} (i : Fin n) (k : ℕ) (hk : k ≤ i.val+1) :
    movingBoxes i k=1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [movingBoxes, dite_eq_right (by omega),ih (by omega)]

lemma scalarPolynomial_eval_reindex {K : Type*} [Field K] {n : ℕ}
    (f : ℂ →+* K) (a : Fin n → K) (σ : Equiv.Perm (Fin n)) (dd rr : ℂ) (hd : dd≠0) :
    MvPolynomial.eval₂Hom f (a ∘ σ) (scalarPolynomial n dd rr hd)=
      MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hd) := by
  rw [←MvPolynomial.eval₂Hom_rename,scalarPolynomial_rename]

lemma permSpectral_nodalScalar {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permSpectral σ (nodalScalar i)=nodalScalar (σ i) := by
  have hc : (permSpectral σ).comp (algebraMap ℂ (SpectralField n))=
      algebraMap ℂ (SpectralField n) := by
    ext z
    exact permSpectral_const σ z
  have hv : (fun j : Fin (n+1) => permSpectral σ ((Fin.snoc spectralA (deletionBeta i) : Fin (n+1) → SpectralField n) j))=
      (Fin.snoc spectralA (deletionBeta (σ i)) : Fin (n+1) → SpectralField n) ∘ topPerm σ := by
    funext j
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp
  rw [nodalScalar,MvPolynomial.map_eval₂Hom,hc,hv,scalarPolynomial_eval_reindex]
  rfl

end

 

 

noncomputable section



lemma scalarPolynomial_snoc_delete_reindex {K : Type*} [Field K] {n : ℕ} (f : ℂ →+* K)
    (i : Fin (n+1)) (a : Fin (n+1) → K) (b : K) (dd rr : ℂ) (hd : dd≠0) :
    MvPolynomial.eval₂Hom f (Fin.snoc a b) (scalarPolynomial (n+2) dd rr hd)=
      MvPolynomial.eval₂Hom f (twoCons (a i) b (fun k => a (i.succAbove k)))
        (scalarPolynomial (n+2) dd rr hd) := by
  rw [←deletionPerm_tuple,scalarPolynomial_eval_reindex]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalScalarDeletion
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset
open scoped Classical



theorem nodalScalar_deletion {n : ℕ} (i : Fin (n+1)) :
    nodalScalar i=(spectralA i+deletionBeta i+constF (n+1) rho)*
      (∏ j : Fin n, (spectralA (i.succAbove j)-shiftedCosine i (phase^(-9:ℤ)))*
        (spectralA (i.succAbove j)-shiftedCosine i (phase^(9:ℤ)))) *
      MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField (n+1)))
        (fun j => spectralA (i.succAbove j)) (scalarPolynomial n d rho (by exact_mod_cast d_ne_zero)) := by
  rw [nodalScalar,scalarPolynomial_snoc_delete_reindex]
  exact scalarPolynomial_delete_roots (algebraMap ℂ (SpectralField (n+1))) n d rho _ _ _ _ _ _
    (deletionScalarTuple_injective i) (spectralA_roots i) (deletionBeta_roots i)
    (deletionScalarTuple_discriminant i)








lemma nodalScalar_factor_smaller {n : ℕ} (i : Fin (n+1)) :
    nodalScalar i=deletionDataFactor i*insertSpectral i (spectralNormalization n) := by
  rw [nodalScalar_deletion,insertSpectral_normalization]
  congr 1
  apply scalarPolynomial_eval
  · exact (spectralA_injective _).comp (Fin.succAbove_right_injective)
  · intro j k hjk
    exact spectralA_discriminant_ne _ _ (Fin.succAbove_right_injective.ne hjk)

end

 

 

noncomputable section
open scoped Classical


lemma rawLocal_weights {K : Type*} [CommRing K] {n : ℕ} (r : Position n) (w : Weights K) :
    rawLocal r w.tile=localR r w := rfl



theorem movingBox_cleared {n m : ℕ} (i j : Fin n) (r : Position m) :
    ((spectralA j-shiftedCosine i (phase^(-9:ℤ)))*
      (spectralA j-shiftedCosine i (phase^(9:ℤ)))) •
      localR r (torusWeights (constF n phase^3*(variableF i/variableF j))) =
    (-4*torusSin (variableF i*variableF j/constF n phase^6)*
      torusSin (constF n phase^3*(variableF i*variableF j))) •
      rawLocal r (torusNumerator (constF n phase^3*(variableF i/variableF j))) := by
  rw [movingBox_scalar_cancellation,←smul_smul]
  congr 1
  rw [←rawLocal_weights,←rawLocal_smul]
  congr 1
  funext t
  exact (torusNumerator_eq _ (torusL_deletion_ratio_ne_zero i j) t).symm

end





noncomputable section






open scoped Classical

 
def movingStep {n : ℕ} (i j : Fin n) : Matrix (Pairing (n+1)) (Pairing (n+1)) (SpectralField n) :=
  if i<j then localR (PartialColumn.rowPosition j.val (by omega))
      (torusWeights (constF n phase^3*(variableF i/variableF j))) else 1

lemma movingBoxes_prefix {n : ℕ} (i : Fin n) (k : ℕ) :
    movingBoxes i k=matrixPrefix (movingStep i) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [movingBoxes,matrixPrefix]
    by_cases hk:k<n
    · rw [dite_eq_left hk]
      by_cases hi:i.val<k
      · rw [dite_eq_left ⟨hi,hk⟩,ih,movingStep,ite_eq_left (show i<⟨k,hk⟩ from hi)]
      · rw [dite_eq_right (by omega),ih,movingStep,ite_eq_right (show ¬i<⟨k,hk⟩ from hi),Matrix.one_mul]
    · rw [dite_eq_right (by omega),dite_eq_right hk,ih]


lemma reducedMovingStep_eq {n : ℕ} (i j : Fin n) :
    scalarPairFactor i j • movingStep i j=reflectionFactor i j • reducedMovingStep i j := by
  by_cases hij:j=i
  · subst j
    simp [scalarPairFactor,reflectionFactor,reducedMovingStep,movingStep]
  · simp only [scalarPairFactor,reflectionFactor,reducedMovingStep,ite_eq_right hij]
    by_cases h:i<j
    · rw [ite_eq_left h,movingStep,ite_eq_left h,movingBox_cleared,smul_smul]
      congr 1
      ring
    · rw [ite_eq_right h,movingStep,ite_eq_right h,movingBox_scalar_cancellation,smul_smul,smul_smul]
      congr 1
      ring

lemma reducedMoving_product {n : ℕ} (i : Fin n) :
    (∏ j,scalarPairFactor i j) • movingBoxes i n=
      (∏ j,reflectionFactor i j) • matrixPrefix (reducedMovingStep i) n := by
  rw [movingBoxes_prefix,←matrixPrefix_smul,←matrixPrefix_smul]
  congr 1
  funext j
  exact reducedMovingStep_eq i j

end





noncomputable section
open scoped Classical


def reducedNodalDatum {n : ℕ} (i : Fin (n+1)) (p : Pairing (n+2)) : SpectralField (n+1) :=
  reducedNodalHead i (p.Occupied (Fin.last (n+1))) *
    (matrixPrefix (reducedMovingStep i) (n+1)).mulVec
      ((deletionMap i.val (show i.val+2≤n+2 by omega)).mulVec
        (fun q => insertSpectral i (rationalVacuum n q))) p

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaurentNumerator
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma deletionMapL_map {n m : ℕ} (r : ℕ) (hr:r+2≤n+2) :
    (deletionMapL (m:=m) r hr).map (algebraMap (SpectralRing m) (SpectralField m))=deletionMap r hr := by
  unfold deletionMapL
  rw [Matrix.map_mul,Matrix.map_mul,functionMatrix_ring_map,functionMatrix_ring_map,rawLocal_map]
  unfold deletionMap
  congr 2
  funext t
  cases t <;> simp [Weights.tile,deletionWeights]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalExchange
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical
open Finset



def nodalExchangePolynomial {n : ℕ} (r : ℕ) (hr : r+2≤n)
    (p : Pairing (n+1)) : Polynomial (SpectralField n) :=
  ∑ q, Polynomial.C (localR (PartialColumn.rowPosition r hr).padTop
      (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩)) p q) *
    (rationalNodalPolynomial n q).map
      (permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩))

lemma nodalExchangePolynomial_coeff {n : ℕ} (r : ℕ) (hr : r+2≤n)
    (p : Pairing (n+1)) (k : ℕ) :
    (nodalExchangePolynomial r hr p).coeff k =
    ∑ q, localR (PartialColumn.rowPosition r hr).padTop
      (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩)) p q *
      permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
        ((rationalNodalPolynomial n q).coeff k) := by
  simp only [nodalExchangePolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,
    Polynomial.coeff_map]

lemma nodalExchangePolynomial_degree {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    LastDegree n (nodalExchangePolynomial r hr) := by
  intro p k hk
  rw [nodalExchangePolynomial_coeff]
  apply sum_eq_zero
  intro q _
  by_cases hh : p.Occupied (Fin.last n) ↔ q.Occupied (Fin.last n)
  · rw [rationalNodalPolynomial_degree n q k (by rwa [←hh]),map_zero,mul_zero]
  · rw [localR_padTop_zero_last _ _ q p hh,zero_mul]

end

 

 

noncomputable section
open scoped Classical







lemma rationalNodalPolynomial_eval_div {n : ℕ} (i : Fin n) (p : Pairing (n+1)) :
    (rationalNodalPolynomial n p).eval (deletionBeta i)=
      nodalVacuum i p / (if p.Occupied (Fin.last n) then torusSin (deletionNode i) else 1) := by
  apply (eq_div_iff (by split_ifs; exact deletionNode_sine_ne_zero i; exact one_ne_zero)).mpr
  rw [mul_comm]
  exact rationalNodalPolynomial_at_node p i

end

 

 

noncomputable section



theorem torus_column_lastValue {n k : ℕ} (w : Fin n → Weights (SpectralField k))
    (z : SpectralField k) (hz : z ≠ 0) (hL : torusL (constF k phase^3/z) ≠ 0)
    (P : Pairing (n+1) → Polynomial (SpectralField k)) :
    (torusCos (z^2/constF k phase^3) + constF k C) •
      (column (Fin.snoc w (torusWeights (constF k phase^3/z)))).mulVec
        (lastValue (RingHom.id _) (torusCos (z^2/constF k phase^3)) (torusSin z) P) =
      lastValue (RingHom.id _) (torusCos (z^2/constF k phase^3)) (torusSin z)
        (lastTransform (fun i => (w i).tile) (constF k d) (constF k c) (constF k C) P) := by
  have h := torus_last_cleared z hz hL
  have he := rawColumn_lastValue (RingHom.id _) (fun i => (w i).tile)
    (constF k d) (constF k c) (constF k C)
    (torusCos (z^2/constF k phase^3)) (torusSin z) (torusSin (constF k phase^3/z))
    (fun t => (torusCos (z^2/constF k phase^3) + constF k C) *
      (torusWeights (constF k phase^3/z)).tile t) P h.1 h.2.1 h.2.2.1 h.2.2.2
    (torus_sine_pair z hz)
  rw [← he]
  have hrow : Fin.snoc (fun i => (w i).tile)
      (fun t => (torusCos (z^2/constF k phase^3) + constF k C) *
        (torusWeights (constF k phase^3/z)).tile t) =
      fun i t => (Fin.snoc (fun _ => 1) (torusCos (z^2/constF k phase^3) + constF k C) :
        Fin (n+1) → SpectralField k) i *
          ((Fin.snoc w (torusWeights (constF k phase^3/z)) : Fin (n+1) → Weights (SpectralField k)) i).tile t := by
    funext i t
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]
    | cast i => simp only [Fin.snoc_castSucc, one_mul]
  simp only [RingHom.id_apply] at *
  rw [hrow, rawColumn_scale, Matrix.smul_mulVec]
  simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const_one, one_mul]
  rfl


 

 

open Finset
open scoped Classical



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_Specialization
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram





noncomputable section
variable {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
  [Algebra R F] [IsFractionRing R F] {φ : R →+* K}



omit [IsDomain R] in
theorem rationalAt_normalizedVacuum {n : ℕ}
    (w : Fin n → Weights F) (v : Fin n → Weights K)
    (h : ∀ i t, RationalAt φ ((w i).tile t) ((v i).tile t))
    (hv : VacuumRegular v) (p : Pairing n) :
    RationalAt φ (normalizedVacuum w p) (normalizedVacuum v p) := by
  classical
  unfold normalizedVacuum attachEmpty
  split_ifs
  · exact RationalAt.one
  · apply RationalAt.mulVec
    · apply RationalAt.nonsingInv
      · intro i j
        exact (RationalAt.matrixOne i j).sub (rationalAt_column w v h i.val j.val)
      · exact hv
    · intro q
      exact rationalAt_column w v h q.val (empty n)

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SpecializationPolynomial
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma lastLaurent_box {n:ℕ} (p:Pairing (n+1)) (P:Polynomial (Laurent n))
    (hb:PolynomialBox P (fun _ => 2*n))
    (hd:∀ k,(if p.Occupied (Fin.last n) then n≤k else n<k) → P.coeff k=0) :
    LaurentBox (lastLaurent p P) (fun _ => 2*n) := by
  have hv:LaurentBox (P.eval₂ (liftLaurentHom n) (lastCosine n))
      (Fin.snoc (fun _ => 2*n) (if p.Occupied (Fin.last n) then 2*(n-1) else 2*n)) := by
    rw [Polynomial.eval₂_eq_sum]
    apply LaurentBox.sum
    intro k hk
    have hkz:P.coeff k≠0 := Polynomial.mem_support_iff.mp hk
    have hkdeg:if p.Occupied (Fin.last n) then k<n else k≤n := by
      split_ifs with hp
      · by_contra hh; exact hkz (hd k (by simp only [hp,ite_true]; omega))
      · by_contra hh; exact hkz (hd k (by simp only [hp,ite_false]; omega))
    have hi:=LaurentBox.insert (Fin.last n) (hb k)
    have hg:=hi.mul ((lastCosine_box n).pow k)
    change LaurentBox (liftLaurent (P.coeff k)*lastCosine n^k) _
    rw [liftLaurent_eq_insert]
    apply hg.mono
    intro j
    induction j using Fin.lastCases with
    | last =>
        simp only [Pi.add_apply,Fin.insertNth_apply_same,selfBound,zero_add,Fin.snoc_last]
        split_ifs at hkdeg ⊢ <;> omega
    | cast j =>
        simp only [Pi.add_apply]
        have hi:(Fin.insertNth (Fin.last n) 0 (fun _ => 2*n) : Fin (n+1) → ℕ) j.castSucc=2*n := by
          simpa only [Fin.succAbove_last] using Fin.insertNth_apply_succAbove (α:=fun _ => ℕ) (Fin.last n) 0 (fun _ => 2*n) j
        simp only [hi,Fin.snoc_castSucc,selfBound,Fin.castSucc_ne_last,ite_false,mul_zero,add_zero,le_refl]
  unfold lastLaurent
  by_cases hp:p.Occupied (Fin.last n)
  · have hn:0<n := by
      by_contra hh
      have he:n=0 := by omega
      subst n
      obtain ⟨j,hj⟩:=hp
      exact p.adj_irrefl _ (by simpa only [show j=Fin.last 0 by apply Fin.ext; omega] using hj)
    rw [ite_eq_left hp]
    apply ((lastSine_box n).mul hv).mono
    intro j
    induction j using Fin.lastCases with
    | last => simp only [Pi.add_apply,selfBound,Fin.snoc_last,hp,ite_true]; omega
    | cast j => simp [selfBound,hp]
  · rw [ite_eq_right hp,one_mul]
    apply hv.mono
    intro j
    induction j using Fin.lastCases <;> simp [hp]

end

 

 

noncomputable section
open Finset
open scoped Classical



theorem spectralColumn_lastValue {n : ℕ} (P : Pairing (n+1) → Polynomial (SpectralField n)) :
    (spectralA (Fin.last n) + constF (n+1) C) •
      (column (spectralWeights (n+1))).mulVec
        (lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n))) P) =
      lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
        (lastTransform (fun i => (spectralWeights n i).tile)
          (constF n d) (constF n c) (constF n C) P) := by
  have h := rawColumn_lastValue (liftSpectral n) (fun i => (spectralWeights n i).tile)
    (constF n d) (constF n c) (constF n C)
    (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
    (torusSin (constF (n+1) phase^3/variableF (Fin.last n)))
    (clearedSpectralRow (Fin.last n)) P
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simpa using spectral_sine_pair (Fin.last n))
  have hrow : Fin.snoc (fun i t => liftSpectral n ((spectralWeights n i).tile t))
      (clearedSpectralRow (Fin.last n)) =
      fun i t => (Fin.snoc (fun _ => 1) (spectralA (Fin.last n)+constF (n+1) C) :
        Fin (n+1) → SpectralField (n+1)) i * (spectralWeights (n+1) i).tile t := by
    funext i t
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; rfl
    | cast i => simp
  rw [hrow, rawColumn_scale, Matrix.smul_mulVec] at h
  simpa only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    prod_const_one, one_mul, ← column_eq_raw] using h


theorem rationalInterpolationResidual_transfer {n : ℕ} (p : Pairing (n+1)) :
    rationalInterpolationResidual n p =
      ((∏ i : Fin n, evalLaurent (rowDenominator i.castSucc)) / 2) *
        lastValue (liftSpectral n) (spectralA (Fin.last n))
          (torusSin (variableF (Fin.last n))) (rationalResidualPolynomial n) p := by
  have ht := congrFun (spectralColumn_lastValue (rationalNodalPolynomial n)) p
  simp only [Pi.smul_apply, smul_eq_mul] at ht
  have hden := twice_rowDenominator (Fin.last n)
  unfold rationalInterpolationResidual
  rw [Fin.prod_univ_castSucc, rationalInterpolant_eq_lastValue]
  unfold rationalResidualPolynomial lastValue at *
  by_cases hp : p.Occupied (Fin.last n)
  · simp only [hp, ite_true, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, liftSpectral_const] at *
    rw [← hden] at ht ⊢
    linear_combination ((∏ i : Fin n, evalLaurent (rowDenominator i.castSucc)) / 2) * ht
  · simp only [hp, ite_false, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, liftSpectral_const] at *
    rw [← hden] at ht ⊢
    linear_combination ((∏ i : Fin n, evalLaurent (rowDenominator i.castSucc)) / 2) * ht



end

 

 

noncomputable section
open scoped Classical

lemma rawColumn_box {n:ℕ} (w:Fin n → Tile → Laurent n)
    (h:∀i t,LaurentBox (w i t) (selfBound i 2)) :
    LaurentMatrixBox (rawColumn w) (fun _ =>2) := by
  intro p q
  unfold rawColumn
  apply LaurentBox.sum
  intro t _
  split_ifs
  · rw [←sum_selfBound n 2]
    exact LaurentBox.prod _ _ _ (fun i _ =>h i (t i))
  · exact LaurentBox.zero _

 

def laurentResidual {n:ℕ} (W:Pairing n → Laurent n) (p:Pairing n) : Laurent n :=
  (rawColumn rowNumerator).mulVec W p-(∏i:Fin n,rowDenominator i)*W p

lemma laurentResidual_box {n:ℕ} (W:Pairing n → Laurent n) (b:ℕ)
    (h:∀p,LaurentBox (W p) (fun _ =>b)) (p:Pairing n) :
    LaurentBox (laurentResidual W p) (fun _ =>b+2) := by
  apply LaurentBox.sub
  · exact ((rawColumn_box rowNumerator rowNumerator_box).mulVec h p).mono (by intro i; simp; omega)
  · have hd:LaurentBox (∏i:Fin n,rowDenominator i) (fun _ =>2) := by
      rw [←sum_selfBound n 2]
      exact LaurentBox.prod _ _ _ (fun i _ =>rowDenominator_box i)
    exact (hd.mul (h p)).mono (by intro i; simp; omega)

lemma laurentResidual_map {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (p:Pairing (n+1)) :
    evalLaurent (laurentResidual (fun p =>lastLaurent p (P p)) p)=rationalInterpolationResidual n p := by
  have hcol:(rawColumn (@rowNumerator (n+1))).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=
      (∏i:Fin (n+1),evalLaurent (rowDenominator i)) • column (spectralWeights (n+1)) := by
    rw [rawColumn_map]
    simp_rw [rowNumerator_map]
    rw [rawColumn_scale]
    rfl
  change (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) _=_
  rw [laurentResidual,map_sub,map_mul,map_prod]
  have he:(algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))
      ((rawColumn rowNumerator).mulVec (fun p =>lastLaurent p (P p)) p)=
      (((rawColumn rowNumerator).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))).mulVec (rationalInterpolant n)) p := by
    simp only [Matrix.mulVec,dotProduct,map_sum,map_mul,Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro q _
    rw [show (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (lastLaurent q (P q))=rationalInterpolant n q from lastLaurent_map q (P q) (hP q)]
  rw [he,hcol,Matrix.smul_mulVec]
  change _ - _ * evalLaurent (lastLaurent p (P p))=_
  rw [lastLaurent_map p (P p) (hP p)]
  simp only [rationalInterpolationResidual,Pi.smul_apply,smul_eq_mul,mul_sub,evalLaurent]







lemma signSpectral_column {n:ℕ} (i:Fin n) (p q:Pairing n) :
    signSpectral i (column (spectralWeights n) p q)=
      occupancySign p i*occupancySign q i*column (spectralWeights n) p q := by
  have h:=column_map (signSpectral i) (spectralWeights n)
  rw [signSpectral_spectralWeights] at h
  have he:=congrArg (fun M:Matrix (Pairing n) (Pairing n) (SpectralField n) => M p q) h
  simpa only [Matrix.map_apply,column_signTwist] using he

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_InterpolantCovariance
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma localR_map_hom {K L:Type*} [CommRing K] [CommRing L] {n:ℕ}
    (f:K →+* L) (a:Position n) (w:Weights K) :
    (localR a w).map f=localR a (w.map f) := by
  ext p q
  simp only [localR,Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,smul_eq_mul,map_sum,map_mul,Weights.map_tile]
  apply Finset.sum_congr rfl
  intro t _
  unfold optionMatrix
  split_ifs <;> simp

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarFlat
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical



theorem scalarPolynomial_cons_flat_identity (n : ℕ) (dd rr cc CC : ℂ)
    (hdd : dd≠0) (hshift : cc+rr=CC) (hlin : 2*dd*cc=CC-cc)
    (hconst : cc^2-dd^2= -cc*CC) :
    MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cons (MvPolynomial.C cc) MvPolynomial.X)
      (scalarPolynomial (n+1) dd rr hdd)=
      (∏ i : Fin n, (MvPolynomial.X i + MvPolynomial.C CC))*scalarPolynomial n dd rr hdd := by
  let f : ℂ →+* CosineField n := (algebraMap (CosineRing n) (CosineField n)).comp MvPolynomial.C
  have hc (z : ℂ) : f z=cosineConst n z := rfl
  have hv : MvPolynomial.eval₂Hom f (@cosineVar n)=algebraMap (CosineRing n) (CosineField n) := by
    apply MvPolynomial.ringHom_ext <;> intro z <;> simp [f,cosineVar]
  have hi : Function.Injective (Fin.cons (f cc) (@cosineVar n)) := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => exact (cosineVar_ne_const j cc (by simpa [hc] using hij.symm)).elim
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (cosineVar_ne_const i cc (by simpa [hc] using hij)).elim
      | succ j => exact congrArg Fin.succ (cosineVar_injective n (by simpa using hij))
  have hfirst (i : Fin n) : cosineVar i≠f cc := cosineVar_ne_const i cc
  have hsecond (i : Fin n) : cosineVar i+f CC≠0 := by
    intro he
    apply cosineVar_ne_const i (-CC)
    rw [←hc,map_neg]
    exact eq_neg_of_add_eq_zero_left he
  have hroot (z : CosineField n) : discriminant (f dd) (f cc) z=(z-f cc)*(z+f CC) :=
    flat_discriminant_map f dd cc CC hlin hconst z
  have hD (i j : Fin (n+1)) (hij:i≠j) :
      discriminant (f dd) ((Fin.cons (f cc) (@cosineVar n) : Fin (n+1) → CosineField n) i)
        ((Fin.cons (f cc) (@cosineVar n) : Fin (n+1) → CosineField n) j)≠0 := by
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => simpa only [Fin.cons_zero,Fin.cons_succ,hroot] using
          mul_ne_zero (sub_ne_zero.mpr (hfirst j)) (hsecond j)
    | succ i =>
      induction j using Fin.cases with
      | zero =>
          simp only [Fin.cons_zero,Fin.cons_succ]
          rw [discriminant_symm,hroot]
          exact mul_ne_zero (sub_ne_zero.mpr (hfirst i)) (hsecond i)
      | succ j => exact discriminant_cosineVar_ne dd hdd i j
  apply IsFractionRing.injective (CosineRing n) (CosineField n)
  rw [MvPolynomial.map_eval₂Hom,map_mul]
  have hm : (algebraMap (CosineRing n) (CosineField n))
      (∏ i : Fin n,(MvPolynomial.X i+MvPolynomial.C CC))=
      ∏ i : Fin n,(algebraMap (CosineRing n) (CosineField n))
        (MvPolynomial.X i+MvPolynomial.C CC) := map_prod _ _ _
  rw [hm]
  have ha : (fun i : Fin (n+1) => (algebraMap (CosineRing n) (CosineField n))
      ((Fin.cons (MvPolynomial.C cc) MvPolynomial.X : Fin (n+1) → CosineRing n) i))=
      Fin.cons (f cc) cosineVar := by
    funext i
    induction i using Fin.cases <;> rfl
  rw [ha]
  change MvPolynomial.eval₂Hom f (Fin.cons (f cc) cosineVar) _ = _
  rw [scalarPolynomial_eval f (n+1) dd rr hdd _ hi hD]
  rw [scalarNormalization_cons_flat _ _ _ _ _ (by simpa only [←map_add] using congrArg f hshift)
    hroot hfirst hsecond]
  rw [←scalarPolynomial_eval f n dd rr hdd _ (cosineVar_injective n)
    (fun i j _ => discriminant_cosineVar_ne dd hdd i j),hv]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [map_add]
  rfl

 
theorem scalarPolynomial_eval_cons_flat {K : Type*} [CommRing K] (f : ℂ →+* K)
    (n : ℕ) (dd rr cc CC : ℂ) (hdd : dd≠0) (hshift : cc+rr=CC)
    (hlin : 2*dd*cc=CC-cc) (hconst : cc^2-dd^2= -cc*CC) (a : Fin n → K) :
    MvPolynomial.eval₂Hom f (Fin.cons (f cc) a) (scalarPolynomial (n+1) dd rr hdd)=
      (∏ i : Fin n, (a i + f CC))*MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) := by
  have h := congrArg (MvPolynomial.eval₂Hom f a)
    (scalarPolynomial_cons_flat_identity n dd rr cc CC hdd hshift hlin hconst)
  rw [MvPolynomial.map_eval₂Hom] at h
  have hc : (MvPolynomial.eval₂Hom f a).comp MvPolynomial.C=f := by
    ext z
    simp
  have hv : (fun i : Fin (n+1) => (MvPolynomial.eval₂Hom f a)
      ((Fin.cons (MvPolynomial.C cc) MvPolynomial.X : Fin (n+1) → CosineRing n) i))=
      Fin.cons (f cc) a := by
    funext i
    induction i using Fin.cases <;> simp
  rw [hc,hv] at h
  simpa only [map_mul,map_prod,map_add,MvPolynomial.eval₂Hom_X',MvPolynomial.eval₂Hom_C] using h

end

 

 

noncomputable section

lemma source_scalarPolynomial_flat {K : Type*} [CommRing K] (f : ℂ →+* K)
    (n : ℕ) (a : Fin n → K) :
    MvPolynomial.eval₂Hom f (Fin.cons (f (c:ℂ)) a)
      (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))=
    (∏ i, (a i + f (C:ℂ)))*MvPolynomial.eval₂Hom f a
      (scalarPolynomial n d rho (by exact_mod_cast d_ne_zero)) :=
  scalarPolynomial_eval_cons_flat f n d rho c C _ (by exact_mod_cast c_add_rho_eq_C)
    flat_scalar_linear flat_scalar_constant a








open Finset
open scoped Classical


theorem rawColumn_padBottom {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (r : Tile → K) (p q : Pairing n) :
    rawColumn (Fin.cons r w) q.padBottom p.padBottom = r .vacant * rawColumn w q p := by
  classical
  unfold rawColumn
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Tile))
    (fun tt : Tile × Configuration n =>
      if Realizes p.padBottom q.padBottom (Fin.cons tt.1 tt.2)
      then ∏ i : Fin (n+1), ((Fin.cons r w : Fin (n+1) → Tile → K) i)
        ((Fin.cons tt.1 tt.2 : Configuration (n+1)) i) else 0)
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [realizes_cons_bottom_iff]
  rw [Finset.sum_eq_single Tile.vacant]
  · simp only [true_and, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp [Fin.prod_univ_succ]
  · intro a ha hav
    simp [hav]
  · simp

 
def firstZeroRaw {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (v : Pairing n → K) : Pairing (n+1) → K :=
  (rawColumn (Fin.cons (deletionWeights : Weights K).tile w)).mulVec
    (vacantBottomExtension v)

theorem mulVec_vacantBottomExtension {K : Type*} [CommRing K] {n : ℕ}
    (A : Matrix (Pairing (n+1)) (Pairing (n+1)) K) (v : Pairing n → K)
    (q : Pairing (n+1)) :
    A.mulVec (vacantBottomExtension v) q = ∑ p, A q p.padBottom * v p := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  symm
  apply Fintype.sum_of_injective Pairing.padBottom Pairing.padBottom_injective
  · intro p hp
    have h : p.Occupied 0 := by
      by_contra h
      exact hp ⟨p.restrict (Fin.succOrderEmb n), p.padBottom_restrict h⟩
    simp [vacantBottomExtension, h]
  · intro p; simp

 
theorem firstZeroRaw_vacant {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (v : Pairing n → K) (q : Pairing n) :
    firstZeroRaw w v q.padBottom = (rawColumn w).mulVec v q := by
  rw [firstZeroRaw, mulVec_vacantBottomExtension]
  simp only [rawColumn_padBottom, Weights.tile, deletionWeights, one_mul, Matrix.mulVec, dotProduct]

 
theorem deletion_column_mulVec {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Weights K) (v : Pairing (n+1) → K) :
    (column (Fin.cons deletionWeights w)).mulVec v =
      firstZeroRaw (fun i => (w i).tile) (fun p => v p.padBottom) := by
  classical
  funext q
  rw [firstZeroRaw, mulVec_vacantBottomExtension]
  simp only [Matrix.mulVec, dotProduct]
  symm
  apply Fintype.sum_of_injective Pairing.padBottom Pairing.padBottom_injective
  · intro p hp
    have h : p.Occupied 0 := by
      by_contra h
      exact hp ⟨p.restrict (Fin.succOrderEmb n), p.padBottom_restrict h⟩
    rw [column_deletion_bottom_col _ rfl _ _ h, zero_mul]
  · intro p
    congr 1
    change rawColumn _ q p.padBottom = rawColumn _ q p.padBottom
    congr 3
    funext i
    exact Fin.cases rfl (fun _ => rfl) i



theorem vacantBottomExtension_leading {K : Type*} [CommRing K] {n : ℕ}
    (P : Pairing (n+1) → Polynomial K) (m : ℕ) :
    (fun p : Pairing (n+1) => (vacantBottomExtension P p.padTop).coeff m) =
      vacantBottomExtension (fun p : Pairing n => (P p.padTop).coeff m) := by
  funext p
  by_cases hp : p.Occupied 0
  · have hp' : p.padTop.Occupied 0 := by
      simpa using (Pairing.padTop_occupied_castSucc p 0).mpr hp
    simp [vacantBottomExtension, hp, hp']
  · rw [← p.padBottom_restrict hp, Pairing.padBottom_padTop]
    simp


theorem firstZeroPolynomial_degree {K : Type*} [CommRing K] {n m : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) (hP : LastDegree m P) :
    LastDegree (m+1) (firstZeroPolynomial w d c C P) :=
  lastTransform_degree _ _ _ _ _ hP.vacantBottomExtension



theorem firstZeroPolynomial_evaluation {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) {n : ℕ} (w : Fin n → Tile → K) (d c C : K)
    (b s t : L) (r : Tile → L) (P : Pairing (n+1) → Polynomial K)
    (hv : r .vacant = b + f C) (hc : r .cap = 2 * f d * t)
    (hu : r .vertical₀ = 2 * f d * s) (hb : r .diagonal₁ = b - f c)
    (hst : 2 * s * t = b - f c) :
    firstZeroRaw (Fin.snoc (fun i a => f (w i a)) r) (lastValue f b s P) =
      lastValue f b s (firstZeroPolynomial w d c C P) := by
  have h := rawColumn_lastValue f (Fin.cons (deletionWeights : Weights K).tile w)
    d c C b s t r (vacantBottomExtension P) hv hc hu hb hst
  rw [lastValue_vacantBottomExtension] at h
  have hmap : (fun (i : Fin (n+1)) (a : Tile) =>
      f ((Fin.cons (deletionWeights : Weights K).tile w : Fin (n+1) → Tile → K) i a)) =
      Fin.cons (deletionWeights : Weights L).tile (fun i a => f (w i a)) := by
    funext i a
    refine Fin.cases ?_ (fun j => ?_) i
    · cases a <;> simp only [Fin.cons_zero, deletionWeights, Weights.tile, map_zero, map_one]
    · rfl
  rw [hmap, ← Fin.cons_snoc_eq_snoc_cons] at h
  exact h

end

 

 

noncomputable section
open Finset

theorem firstZeroRaw_rowScale {K : Type*} [CommRing K] {n : ℕ}
    (a : Fin n → K) (w : Fin n → Tile → K) (v : Pairing n → K) :
    firstZeroRaw (fun i t => a i * w i t) v =
      (∏ i, a i) • firstZeroRaw w v := by
  have h : Fin.cons (deletionWeights : Weights K).tile (fun i t => a i * w i t) =
      (fun (i : Fin (n+1)) t => (Fin.cons 1 a : Fin (n+1) → K) i *
        (Fin.cons (deletionWeights : Weights K).tile w : Fin (n+1) → Tile → K) i t) := by
    funext i t
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rfl
  rw [firstZeroRaw, h, rawColumn_scale]
  simp [Fin.prod_univ_succ, firstZeroRaw, Matrix.smul_mulVec]



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FirstFlatSpecialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical







lemma scalarPolynomial_eval_snoc_flat {K : Type*} [Field K] (f : ℂ →+* K)
    (n : ℕ) (a : Fin n → K) :
    MvPolynomial.eval₂Hom f (Fin.snoc a (f (c:ℂ)))
      (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))=
      (∏ i, (a i+f (C:ℂ)))*MvPolynomial.eval₂Hom f a
        (scalarPolynomial n d rho (by exact_mod_cast d_ne_zero)) := by
  rw [Fin.snoc_eq_cons_rotate]
  change MvPolynomial.eval₂Hom f ((Fin.cons (f (c:ℂ)) a : Fin (n+1) → K) ∘ finRotate (n+1)) _ = _
  rw [scalarPolynomial_eval_reindex,source_scalarPolynomial_flat]

lemma firstFlatSmallerScalar_eq (n : ℕ) (i : Fin (n+1)) :
    firstFlatSmallerScalar n i=
      MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField n))
        (Fin.snoc spectralA ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i))
        (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero)) := by
  induction i using Fin.cases with
  | zero =>
      simp only [firstFlatSmallerScalar,Fin.cons_zero,constF]
      rw [scalarPolynomial_eval_snoc_flat (algebraMap ℂ (SpectralField n)) n spectralA,scalarPolynomial_eval_spectral]
  | succ i => rfl

lemma rationalAt_firstFlat_nodalScalar {n : ℕ} (i : Fin (n+1)) :
    RationalAt (firstFlatEvaluation n).toRingHom (nodalScalar i)
      ((∏ j : Fin n, (spectralA j+constF n C))*
        (((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)+constF n C)*
        firstFlatSmallerScalar n i) := by
  have h := RationalAt.mv_eval (algebraMap ℂ (SpectralField (n+1)))
    (algebraMap ℂ (SpectralField n))
    (Fin.snoc spectralA (deletionBeta i))
    (Fin.snoc (Fin.cons (constF n c) spectralA)
      ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i))
    (rationalAt_const (firstFlatEvaluation n))
    (fun j => by
      induction j using Fin.lastCases with
      | last => simpa using rationalAt_firstFlat_deletionBeta i
      | cast j => simpa using rationalAt_firstFlat_spectralA j)
    (scalarPolynomial (n+2) d rho (by exact_mod_cast d_ne_zero))
  rw [←Fin.cons_snoc_eq_snoc_cons] at h
  simp only [constF] at h
  rw [source_scalarPolynomial_flat (algebraMap ℂ (SpectralField n)) (n+1)] at h
  rw [Fin.prod_univ_castSucc] at h
  simpa only [nodalScalar,Fin.snoc_castSucc,Fin.snoc_last,constF,firstFlatSmallerScalar_eq] using h

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ResidualEvaluation
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma permSpectral_column_map {n:ℕ} (σ:Equiv.Perm (Fin n)) :
    (column (spectralWeights n)).map (permSpectral σ)=column (fun i =>spectralWeights n (σ i)) := by
  rw [column_map]
  congr 1
  funext i
  exact permSpectral_spectralWeights σ i

lemma rationalAt_localR {n k l:ℕ} (φ:Laurent k →ₐ[ℂ] SpectralField l)
    (a:Position n) (w:Weights (SpectralField k)) (v:Weights (SpectralField l))
    (h:∀t,RationalAt φ.toRingHom (w.tile t) (v.tile t)) (p q:Pairing n) :
    RationalAt φ.toRingHom (localR a w p q) (localR a v p q) := by
  simp only [localR,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply RationalAt.sum
  intro t _
  apply (h t).mul
  unfold optionMatrix
  split_ifs
  · exact RationalAt.one
  · exact RationalAt.zero







lemma firstZeroRaw_smul {K:Type*} [CommRing K] {n:ℕ}
    (w:Fin n → Tile → K) (a:K) (v:Pairing n → K) :
    firstZeroRaw w (a • v)=a • firstZeroRaw w v := by
  have he:vacantBottomExtension (a • v)=a • vacantBottomExtension v := by
    funext p
    by_cases hp:p.Occupied 0 <;> simp [vacantBottomExtension,hp,Pi.smul_apply]
  rw [firstZeroRaw,he,Matrix.mulVec_smul]
  rfl

lemma rationalAt_firstFlat_normalization (n:ℕ) :
    RationalAt (firstFlatEvaluation n).toRingHom (spectralNormalization (n+1))
      ((∏ j : Fin n, (spectralA j+constF n C))*spectralNormalization n) := by
  have h:=RationalAt.mv_eval (algebraMap ℂ (SpectralField (n+1)))
    (algebraMap ℂ (SpectralField n)) spectralA (Fin.cons (constF n c) spectralA)
    (rationalAt_const (firstFlatEvaluation n)) rationalAt_firstFlat_spectralA
    (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))
  simp only [constF] at h
  rw [scalarPolynomial_eval_spectral,source_scalarPolynomial_flat,scalarPolynomial_eval_spectral] at h
  exact h







lemma torus_firstZero_lastValue {n k:ℕ} (w:Fin n → Weights (SpectralField k))
    (z:SpectralField k) (hz:z≠0) (hL:torusL (constF k phase^3/z)≠0)
    (P:Pairing (n+1) → Polynomial (SpectralField k)) :
    (torusCos (z^2/constF k phase^3)+constF k C) •
      firstZeroRaw (fun i => ((Fin.snoc w (torusWeights (constF k phase^3/z)) :
        Fin (n+1) → Weights (SpectralField k)) i).tile)
        (lastValue (RingHom.id _) (torusCos (z^2/constF k phase^3)) (torusSin z) P)=
      lastValue (RingHom.id _) (torusCos (z^2/constF k phase^3)) (torusSin z)
        (firstZeroPolynomial (fun i => (w i).tile) (constF k d) (constF k c) (constF k C) P) := by
  have h:=torus_last_cleared z hz hL
  have he:=firstZeroPolynomial_evaluation (RingHom.id _) (fun i => (w i).tile)
    (constF k d) (constF k c) (constF k C)
    (torusCos (z^2/constF k phase^3)) (torusSin z) (torusSin (constF k phase^3/z))
    (fun t => (torusCos (z^2/constF k phase^3)+constF k C)*
      (torusWeights (constF k phase^3/z)).tile t) P h.1 h.2.1 h.2.2.1 h.2.2.2
    (torus_sine_pair z hz)
  have hrow : Fin.snoc (fun i t => (RingHom.id (SpectralField k)) ((w i).tile t))
      (fun t => (torusCos (z^2/constF k phase^3)+constF k C)*
        (torusWeights (constF k phase^3/z)).tile t)=
      fun i t => (Fin.snoc (fun _ => 1) (torusCos (z^2/constF k phase^3)+constF k C) :
        Fin (n+1) → SpectralField k) i *
        ((Fin.snoc w (torusWeights (constF k phase^3/z)) : Fin (n+1) → Weights (SpectralField k)) i).tile t := by
    funext i t
    induction i using Fin.lastCases <;> simp
  rw [hrow,firstZeroRaw_rowScale] at he
  simpa only [Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,Finset.prod_const_one,one_mul] using he

lemma rationalAt_last_normalization {n:ℕ} (z:SpectralField n) (hz:z≠0) :
    RationalAt (lastEvaluation z hz).toRingHom (spectralNormalization (n+1))
      (MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField n))
        (Fin.snoc spectralA (torusCos (z^2/constF n phase^3)))
        (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))) := by
  have h:=RationalAt.mv_eval (algebraMap ℂ (SpectralField (n+1)))
    (algebraMap ℂ (SpectralField n)) spectralA
    (Fin.snoc spectralA (torusCos (z^2/constF n phase^3)))
    (rationalAt_const (lastEvaluation z hz))
    (fun i => by
      induction i using Fin.lastCases with
      | last => simpa only [Fin.snoc_last] using rationalAt_last_spectralA z hz
      | cast i => simpa only [Fin.snoc_castSucc,liftSpectral_spectralA] using
          rationalAt_last_lift z hz (spectralA i))
    (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))
  rwa [scalarPolynomial_eval_spectral] at h

lemma rationalAt_last_vacuum {n:ℕ} (z:SpectralField n) (hz:z≠0)
    (hL:torusL (constF n phase^3/z)≠0)
    (hr:VacuumRegular (Fin.snoc (spectralWeights n) (torusWeights (constF n phase^3/z))))
    (p:Pairing (n+1)) :
    RationalAt (lastEvaluation z hz).toRingHom (rationalVacuum (n+1) p)
      ((MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField n))
        (Fin.snoc spectralA (torusCos (z^2/constF n phase^3)))
        (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero)))*
        normalizedVacuum (Fin.snoc (spectralWeights n) (torusWeights (constF n phase^3/z))) p) :=
  (rationalAt_last_normalization z hz).mul
    (rationalAt_normalizedVacuum _ _ (rationalAt_last_weights z hz hL) hr p)



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FirstThree
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma rationalAt_firstThree_normalization (n:ℕ) :
    RationalAt (firstThreeEvaluation n).toRingHom (spectralNormalization (n+1))
      ((∏ j:Fin n,(spectralA j+constF n C))*spectralNormalization n) := by
  have h:=RationalAt.mv_eval (algebraMap ℂ (SpectralField (n+1)))
    (algebraMap ℂ (SpectralField n)) spectralA (Fin.cons (constF n c) spectralA)
    (rationalAt_const (firstThreeEvaluation n)) rationalAt_firstThree_spectralA
    (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))
  simp only [constF] at h
  rw [scalarPolynomial_eval_spectral,source_scalarPolynomial_flat,scalarPolynomial_eval_spectral] at h
  exact h

lemma rationalAt_firstThree_nodalScalar {n:ℕ} (i:Fin n) :
    RationalAt (firstThreeEvaluation n).toRingHom (nodalScalar i.succ)
      ((∏ j:Fin n,(spectralA j+constF n C))*(deletionBeta i+constF n C)*nodalScalar i) := by
  have h:=RationalAt.mv_eval (algebraMap ℂ (SpectralField (n+1)))
    (algebraMap ℂ (SpectralField n))
    (Fin.snoc spectralA (deletionBeta i.succ))
    (Fin.snoc (Fin.cons (constF n c) spectralA) (deletionBeta i))
    (rationalAt_const (firstThreeEvaluation n))
    (fun j => by
      induction j using Fin.lastCases with
      | last => simpa using rationalAt_firstThree_deletionBeta i.succ
      | cast j => simpa using rationalAt_firstThree_spectralA j)
    (scalarPolynomial (n+2) d rho (by exact_mod_cast d_ne_zero))
  rw [←Fin.cons_snoc_eq_snoc_cons] at h
  simp only [constF] at h
  rw [source_scalarPolynomial_flat (algebraMap ℂ (SpectralField n)) (n+1)] at h
  rw [Fin.prod_univ_castSucc] at h
  simpa only [nodalScalar,Fin.snoc_castSucc,Fin.snoc_last,constF] using h

lemma firstThreePolynomial_leading {K:Type*} [CommRing K] {n m:ℕ} (C:K)
    (P:Pairing (n+1) → Polynomial K) (hP:LastDegree m P) (p:Pairing (n+1)) :
    (firstThreePolynomial C P p.padTop).coeff (m+1)=
      vacantBottomExtension (fun q => (P q.padTop).coeff m) p := by
  by_cases hp:p.Occupied 0
  · have ht:p.padTop.Occupied 0 := by
      exact (p.padTop_occupied_castSucc 0).mpr hp
    simp [firstThreePolynomial,vacantBottomExtension,hp,ht]
  · rw [←p.padBottom_restrict hp,Pairing.padBottom_padTop,
      firstThreePolynomial_padBottom,vacantBottomExtension_padBottom]
    have hz:=hP (p.restrict (Fin.succOrderEmb n)).padTop (m+1) (by simp)
    simp [add_mul,Polynomial.coeff_X_mul,hz]







lemma vacuumRegular_of_rationalAt {R F K:Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] (φ:R →+* K) {n:ℕ}
    (w:Fin n → Weights F) (v:Fin n → Weights K)
    (h:∀i t,RationalAt φ ((w i).tile t) ((v i).tile t))
    (hv:VacuumRegular v) : VacuumRegular w := by
  have hb:∀i j,RationalAt φ ((1-restrictedColumn w) i j) ((1-restrictedColumn v) i j) := by
    intro i j
    exact (RationalAt.matrixOne i j).sub (rationalAt_column w v h i.val j.val)
  exact (RationalAt.det (1-restrictedColumn w) (1-restrictedColumn v) hb).ne_zero hv

lemma torusRegular_of_rationalAt {m n r:ℕ} (φ:Laurent m →ₐ[ℂ] SpectralField n)
    (x:Fin r → SpectralField m) (y:Fin r → SpectralField n)
    (h:∀i,RationalAt φ.toRingHom (x i) (y i))
    (hy:∀i,y i≠0) (hL:∀i,torusL (y i)≠0)
    (hv:VacuumRegular (fun i =>torusWeights (y i))) :
    VacuumRegular (fun i =>torusWeights (x i)) := by
  apply vacuumRegular_of_rationalAt φ.toRingHom _ _ _ hv
  intro i t
  exact rationalAt_torusWeights φ (h i) (hy i) (hL i) t

lemma rationalAt_phaseRow {n:ℕ} (i:Fin n) (k:ℕ) :
    RationalAt (allOneEvaluation n).toRingHom (constF n phase^k/variableF i) (constF 0 phase^k) := by
  simpa only [div_one] using ((rationalAt_const (allOneEvaluation n) phase).pow k).div
    (rationalAt_variable (fun _ : Fin n =>(1:SpectralField 0)) (fun _ =>one_ne_zero) i) one_ne_zero

lemma torusL_phaseRow_ne_zero {n:ℕ} (i:Fin n) (k:ℕ) (hk:k≤3) :
    torusL (constF n phase^k/variableF i)≠0 :=
  (rationalAt_torusL (allOneEvaluation n) (rationalAt_phaseRow i k)
    (pow_ne_zero _ (constF_phase_ne_zero 0))).ne_zero (torusL_phase_small_ne_zero 0 k hk)



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarDeleteContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical



theorem scalarPolynomial_delete_continuation {K:Type*} [Field K] [CharZero K]
    (f:ℂ →+* K) (n:ℕ) (dd rr:ℂ) (hdd:dd≠0) (x y γ σ:K) (hxy:x≠y)
    (hxroot:∀z,discriminant (f dd) x z=(z-y)*(z-γ))
    (hyroot:∀z,discriminant (f dd) y z=(z-x)*(z-σ)) (a:Fin n → K) :
    MvPolynomial.eval₂Hom f (twoCons x y a) (scalarPolynomial (n+2) dd rr hdd)=
      (x+y+f rr)*(∏i:Fin n,(a i-γ)*(a i-σ))*
        MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) := by
  let g:K →+* PolynomialField K n:=genericConst n
  have rootsMap (v u w:K) (h:∀z,discriminant (f dd) v z=(z-u)*(z-w))
      (z:PolynomialField K n) :
      discriminant (g (f dd)) (g v) z=(z-g u)*(z-g w) := by
    have h0:=h 0
    have h1:=h 1
    have hc:v^2-(f dd)^2=u*w := by simpa [discriminant] using h0
    have hl:2*f dd*v= -(u+w) := by
      simp only [discriminant] at h1
      linear_combination h1-hc
    have hcm:=congrArg g hc
    have hlm:=congrArg g hl
    simp only [map_sub,map_pow,map_mul,map_ofNat,map_neg,map_add] at hcm hlm
    unfold discriminant
    linear_combination hcm+z*hlm
  have hh:=scalarPolynomial_delete_roots (g.comp f) n dd rr hdd
    (g x) (g y) (g γ) (g σ) genericVar
    (generic_twoCons_inj x y hxy) (rootsMap x y γ hxroot) (rootsMap y x σ hyroot)
    (generic_twoCons_discriminant (f dd) x y (by simpa using f.injective.ne hdd))
  have hp:
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp f) (twoCons (MvPolynomial.C x) (MvPolynomial.C y) MvPolynomial.X)
          (scalarPolynomial (n+2) dd rr hdd)=
        (MvPolynomial.C x+MvPolynomial.C y+MvPolynomial.C (f rr)) *
          (∏i:Fin n,(MvPolynomial.X i-MvPolynomial.C γ)*(MvPolynomial.X i-MvPolynomial.C σ))*
          MvPolynomial.eval₂Hom (MvPolynomial.C.comp f) MvPolynomial.X (scalarPolynomial n dd rr hdd) := by
    apply IsFractionRing.injective (MvPolynomial (Fin n) K) (PolynomialField K n)
    simp only [MvPolynomial.map_eval₂Hom,map_mul,map_prod,map_sub,map_add] 
    convert hh using 1
    · apply congrArg (fun v:Fin (n+2) → PolynomialField K n =>
        MvPolynomial.eval₂Hom (g.comp f) v (scalarPolynomial (n+2) dd rr hdd))
      funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ i => induction i using Fin.cases <;> rfl
    · rfl
  have hh':=congrArg (MvPolynomial.eval a) hp
  simp only [MvPolynomial.map_eval₂Hom,map_mul,map_prod,map_sub,map_add,MvPolynomial.eval_X,
    MvPolynomial.eval_C] at hh'
  have hc: (MvPolynomial.eval a).comp (MvPolynomial.C.comp f)=f := by
    ext z; simp
  have hx:(fun i => (MvPolynomial.eval a)
      (twoCons (MvPolynomial.C x) (MvPolynomial.C y) MvPolynomial.X i))=twoCons x y a := by
    funext i
    induction i using Fin.cases with
    | zero => simp [twoCons]
    | succ i => induction i using Fin.cases <;> simp [twoCons]
  simpa only [hc,hx] using hh'







lemma scalarValue_extract {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (a:Fin (n+1) → K) (i:Fin (n+1)) :
    scalarValue f a=scalarValue f (Fin.cons (a i) (fun j => a (i.succAbove j))) := by
  have h:=scalarValue_permute f a i.cycleRange.symm
  rw [←h]
  congr 1
  funext j
  induction j using Fin.cases <;> simp

lemma scalarValue_swap_head {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y:K) (a:Fin n → K) :
    scalarValue f (Fin.cons x (Fin.cons y a))=scalarValue f (Fin.cons y (Fin.cons x a)) := by
  have h:=scalarValue_extract f (Fin.cons x (Fin.cons y a)) (1:Fin (n+2))
  apply h.trans
  congr 1
  funext j
  induction j using Fin.cases with
  | zero => rfl
  | succ j =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => simp [Fin.succAbove,Fin.lt_def]

lemma scalarValue_zero {K:Type*} [CommRing K] (f:ℂ →+* K) (a:Fin 0 → K) : scalarValue f a=1 := by
  have hp:=scalarNumerator_eq_vandermonde 0 (d:ℂ) rho (by exact_mod_cast d_ne_zero)
  have h0:scalarPolynomial 0 d rho (by exact_mod_cast d_ne_zero)=1 := by
    simp [scalarNumerator,sourceVandermonde,clearedPfaffian,clearedPfaffianTerm] at hp
    rw [Finset.prod_eq_one (fun e _ => Fin.elim0 e.val.1)] at hp
    exact hp.symm
  simp [scalarValue,h0]

lemma scalarValue_one {K:Type*} [CommRing K] (f:ℂ →+* K) (x:K) :
    scalarValue f (fun _:Fin 1 =>x)=1 := by
  let a:Fin 0 → K := Fin.elim0
  have h:=Polynomial.eq_C_of_natDegree_le_zero
    (scalarPolynomial_first_degree f 0 d rho (by exact_mod_cast d_ne_zero) a)
  rw [scalarPolynomial_first_top_continuation] at h
  change firstScalarHom f a _=Polynomial.C (scalarValue f a) at h
  rw [scalarValue_zero] at h
  have he:=congrArg (fun P:Polynomial K =>P.eval x) h
  rw [eval_firstScalarHom] at he
  convert he using 1
  · apply congrArg (scalarValue f)
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i
  · simp

lemma scalarValue_two {K:Type*} [CommRing K] (f:ℂ →+* K) (x y:K) :
    scalarValue f (Fin.cons x (fun _:Fin 1 =>y))=x+y+f (rho:ℂ) := by
  let a:Fin 1 → K := fun _ =>y
  let P:=firstScalarHom f a (scalarPolynomial 2 d rho (by exact_mod_cast d_ne_zero))
  have hp:P=Polynomial.X+Polynomial.C (P.coeff 0) := by
    have h:=Polynomial.eq_X_add_C_of_natDegree_le_one
      (scalarPolynomial_first_degree f 1 d rho (by exact_mod_cast d_ne_zero) a)
    rw [scalarPolynomial_first_top_continuation] at h
    change P=Polynomial.C (scalarValue f a)*Polynomial.X+Polynomial.C (P.coeff 0) at h
    rw [scalarValue_one] at h
    simpa using h
  have hf:=source_scalarPolynomial_flat f 1 a
  have hc:P.eval (f (c:ℂ))=y+f (C:ℂ) := by
    change (firstScalarHom f a _).eval _ = _
    rw [eval_firstScalarHom,hf]
    change _ * scalarValue f a=_
    rw [scalarValue_one]
    simp [a]
  rw [hp] at hc
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C] at hc
  have hconst:f (c:ℂ)+f (rho:ℂ)=f (C:ℂ) := by
    rw [←map_add]; congr 1; exact_mod_cast c_add_rho_eq_C
  have he:=congrArg (fun Q:Polynomial K =>Q.eval x) hp
  change (firstScalarHom f a _).eval x = _ at he
  rw [eval_firstScalarHom] at he
  change scalarValue f (Fin.cons x a)= _ at he
  rw [he]
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  linear_combination hc-hconst


 

 


lemma scalarValue_cons_extract {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (z:K) (a:Fin (n+1) → K) (i:Fin (n+1)) :
    scalarValue f (Fin.cons z a)=
      scalarValue f (Fin.cons z (Fin.cons (a i) (fun j =>a (i.succAbove j)))) := by
  have h:=scalarValue_extract f (Fin.cons z a) i.succ
  have hv:(fun j:Fin (n+1) => (Fin.cons z a : Fin (n+2) → K) (i.succ.succAbove j))=
      Fin.cons z (fun j =>a (i.succAbove j)) := by
    funext j
    induction j using Fin.cases <;> simp
  simp only [Fin.cons_succ,hv] at h
  exact h.trans (scalarValue_swap_head f (a i) z _)

lemma scalarValue_one_middle_extract {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (z x:K) (a:Fin (n+1) → K) (i:Fin (n+1)) :
    scalarValue f (Fin.cons z (Fin.cons x a))=
      scalarValue f (Fin.cons z (Fin.cons (a i) (Fin.cons x (fun j =>a (i.succAbove j))))) := by
  have h:=scalarValue_cons_extract f z (Fin.cons x a) i.succ
  have hv:(fun j:Fin (n+1) => (Fin.cons x a : Fin (n+2) → K) (i.succ.succAbove j))=
      Fin.cons x (fun j =>a (i.succAbove j)) := by
    funext j
    induction j using Fin.cases <;> simp
  simpa only [Fin.cons_succ,hv] using h

lemma scalarValue_two_middle_extract {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (z x y:K) (a:Fin (n+1) → K) (i:Fin (n+1)) :
    scalarValue f (Fin.cons z (Fin.cons x (Fin.cons y a)))=
      scalarValue f (Fin.cons z (Fin.cons (a i) (Fin.cons x (Fin.cons y (fun j =>a (i.succAbove j)))))) := by
  have h:=scalarValue_cons_extract f z (Fin.cons x (Fin.cons y a)) i.succ.succ
  have hv:(fun j:Fin (n+2) => (Fin.cons x (Fin.cons y a) : Fin (n+3) → K) (i.succ.succ.succAbove j))=
      Fin.cons x (Fin.cons y (fun j =>a (i.succAbove j))) := by
    funext j
    induction j using Fin.cases with
    | zero => simp
    | succ j => induction j using Fin.cases <;> simp
  simpa only [Fin.cons_succ,hv] using h

lemma scalarValue_delete {K:Type*} [Field K] [CharZero K] (f:ℂ →+* K) {n:ℕ}
    (x y γ σ:K) (hxy:x≠y)
    (hx:∀z,discriminant (f (d:ℂ)) x z=(z-y)*(z-γ))
    (hy:∀z,discriminant (f (d:ℂ)) y z=(z-x)*(z-σ)) (a:Fin n → K) :
    scalarValue f (Fin.cons x (Fin.cons y a))=
      (x+y+f (rho:ℂ))*(∏i,(a i-γ)*(a i-σ))*scalarValue f a := by
  exact scalarPolynomial_delete_continuation f n d rho _ x y γ σ hxy hx hy a

lemma scalarValue_flat {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ} (a:Fin n → K) :
    scalarValue f (Fin.cons (f (c:ℂ)) a)=(∏i,(a i+f (C:ℂ)))*scalarValue f a :=
  source_scalarPolynomial_flat f n a








lemma scalarMergeDiff_eval {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y t:K) (a:Fin n → K) (z:K) :
    (scalarMergeDiff f x y t a).eval z=
      scalarValue f (Fin.cons z (Fin.cons x (Fin.cons y a)))-
        (x+y+f (rho:ℂ))*(∏i,(a i+t))*(z+t)*scalarValue f (Fin.cons z (Fin.cons t a)) := by
  simp only [scalarMergeDiff,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_add,Polynomial.eval_X,eval_firstScalarHom,scalarValue]
  ring

lemma scalarMergeDiff_degree {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y t:K) (a:Fin n → K) : (scalarMergeDiff f x y t a).natDegree≤n+2 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact scalarPolynomial_first_degree f (n+2) d rho _ _
  · apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply (Polynomial.natDegree_mul_le).trans
    have hp:=scalarPolynomial_first_degree f (n+1) d rho (by exact_mod_cast d_ne_zero) (Fin.cons t a)
    change ((firstScalarHom f (Fin.cons t a)) (scalarPolynomial (n+2) d rho _)).natDegree≤n+1 at hp
    have hl:(Polynomial.X+Polynomial.C t).natDegree≤1:=
      (Polynomial.natDegree_add_le _ _).trans (max_le Polynomial.natDegree_X_le (by simp))
    omega

lemma scalarMergeDiff_top {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y t:K) (a:Fin n → K)
    (h:scalarValue f (Fin.cons x (Fin.cons y a))=
      (x+y+f (rho:ℂ))*(∏i,(a i+t))*scalarValue f (Fin.cons t a)) :
    (scalarMergeDiff f x y t a).coeff (n+2)=0 := by
  unfold scalarMergeDiff
  rw [Polynomial.coeff_sub,Polynomial.coeff_C_mul,add_mul (Polynomial.X) (Polynomial.C t),Polynomial.coeff_add,
    Polynomial.coeff_X_mul,Polynomial.coeff_C_mul]
  rw [scalarPolynomial_first_top_continuation,scalarPolynomial_first_top_continuation]
  have hp:=scalarPolynomial_first_degree f (n+1) d rho (by exact_mod_cast d_ne_zero) (Fin.cons t a)
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by omega)),mul_zero,add_zero]
  exact sub_eq_zero.mpr h

lemma scalarMergeDiff_degree_reduced {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y t:K) (a:Fin n → K)
    (h:scalarValue f (Fin.cons x (Fin.cons y a))=
      (x+y+f (rho:ℂ))*(∏i,(a i+t))*scalarValue f (Fin.cons t a)) :
    (scalarMergeDiff f x y t a).natDegree≤n+1 := by
  simpa using Polynomial.natDegree_le_pred (scalarMergeDiff_degree f x y t a)
    (scalarMergeDiff_top f x y t a h)

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarMergeTrig
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section






open scoped Classical

lemma scalarValue_fcos_delete {m n:ℕ} (i:Fin m) (k:ℤ) (a:Fin n → SpectralField m) :
    scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i k) (Fin.cons (fcos i (k+6)) a))=
      (fcos i k+fcos i (k+6)+constF m rho)*
        (∏j,(a j-fcos i (k-6))*(a j-fcos i (k+12)))*
        scalarValue (algebraMap ℂ (SpectralField m)) a := by
  apply scalarValue_delete _ _ _ _ _ (fcos_six_ne i k)
  · intro z
    change discriminant (constF m d) (fcos i k) z=_
    rw [fcos_roots,mul_comm]
  · intro z; simpa only [constF,add_sub_cancel_right,show k+6+6=k+12 by omega] using fcos_roots i (k+6) z

lemma scalarMergeDiff_eval_neg {m n:ℕ} (i:Fin m) (k:ℤ) (a:Fin n → SpectralField m) :
    (scalarMergeDiff (algebraMap ℂ (SpectralField m)) (fcos i (k-2)) (fcos i (k+2)) (fcos i k) a).eval (-fcos i k)=0 := by
  rw [scalarMergeDiff_eval,neg_add_cancel,mul_zero,zero_mul,sub_zero]
  rw [←fcos_sub_eight]
  have hh:=scalarValue_fcos_delete i (k-8) (Fin.cons (fcos i (k+2)) a)
  have hp:fcos i (k-8-6)=fcos i (k+2) := by
    rw [←fcos_sixteen i (k-8-6)]
    congr 1; omega
  simp only [show k-8+6=k-2 by omega,hp,Fin.prod_univ_succ,Fin.cons_zero,
    Fin.cons_succ,sub_self,zero_mul,mul_zero] at hh
  exact hh

lemma scalarMergeDiff_eval_flat {m n:ℕ} (i:Fin m) (k:ℤ) (a:Fin n → SpectralField m)
    (h:scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i (k-2)) (Fin.cons (fcos i (k+2)) a))=
      (fcos i (k-2)+fcos i (k+2)+constF m rho)*(∏j,(a j+fcos i k))*
        scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i k) a)) :
    (scalarMergeDiff (algebraMap ℂ (SpectralField m)) (fcos i (k-2)) (fcos i (k+2)) (fcos i k) a).eval (constF m c)=0 := by
  rw [scalarMergeDiff_eval]
  simp only [constF] at h ⊢
  rw [scalarValue_flat,scalarValue_flat,h]
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  have he:=fcos_flat_factor i k
  change (constF m C+fcos i (k-2))*(constF m C+fcos i (k+2))=_ at he
  have hring:
      (fcos i (k-2) + (algebraMap ℂ (SpectralField m)) (C:ℂ)) *
        ((fcos i (k+2) + (algebraMap ℂ (SpectralField m)) (C:ℂ)) * (∏j,(a j+(algebraMap ℂ (SpectralField m)) (C:ℂ))))=
      (constF m c+fcos i k)*(fcos i k+constF m C)*(∏j,(a j+constF m C)) := by
    calc
      _ = ((constF m C+fcos i (k-2))*(constF m C+fcos i (k+2)))*(∏j,(a j+constF m C)) := by dsimp only [constF]; ring
      _ = _ := by rw [he]; ring
  rw [hring]
  dsimp only [constF]
  ring

lemma scalarMergeDiff_eval_deletion {m n:ℕ} (i:Fin m) (k:ℤ)
    (a:Fin (n+1) → SpectralField m) (j:Fin (n+1)) (g:Fin m) (l:ℤ)
    (ha:a j=fcos g l)
    (h:scalarValue (algebraMap ℂ (SpectralField m))
        (Fin.cons (fcos i (k-2)) (Fin.cons (fcos i (k+2)) (fun v =>a (j.succAbove v))))=
      (fcos i (k-2)+fcos i (k+2)+constF m rho)*(∏v,(a (j.succAbove v)+fcos i k))*
        scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i k) (fun v =>a (j.succAbove v)))) :
    (scalarMergeDiff (algebraMap ℂ (SpectralField m)) (fcos i (k-2)) (fcos i (k+2)) (fcos i k) a).eval (fcos g (l+6))=0 := by
  rw [scalarMergeDiff_eval,scalarValue_two_middle_extract _ _ _ _ a j,
    scalarValue_one_middle_extract _ _ _ a j,ha,
    scalarValue_swap_head _ (fcos g (l+6)) (fcos g l),
    scalarValue_swap_head _ (fcos g (l+6)) (fcos g l),
    scalarValue_fcos_delete,scalarValue_fcos_delete,h]
  rw [Fin.prod_univ_succAbove (fun v =>a v+fcos i k) j,ha]
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  have he:=fcos_delete_factor i g k l
  
  have hp:
      (fcos i (k-2)-fcos g (l-6))*(fcos i (k-2)-fcos g (l+12))*
        ((fcos i (k+2)-fcos g (l-6))*(fcos i (k+2)-fcos g (l+12))*
        (∏v,(a (j.succAbove v)-fcos g (l-6))*(a (j.succAbove v)-fcos g (l+12))))=
      ((fcos i k+fcos g l)*(fcos i k+fcos g (l+6))*
        (fcos i k-fcos g (l-6))*(fcos i k-fcos g (l+12)))*
        (∏v,(a (j.succAbove v)-fcos g (l-6))*(a (j.succAbove v)-fcos g (l+12))) := by
    rw [←he]; ring
  rw [hp]
  dsimp only [constF]
  ring

end

 

 

noncomputable section






open scoped Classical

lemma scalarValue_rotate3 {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y z:K) (a:Fin n → K) :
    scalarValue f (Fin.cons x (Fin.cons y (Fin.cons z a)))=
      scalarValue f (Fin.cons z (Fin.cons x (Fin.cons y a))) := by
  rw [scalarValue_cons_extract f x (Fin.cons y (Fin.cons z a)) (1:Fin (n+2))]
  have hv:(fun j:Fin (n+1) =>(Fin.cons y (Fin.cons z a):Fin (n+2) → K) ((1:Fin (n+2)).succAbove j))=Fin.cons y a := by
    funext j
    induction j using Fin.cases with
    | zero => rfl
    | succ j => simp [Fin.succAbove,Fin.lt_def]
  rw [hv]
  simpa only [show (1:Fin (n+2))=(0:Fin (n+1)).succ from rfl,Fin.cons_succ,Fin.cons_zero] using scalarValue_swap_head f x z (Fin.cons y a)


end

 

 

noncomputable section
open scoped Classical

lemma rationalAt_scalarValue {m n r:ℕ} (φ:Laurent m →ₐ[ℂ] SpectralField n)
    (a:Fin r → SpectralField m) (b:Fin r → SpectralField n)
    (ha:∀j,RationalAt φ.toRingHom (a j) (b j)) :
    RationalAt φ.toRingHom (scalarValue (algebraMap ℂ (SpectralField m)) a)
      (scalarValue (algebraMap ℂ (SpectralField n)) b) :=
  RationalAt.mv_eval _ _ a b (rationalAt_const φ) ha _



lemma lastLaurent_regular_value {n m:ℕ} (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,evalLaurent (lastLaurent p (P p))=rationalVacuum (n+1) p)
    (z:Fin n → SpectralField m) (hz:∀i,z i≠0) (y:SpectralField m) (hy:y≠0)
    (hL:∀i,torusL (constF m phase^3/(Fin.snoc z y : Fin (n+1) → SpectralField m) i)≠0)
    (hreg:VacuumRegular (fun i =>torusWeights (constF m phase^3/(Fin.snoc z y : Fin (n+1) → SpectralField m) i)))
    (p:Pairing (n+1)) :
    (if p.Occupied (Fin.last n) then torusSin y else 1)*
      ((P p).map (torusEvaluation z hz).toRingHom).eval (torusCos (y^2/constF m phase^3))=
      scalarValue (algebraMap ℂ (SpectralField m)) (fun i =>torusCos (((Fin.snoc z y : Fin (n+1) → SpectralField m) i)^2/constF m phase^3))*
        normalizedVacuum (fun i =>torusWeights (constF m phase^3/(Fin.snoc z y : Fin (n+1) → SpectralField m) i)) p := by
  let x:Fin (n+1) → SpectralField m:=Fin.snoc z y
  have hx:∀i:Fin (n+1),x i≠0:=fun i =>Fin.lastCases (by simpa [x] using hy) (fun j =>by simpa [x] using hz j) i
  let φ:=torusEvaluation x hx
  have hv:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField (n+1)) (lastLaurent p (P p))
  change RationalAt _ (evalLaurent (lastLaurent p (P p))) _ at hv
  rw [hP p] at hv
  have hs:RationalAt φ.toRingHom (spectralNormalization (n+1))
      (scalarValue (algebraMap ℂ (SpectralField m)) (fun i =>torusCos ((x i)^2/constF m phase^3))) := by
    rw [←scalarPolynomial_eval_spectral]
    apply rationalAt_scalarValue
    intro i
    exact rationalAt_torusCos φ (((rationalAt_variable x hx i).pow 2).div
      ((rationalAt_const φ phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero m)))
      (div_ne_zero (pow_ne_zero _ (hx i)) (pow_ne_zero _ (constF_phase_ne_zero m)))
  have hw (i:Fin (n+1)) (t:Tile):RationalAt φ.toRingHom ((spectralWeights (n+1) i).tile t)
      ((torusWeights (constF m phase^3/x i)).tile t) := by
    apply rationalAt_torusWeights
    · exact ((rationalAt_const φ phase).pow 3).div (rationalAt_variable x hx i) (hx i)
    · exact div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero m)) (hx i)
    · exact hL i
  have hn:=rationalAt_normalizedVacuum _ _ hw hreg p
  have he:=hv.unique (hs.mul hn)
  dsimp only [φ,x] at he
  change torusEvaluation _ _ (lastLaurent p (P p))=_ at he
  rw [torusEvaluation_lastLaurent z hz y hy] at he
  exact he


 

 


lemma rationalAt_torusVacuum {n m:ℕ} (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (hL:∀i,torusL (constF m phase^3/z i)≠0)
    (hreg:VacuumRegular (fun i =>torusWeights (constF m phase^3/z i)))
    (p:Pairing n) :
    RationalAt (torusEvaluation z hz).toRingHom (rationalVacuum n p)
      (scalarValue (algebraMap ℂ (SpectralField m)) (fun i =>torusCos ((z i)^2/constF m phase^3))*
        normalizedVacuum (fun i =>torusWeights (constF m phase^3/z i)) p) := by
  let φ:=torusEvaluation z hz
  have hs:RationalAt φ.toRingHom (spectralNormalization n)
      (scalarValue (algebraMap ℂ (SpectralField m)) (fun i =>torusCos ((z i)^2/constF m phase^3))) := by
    rw [←scalarPolynomial_eval_spectral]
    apply rationalAt_scalarValue
    intro i
    exact rationalAt_torusCos φ (((rationalAt_variable z hz i).pow 2).div
      ((rationalAt_const φ phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero m)))
      (div_ne_zero (pow_ne_zero _ (hz i)) (pow_ne_zero _ (constF_phase_ne_zero m)))
  have hw (i:Fin n) (t:Tile):RationalAt φ.toRingHom ((spectralWeights n i).tile t)
      ((torusWeights (constF m phase^3/z i)).tile t) := by
    apply rationalAt_torusWeights
    · exact ((rationalAt_const φ phase).pow 3).div (rationalAt_variable z hz i) (hz i)
    · exact div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero m)) (hz i)
    · exact hL i
  exact hs.mul (rationalAt_normalizedVacuum _ _ hw hreg p)

lemma torusEvaluation_vacuum {n m:ℕ} (W:Pairing n → Laurent n)
    (hW:∀p,evalLaurent (W p)=rationalVacuum n p)
    (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (hL:∀i,torusL (constF m phase^3/z i)≠0)
    (hreg:VacuumRegular (fun i =>torusWeights (constF m phase^3/z i)))
    (p:Pairing n) :
    torusEvaluation z hz (W p)=
      scalarValue (algebraMap ℂ (SpectralField m)) (fun i =>torusCos ((z i)^2/constF m phase^3))*
        normalizedVacuum (fun i =>torusWeights (constF m phase^3/z i)) p := by
  have h:=RationalAt.algebraMap (φ:=(torusEvaluation z hz).toRingHom) (F:=SpectralField n) (W p)
  change RationalAt _ (evalLaurent (W p)) _ at h
  rw [hW] at h
  exact h.unique (rationalAt_torusVacuum z hz hL hreg p)

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PairSelfNode
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma pairEarlier_L {n s:ℕ} (hs:s≤3) (i:Fin (n+2)) :
    torusL (constF (n+1) phase^3/pairPoint n s i)≠0 := by
  rw [pairArgument hs i]
  exact torusL_phaseRow_ne_zero _ _ (pairExponent_le n s i)

lemma rationalAt_pair_nodalWeights {n s:ℕ} (hs:s≤3) (i:Fin (n+2)) (hi:i≠1)
    (j:Fin (n+3)) (t:Tile) :
    RationalAt (pairEvaluation n s).toRingHom ((nodalWeights i j).tile t) ((pairNodeWeights n s i j).tile t) := by
  induction j using Fin.lastCases with
  | cast j =>
    simp only [nodalWeights,Fin.snoc_castSucc,spectralWeights,pairNodeWeights,pairEarlierWeights]
    rw [←pairArgument hs j]
    exact rationalAt_torusWeights _
      (((rationalAt_const (pairEvaluation n s) phase).pow 3).div (rationalAt_pair_variable s j) (pairPoint_ne_zero n s j))
      (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) (pairPoint_ne_zero n s j)) (pairEarlier_L hs j) t
  | last =>
    simp only [nodalWeights_last,pairNodeWeights,Fin.snoc_last]
    have hv:=rationalAt_pair_variable s i
    rw [pairPoint_of_ne i hi] at hv
    exact rationalAt_torusWeights _ (hv.inv (variableF_ne_zero _))
      (inv_ne_zero (variableF_ne_zero _))
      (by simpa only [pow_zero,one_div] using torusL_phaseRow_ne_zero (pairIndex n i) 0 (by omega)) t







lemma rationalAt_pair_nodalScalar {n:ℕ} (s:ℕ) (i:Fin (n+2)) :
    RationalAt (pairEvaluation n s).toRingHom (nodalScalar i)
      (scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.snoc (pairCosines n s) (pairBeta n s i))) := by
  apply rationalAt_scalarValue
  intro j
  induction j using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using rationalAt_pair_deletionBeta s i
  | cast j => simpa only [Fin.snoc_castSucc] using rationalAt_pair_spectralA s j

lemma deletePoint_node_L {n:ℕ} (i:Fin (n+1)) (j:Fin (n+1)) :
    torusL (constF (n+1) phase^3/
      (Fin.snoc (deletePoint n) (deletionNode i) : Fin (n+1) → SpectralField (n+1)) j)≠0 := by
  induction j using Fin.lastCases with
  | last =>
      rw [Fin.snoc_last]
      have he:constF (n+1) phase^3/deletionNode i=(variableF i)⁻¹ := by
        rw [deletionNode]; field_simp [constF_phase_ne_zero,variableF_ne_zero]
      rw [he]
      simpa using torusL_phaseRow_ne_zero i 0 (by omega)
  | cast j => simpa only [Fin.snoc_castSucc,deletePoint] using torusL_phaseRow_ne_zero j.succ 3 (by omega)







lemma scalar_pair_delete (n:ℕ) :
    scalarValue (algebraMap ℂ (SpectralField (n+1))) (pairCosines n 3)=
      deletePairScalar n*scalarValue (algebraMap ℂ (SpectralField (n+1))) (fun j:Fin n =>fcos j.succ (-3)) := by
  exact scalarValue_fcos_delete 0 (-3) (fun j:Fin n =>fcos j.succ (-3))

lemma scalar_pair_delete_snoc {n:ℕ} (b:SpectralField (n+1)) :
    scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.snoc (pairCosines n 3) b)=
      deletePairScalar n*((b-fcos 0 (-9))*(b-fcos 0 9))*
        scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.snoc (fun j:Fin n =>fcos j.succ (-3)) b) := by
  have he:=scalarValue_fcos_delete (0:Fin (n+1)) (-3)
    (Fin.snoc (fun j:Fin n =>fcos j.succ (-3)) b)
  unfold pairCosines
  rw [Fin.snoc_twoCons]
  norm_num only at he ⊢
  rw [he]
  simp only [Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
  dsimp only [deletePairScalar]
  ring







lemma mergeMap_last {n m:ℕ} (r:ℕ) (hr:r+2≤n+1) :
    LastMatrix (mergeMap (m:=m) r (show r+2≤n+2 by omega)) := by
  let j:Fin (n+1):=⟨r+1,by omega⟩
  change LastMatrix (localR (PartialColumn.rowPosition r hr).padTop (mergeWeights (constF m phase)) *
    functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb j.castSucc)))
  exact (LastMatrix.local _ _).mul (LastMatrix.omit j)

lemma mergeMap_padTop {n m:ℕ} (r:ℕ) (hr:r+2≤n+1) (p:Pairing (n+1)) (q:Pairing n) :
    mergeMap (m:=m) r (show r+2≤n+2 by omega) p.padTop q.padTop=mergeMap r hr p q := by
  let j:Fin (n+1):=⟨r+1,by omega⟩
  calc
    _ = localR (PartialColumn.rowPosition r hr).padTop (mergeWeights (constF m phase)) p.padTop
        (q.padTop.map (Fin.succAboveOrderEmb j.castSucc)) := mul_functionMatrix _ _ _ _
    _ = localR (PartialColumn.rowPosition r hr) (mergeWeights (constF m phase)) p
        (q.map (Fin.succAboveOrderEmb j)) := by
      rw [←Pairing.omit_padTop,localR_padTop]
    _ = _ := (mul_functionMatrix _ _ _ _).symm

lemma deletionMap_last {n m:ℕ} (r:ℕ) (hr:r+2≤n+2) :
    LastMatrix (deletionMap (m:=m) r (show r+2≤n+3 by omega)) := by
  let j:Fin (n+2):=⟨r+1,by omega⟩
  let k:Fin (n+1):=⟨r,by omega⟩
  change LastMatrix ((localR (PartialColumn.rowPosition r hr).padTop (deletionWeights : Weights (SpectralField m))) *
    ((functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb j.castSucc))) *
      (functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb k.castSucc)))))
  exact (LastMatrix.local _ _).mul ((LastMatrix.omit j).mul (LastMatrix.omit k))

lemma deletionMap_padTop {n m:ℕ} (r:ℕ) (hr:r+2≤n+2) (p:Pairing (n+2)) (q:Pairing n) :
    deletionMap (m:=m) r (show r+2≤n+3 by omega) p.padTop q.padTop=deletionMap r hr p q := by
  let j:Fin (n+2):=⟨r+1,by omega⟩
  let k:Fin (n+1):=⟨r,by omega⟩
  let B : Matrix (Pairing (n+3)) (Pairing (n+2)) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb j.castSucc))
  let D : Matrix (Pairing (n+2)) (Pairing (n+1)) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb k.castSucc))
  let B' : Matrix (Pairing (n+2)) (Pairing (n+1)) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb j))
  let D' : Matrix (Pairing (n+1)) (Pairing n) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb k))
  change (localR (PartialColumn.rowPosition r hr).padTop (deletionWeights : Weights (SpectralField m)) * (B*D)) p.padTop q.padTop =
    (localR (PartialColumn.rowPosition r hr) (deletionWeights : Weights (SpectralField m)) * (B'*D')) p q
  rw [←Matrix.mul_assoc,←Matrix.mul_assoc]
  dsimp only [B,D,B',D']
  rw [mul_functionMatrix,mul_functionMatrix,mul_functionMatrix,mul_functionMatrix]
  change localR (PartialColumn.rowPosition r hr).padTop (deletionWeights : Weights (SpectralField m)) p.padTop
    ((q.padTop.map (Fin.succAboveOrderEmb k.castSucc)).map (Fin.succAboveOrderEmb j.castSucc))=_
  rw [←Pairing.omit_padTop,←Pairing.omit_padTop,localR_padTop]



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalTorusValue
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma mappedNodal_leading {n m:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (hL:∀i,torusL (constF m phase^3/z i)≠0)
    (hreg:VacuumRegular (fun i =>torusWeights (constF m phase^3/z i)))
    (p:Pairing n) :
    ((P p.padTop).map (torusEvaluation z hz).toRingHom).coeff n=
      scalarValue (algebraMap ℂ (SpectralField m)) (fun i =>torusCos ((z i)^2/constF m phase^3))*
        normalizedVacuum (fun i =>torusWeights (constF m phase^3/z i)) p := by
  rw [Polynomial.coeff_map]
  have h:=RationalAt.algebraMap (φ:=(torusEvaluation z hz).toRingHom)
    (F:=SpectralField n) ((P p.padTop).coeff n)
  have he:=congrArg (fun Q:Polynomial (SpectralField n) =>Q.coeff n) (hP p.padTop)
  rw [Polynomial.coeff_map,rationalNodalPolynomial_leading] at he
  rw [he] at h
  exact h.unique (rationalAt_torusVacuum z hz hL hreg p)

lemma mappedNodal_degree {n m:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (φ:Laurent n →+* SpectralField m) : LastDegree n (fun p =>(P p).map φ) := by
  exact (LastDegree.of_map (algebraMap (SpectralRing n) (SpectralField n)) (IsFractionRing.injective _ _)
    (by simpa only [hP] using rationalNodalPolynomial_degree n)).map φ

lemma mergeZ_L (n:ℕ) : torusL (mergeZ n)≠0 := by
  simpa only [mergeZ,pow_one] using torusL_phaseRow_ne_zero (0:Fin (n+1)) 1 (by omega)
lemma mergeZ_one_L (n:ℕ) : torusL (constF (n+1) phase*mergeZ n)≠0 := by
  have he:constF (n+1) phase*mergeZ n=constF (n+1) phase^2/variableF 0 := by unfold mergeZ; ring
  rw [he]; exact torusL_phaseRow_ne_zero _ _ (by omega)
lemma mergeZ_two_L (n:ℕ) : torusL (constF (n+1) phase^2*mergeZ n)≠0 := by
  have he:constF (n+1) phase^2*mergeZ n=constF (n+1) phase^3/variableF 0 := by unfold mergeZ; ring
  rw [he]; exact torusL_phaseRow_ne_zero _ _ (by omega)

lemma mergePoint_L (n:ℕ) (i:Fin (n+1)) : torusL (constF (n+1) phase^3/mergePoint n i)≠0 := by
  rw [mergePoint_argument]
  exact torusL_phaseRow_ne_zero i _ (mergeExponent_le n i)

lemma mergePoint_node_L {n:ℕ} (i:Fin (n+1)) (j:Fin (n+2)) :
    torusL (constF (n+1) phase^3/
      (Fin.snoc (mergePoint n) (deletionNode i) : Fin (n+2) → SpectralField (n+1)) j)≠0 := by
  induction j using Fin.lastCases with
  | last =>
      rw [Fin.snoc_last]
      have he:constF (n+1) phase^3/deletionNode i=(variableF i)⁻¹ := by
        rw [deletionNode]; field_simp [constF_phase_ne_zero,variableF_ne_zero]
      rw [he]
      simpa using torusL_phaseRow_ne_zero i 0 (by omega)
  | cast j => simpa only [Fin.snoc_castSucc] using mergePoint_L n j







end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MergePairCandidate
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical



lemma lastValue_firstZero_spectral (n:ℕ) :
    lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
      (firstZeroPolynomial (fun i =>(spectralWeights n i).tile) (constF n d) (constF n c)
        (constF n C) (rationalNodalPolynomial n))=
      (spectralA (Fin.last n)+constF (n+1) C) •
        firstZeroRaw (fun i =>(spectralWeights (n+1) i).tile) (rationalInterpolant n) := by
  let z:SpectralField (n+1):=variableF (Fin.last n)
  have hL:torusL (constF (n+1) phase^3/z)≠0 := by
    rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero _
  have ht:=torus_last_cleared z (variableF_ne_zero _) hL
  have h:=firstZeroPolynomial_evaluation (liftSpectral n) (fun i =>(spectralWeights n i).tile)
    (constF n d) (constF n c) (constF n C)
    (spectralA (Fin.last n)) (torusSin z) (torusSin (constF (n+1) phase^3/z))
    (fun t =>(spectralA (Fin.last n)+constF (n+1) C)*(spectralWeights (n+1) (Fin.last n)).tile t)
    (rationalNodalPolynomial n)
    (by simpa only [liftSpectral_const,z,spectralA,spectralWeights] using ht.1)
    (by simpa only [liftSpectral_const,z,spectralA,spectralWeights] using ht.2.1)
    (by simpa only [liftSpectral_const,z,spectralA,spectralWeights] using ht.2.2.1)
    (by simpa only [liftSpectral_const,z,spectralA,spectralWeights] using ht.2.2.2)
    (by simpa only [liftSpectral_const,z,spectralA,spectralWeights] using torus_sine_pair z (variableF_ne_zero _))
  rw [lastValue_spectral] at h
  have he:Fin.snoc (fun i t =>liftSpectral n ((spectralWeights n i).tile t))
      (fun t =>(spectralA (Fin.last n)+constF (n+1) C)*(spectralWeights (n+1) (Fin.last n)).tile t)=
      fun i t =>(Fin.snoc (fun _ =>1) (spectralA (Fin.last n)+constF (n+1) C):Fin (n+1) → SpectralField (n+1)) i *
        (spectralWeights (n+1) i).tile t := by
    funext i t
    induction i using Fin.lastCases <;> simp only [Fin.snoc_last,Fin.snoc_castSucc,
      liftSpectral_weights_tile,one_mul]
  rw [he,firstZeroRaw_rowScale] at h
  simpa only [Fin.prod_univ_castSucc,Fin.snoc_last,Fin.snoc_castSucc,Finset.prod_const_one,one_mul] using h.symm

end





noncomputable section
open scoped Classical LaurentPolynomial



lemma fullPeel_injective {n:ℕ} (i:Fin (n+1)) : Function.Injective (fullPeel i) :=
  (AddMonoidAlgebra.map_injective _ (insertSpectral i).injective).comp (peelLaurent_injective i)

lemma fullPeel_monomial {n:ℕ} (i:Fin (n+1)) (e:Fin (n+1) → ℤ) (c:ℂ) :
    fullPeel i (monomialL e c)=AddMonoidAlgebra.single (e i)
      (evalLaurent (monomialL (Function.update e i 0) c)) := by
  change AddMonoidAlgebra.mapRingHom ℤ (insertSpectral i) (peelLaurent i (monomialL e c))=_
  rw [peelLaurent_monomial,AddMonoidAlgebra.mapRingHom_single,insertSpectral_evalLaurent,insertLaurent_monomial]
  congr 3
  simp [Fin.insertNth_removeNth]

lemma fullPeel_eval {n:ℕ} (i:Fin (n+1)) (z:SpectralField (n+1)) (hz:z≠0) (f:Laurent (n+1)) :
    LaurentPolynomial.eval₂ (RingHom.id _) (Units.mk0 z hz) (fullPeel i f)=
      torusEvaluation (Function.update variableF i z)
        (fun j =>by by_cases h:j=i <;> simp [h,hz,variableF_ne_zero]) f := by
  let ψ:=torusEvaluation (Function.update variableF i z)
        (fun j =>by by_cases h:j=i <;> simp [h,hz,variableF_ne_zero])
  have he:(LaurentPolynomial.eval₂ (RingHom.id _) (Units.mk0 z hz)).comp (fullPeel i)=ψ.toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change LaurentPolynomial.eval₂ _ _ (fullPeel i (monomialL _ _))=ψ (monomialL _ _)
    all_goals rw [fullPeel_monomial, LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T]
    all_goals simp only [RingHom.id_apply,Units.val_zpow_eq_zpow_val,Units.val_mk0]
    all_goals rw [evalLaurent_monomial_full,torusEvaluation_monomial]
    all_goals rw [Fin.prod_univ_succAbove _ i,Fin.prod_univ_succAbove _ i]
    all_goals simp only [Function.update_self,Function.update_of_ne (Fin.succAbove_ne _ _),zpow_zero,one_mul]
    all_goals ring
  exact DFunLike.congr_fun he f

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ResidualParityCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical

lemma pair_update_regular {n:ℕ} (i j:Fin n) (_hij:i≠j) (c:ℂ) (hc:c≠0) :
    PairExchangeRegular (Function.update variableF i.castSucc (constF (n+1) c*variableF j.castSucc)) i j := by
  let E:Fin n → Fin (n+1) → ℤ:=fun a =>if a=i then variableExponent j.castSucc else variableExponent a.castSucc
  let C:Fin n → ℂ:=fun a =>if a=i then c else 1
  have he (a:Fin n):(Function.update variableF i.castSucc (constF (n+1) c*variableF j.castSucc)) a.castSucc=
      evalLaurent (monomialL (E a) (C a)) := by
    by_cases ha:a=i
    · subst a; simp only [Function.update_self,E,C,ite_true]
      change constF (n+1) c*evalLaurent (monomialL (variableExponent j.castSucc) 1)=_
      simpa using constF_mul_monomial c 1 (variableExponent j.castSucc)
    · simp only [Function.update_of_ne (fun h =>ha (Fin.castSucc_injective n h)),E,C,ite_eq_right ha]
      rfl
  have hC (a:Fin n):C a≠0 := by dsimp [C]; split_ifs <;> simp_all
  intro a b hab hpair
  rw [he,he]
  apply monomial_ratio_regular _ _ _ _ _ (hC b) (hC a)
  intro h
  by_cases hai:a=i <;> by_cases hbi:b=i
  · exact hab (hai.trans hbi.symm)
  · have hh: b=j := Fin.castSucc_injective n (variableExponent_injective (by simpa [E,hai,hbi] using h))
    exact hpair (Or.inl ⟨hai,hh⟩)
  · have hh: a=j := Fin.castSucc_injective n (variableExponent_injective (by simpa [E,hai,hbi] using h.symm))
    exact hpair (Or.inr ⟨hh,hbi⟩)
  · exact hab (Fin.castSucc_injective n (variableExponent_injective (by simpa [E,hai,hbi] using h.symm)))







end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalEmpty
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical








structure VacuumPolynomialData (n:ℕ) where
  P : Pairing (n+1) → Polynomial (Laurent n)
  map_P : ∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p
  box_P : ∀p,PolynomialBox (P p) (fun _ =>2*n)
  eval_P : ∀p,evalLaurent (lastLaurent p (P p))=rationalVacuum (n+1) p

namespace VacuumPolynomialData
variable {n:ℕ} (D:VacuumPolynomialData n)
def W : Pairing (n+1) → Laurent (n+1) := fun p =>lastLaurent p (D.P p)
lemma degree : LastDegree n D.P :=
  LastDegree.of_map _ (IsFractionRing.injective (SpectralRing n) (SpectralField n))
    (by simpa only [D.map_P] using rationalNodalPolynomial_degree n)
lemma box (p:Pairing (n+1)) : LaurentBox (D.W p) (fun _ =>2*n) :=
  lastLaurent_box p (D.P p) (D.box_P p) (D.degree p)
include D in
lemma interpolant : ∀p,rationalInterpolant n p=rationalVacuum (n+1) p := by
  intro p
  rw [←lastLaurent_map p (D.P p) (D.map_P p)]
  exact D.eval_P p
end VacuumPolynomialData

lemma spectralNormalization_zero : spectralNormalization 0=1 := by
  rw [←scalarPolynomial_eval_spectral]
  exact scalarValue_zero _ _
lemma rationalVacuum_zero (p:Pairing 0) : rationalVacuum 0 p=1 := by
  have hp:p=empty 0 := (p.eq_empty_iff).mpr (fun i =>Fin.elim0 i)
  rw [hp,rationalVacuum_empty,spectralNormalization_zero]
lemma rationalVacuum_one (p:Pairing 1) : rationalVacuum 1 p=1 := by
  rw [p.one_eq_empty,rationalVacuum_empty,←scalarPolynomial_eval_spectral]
  convert scalarValue_one (algebraMap ℂ (SpectralField 1)) (spectralA 0) using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  funext i
  congr 1
  exact Subsingleton.elim _ _

lemma rationalNodalPolynomial_zero (p:Pairing 1) : rationalNodalPolynomial 0 p=1 := by
  rw [p.one_eq_empty]
  simp [rationalNodalPolynomial,rationalVacuum_zero,Lagrange.nodal,Lagrange.interpolate]

noncomputable def vacuumData_zero : VacuumPolynomialData 0 where
  P := fun _ =>1
  map_P := fun p =>by rw [Polynomial.map_one,rationalNodalPolynomial_zero]
  box_P := fun p =>by
    convert (PolynomialBox.one (n:=0)) using 1
    all_goals try with_reducible_and_instances rfl
  eval_P := fun p =>by
    rw [rationalVacuum_one]
    simp [lastLaurent,p.one_eq_empty,evalLaurent]









lemma deletionMap_map {n m k:ℕ} (f:SpectralField m →+* SpectralField k) (r:ℕ) (hr:r+2≤n+2) :
    (deletionMap (m:=m) r hr).map f=deletionMap (m:=k) r hr := by
  let E₁ : Matrix (Pairing (n+2)) (Pairing (n+1)) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r+1,by omega⟩))
  let E₀ : Matrix (Pairing (n+1)) (Pairing n) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r,by omega⟩))
  let S := localR (PartialColumn.rowPosition r hr) (deletionWeights : Weights (SpectralField m))
  have hw:(deletionWeights:Weights (SpectralField m)).map f=deletionWeights := by simp [Weights.map,deletionWeights]
  calc
    _ = S.map f * (E₁*E₀).map f := Matrix.map_mul
    _ = S.map f * (E₁.map f*E₀.map f) :=
      congrArg (fun M => S.map f * M) (Matrix.map_mul (L := E₁) (M := E₀) (f := f))
    _ = _ := by
      dsimp only [S,E₁,E₀]
      rw [localR_map_hom,functionMatrix_map_hom,functionMatrix_map_hom,hw]
      rfl

lemma mergeMap_lift {n m:ℕ} (r:ℕ) (hr:r+2≤n+1) :
    (mergeMap (m:=m) r hr).map (liftSpectral m)=mergeMap (m:=m+1) r hr := by
  let E : Matrix (Pairing (n+1)) (Pairing n) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r+1,by omega⟩))
  let S := localR (PartialColumn.rowPosition r hr) (mergeWeights (constF m phase))
  have hw:(mergeWeights (constF m phase)).map (liftSpectral m)=mergeWeights (constF (m+1) phase) := by
    simp [Weights.map,mergeWeights,map_div₀,liftSpectral_const]
  calc
    _ = S.map (liftSpectral m) * E.map (liftSpectral m) := Matrix.map_mul
    _ = _ := by
      dsimp only [S,E]
      rw [localR_map_hom,functionMatrix_map_hom,hw]
      rfl

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumDegree
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram




noncomputable section
open scoped BigOperators Classical



def northSource {K : Type*} [CommRing K] {n : ℕ} (w : Fin n → Tile → K) :
    Matrix (SourcePairing n) (Pairing n) K :=
  fun q p => lastCoefficient w q.val p.padTop

end




end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SplitGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

@[simp] lemma rowReflectSpectral_normalization {n : ℕ} (i : Fin n) :
    rowReflectSpectral i (spectralNormalization n) = spectralNormalization n := by
  simp only [spectralNormalization,map_scalarNormalization,rowReflectSpectral_const,
    rowReflectSpectral_spectralA]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ArchRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators LaurentPolynomial

lemma archRootCoefficient_ne_zero (b : Bool) (k : ArchShiftIndex) :
    archRootCoefficient b k≠0 := by
  cases b <;> simp [archRootCoefficient,phase_ne_zero]

def archRootScalar {n : ℕ} : ArchRootIndex n → ℂ
  | none => 1
  | some (_,b,k) => archRootCoefficient b k

def archRoot {n : ℕ} (k : ArchRootIndex n) : SpectralField (n+2) :=
  evalLaurent (monomialL (archRootExponent k) (archRootScalar k))

lemma archRootScalar_ne_zero {n : ℕ} (k : ArchRootIndex n) : archRootScalar k≠0 := by
  cases k with
  | none => exact one_ne_zero
  | some k => exact archRootCoefficient_ne_zero k.2.1 k.2.2







def archEvaluate {n : ℕ} (f : Laurent (n+1)) (x : SpectralField (n+1)) (hx : x≠0) : SpectralField (n+1) :=
  torusEvaluation (Function.update variableF 0 x)
    (fun j => by by_cases h:j=0 <;> simp [h,hx,variableF_ne_zero]) f

end
 

 

noncomputable section
open scoped Classical BigOperators



def scalarArchNumerator {K : Type*} [CommRing K]
    (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) : K :=
  (∑ i,a i) * scalarValue f a ^ 2 - f (2*(d:ℂ)-1) * scalarValue f a * previousCoeff n (nextScalar f a)


def archCandidate (n : ℕ) : Laurent n := scalarArchNumerator (constantL n) rowCosineL

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram

noncomputable section
open scoped Classical BigOperators
open Filter Topology



def archPolynomialAt {n : ℕ} (a : Fin n → ℂ) : Polynomial ℂ :=
  Polynomial.C (scalarValue (RingHom.id ℂ) a)⁻¹ * nextScalar (RingHom.id ℂ) a

end
end CriticalStrip.Diagram




end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FluxWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree Filter Topology


def exitWeight (D : Vertex→Prop) (i : ℤ) (l : List Bool) : ℂ :=
  if IsExit D i l then wordWeight factor l else 0

end





end CriticalStrip.HoneycombBranch

end OAI
end


