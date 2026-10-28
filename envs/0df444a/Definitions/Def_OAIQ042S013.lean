-- Prove2me | Definitions.Def_OAIQ042S013
-- name    : OAIQ042S013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:59:38.011808+00:00
-- url     : https://prove2.me/theorems/f9666598-0701-4a7f-9080-f822b3a0f188
-- title:
--   Definitions bundle OAIQ042S013 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 120 declarations of OpenAI's Lean: 1 definition and 119 theorems. The definitions and types are `OAI.CriticalStrip.Diagram.integratedNorthSource`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: `StripMass_AugmentedTail`, `StripMass_CollisionSubstitutions`, `StripMass_CramerBounds`, `StripMass_DiagonalFactors`, `StripMass_FirstFlatSpecialization`, `StripMass_FirstThree`, `StripMass_InterpolantCovariance`, `StripMass_LastRow`, `StripMass_LaurentNumerator`, `StripMass_LocalPadding`, `StripMass_MergePairCandidate`, `StripMass_MirrorExterior`, `StripMass_NodalEmpty`, `StripMass_NodalExchange`, `StripMass_NodalRegularity`, `StripMass_NodalScalarDeletion`, `StripMass_NodalTorusValue`, `StripMass_PairSelfNode`, `StripMass_PhaseAlgebra`, `StripMass_ResidualEvaluation`, `StripMass_ResidualParityCoefficients`, `StripMass_RestrictedDiagrams`, `StripMass_ScalarFlat`, `StripMass_Specialization`, `StripMass_SpecializationPolynomial`, `StripMass_SwapVacancy`, `StripMass_ThreeBoxBraidPolynomial`, `StripMass_TopPadding`, `StripMass_VacuumDegree`.
--
--   **Imports.** It imports the bundles `OAIQ042S010`, `OAIQ042S011` and `OAIQ042S012` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ042S015`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ042S010
import Definitions.Def_OAIQ042S011
import Definitions.Def_OAIQ042S012

section
-- module Solutions.OAIQ042_SS.StripMass_TopPadding
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

theorem column_padTop {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜) (p q : Pairing n) :
    column w q.padTop p.padTop = column (fun i => w i.castSucc) q p := by
  classical
  unfold column
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => Tile))
    (fun tt : Tile × Configuration n =>
      if Realizes p.padTop q.padTop (Fin.snoc tt.2 tt.1)
      then ∏ i : Fin (n+1), (w i).tile ((Fin.snoc tt.2 tt.1 : Configuration (n+1)) i) else 0)
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [realizes_snoc_top_iff]
  rw [Finset.sum_eq_single Tile.vacant]
  · apply Finset.sum_congr rfl
    intro t _
    simp [Fin.prod_univ_castSucc, Weights.tile]
  · intro a ha hav
    simp [hav]
  · simp


theorem det_flat_top {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜)
    (hw : w (Fin.last n) = identityWeights ∨ w (Fin.last n) = deletionWeights) :
    (1-restrictedColumn w).det = (1-restrictedColumn (fun i => w i.castSucc)).det := by
  classical
  let e := Pairing.nonemptyTopSplit n
  let M := (restrictedColumn w).submatrix e e
  have hblock : M.toBlocks₁₁ = restrictedColumn (fun i => w i.castSucc) := by
    ext q p
    exact column_padTop w p.val q.val
  have hdet : (1-restrictedColumn w).det = (1-M).det := by
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv]
    rfl
  rw [hdet]
  rcases hw with hi | hd
  · rw [det_one_sub_zero_cols M, hblock]
    intro q p
    exact column_identity_top_col w hi p.val.val (e q).val (not_not.mp p.property)
  · rw [det_one_sub_zero_rows M, hblock]
    intro q p
    exact column_deletion_top_row w hd (e p).val q.val.val (not_not.mp q.property)



theorem det_one_nonflat {𝕜 : Type*} [CommRing 𝕜] (n : ℕ)
    (w : Fin n → Weights 𝕜)
    (hw : ∀ i j, ¬(w i).IsFlat → ¬(w j).IsFlat → i = j) :
    (1-restrictedColumn w).det = 1 := by
  classical
  induction n with
  | zero => exact det_column_le_one (by omega) w
  | succ n ih =>
      by_cases hn : n = 0
      · subst n; exact det_column_le_one (by omega) w
      by_cases hb : (w 0).IsFlat
      · rw [det_flat_bottom w hb]
        apply ih
        intro i j hi hj
        exact Fin.succ_injective n (hw i.succ j.succ hi hj)
      · have ht : (w (Fin.last n)).IsFlat := by
          by_contra ht
          have he := congrArg Fin.val (hw 0 (Fin.last n) hb ht)
          exact hn (by simpa using he.symm)
        rw [det_flat_top w ht]
        apply ih
        intro i j hi hj
        exact Fin.castSucc_injective n (hw i.castSucc j.castSucc hi hj)

theorem normalizedVacuum_stationary {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) (hw : VacuumRegular w) :
    IsNormalizedStationary w (normalizedVacuum w) := by
  classical
  let Q := restrictedColumn w
  let v := injectionColumn w
  let P := (1-Q)⁻¹.mulVec v
  have hsolve : P-Q.mulVec P = v := by
    suffices hs : (1-Q).mulVec P = v by simpa [Matrix.sub_mulVec] using hs
    change (1-Q).mulVec ((1-Q)⁻¹.mulVec v) = v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hw),
      Matrix.one_mulVec]
  refine ⟨attachEmpty_empty _, ?_⟩
  funext p
  by_cases hp : p = empty n
  · subst p; exact column_mulVec_empty w _
  · let p' : NonemptyPairing n := ⟨p,hp⟩
    change (column w).mulVec (attachEmpty P) p'.val = attachEmpty P p'.val
    rw [column_mulVec_nonempty]
    simp only [attachEmpty_empty, mul_one, attachEmpty_nonempty]
    have he := congrFun hsolve p'
    change P p' - Q.mulVec P p' = v p' at he
    exact eq_sub_iff_add_eq.mp he.symm

end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RestrictedDiagrams
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Circuit.compactWiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph _root_.OAI.CriticalStrip.Diagram.peeledRingIsDomain _root_.OAI.CriticalStrip.Diagram.spectralFieldCharZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section



theorem spectral_regular (n : ℕ) : VacuumRegular (spectralWeights n) := by
  apply regular_of_cleared_specialization
    (algebraMap (SpectralRing n) (SpectralField n))
    (IsFractionRing.injective _ _) (flatEval n).toRingHom
    rowDenominator rowNumerator (spectralWeights n) (fun _ => deletionWeights)
  · exact flatEval_rowDenominator_ne_zero
  · exact rowNumerator_map
  · exact rowNumerator_flatEval
  · unfold VacuumRegular
    rw [det_one_nonflat]
    · exact one_ne_zero
    · intro i j hi
      exact (hi (Or.inr rfl)).elim

theorem spectral_normalizedVacuum_stationary (n : ℕ) :
    IsNormalizedStationary (spectralWeights n) (normalizedVacuum (spectralWeights n)) :=
  normalizedVacuum_stationary _ (spectral_regular n)
end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LastRow
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Circuit.compactWiring_symm _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph _root_.OAI.CriticalStrip.Diagram.gateWiring_symm _root_.OAI.CriticalStrip.Diagram.peeledRingIsDomain _root_.OAI.CriticalStrip.Diagram.spectralFieldCharZero _root_.OAI.CriticalStrip.Diagram.tileAdjDecidable _root_.OAI.CriticalStrip.Diagram.tileOccupiedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset


theorem lastCoefficient_padTop {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (q p : Pairing n) :
    lastCoefficient w q.padTop p.padTop = rawColumn w q p := by
  classical
  simp only [lastCoefficient, lastTile, Pairing.padTop_not_occupied_last,
    ite_false, realizes_snoc_top_iff, true_and, rawColumn]



end

 

 

noncomputable section






open scoped Classical

lemma normalizedVacuum_map {K L : Type*} [Field K] [Field L] {n : ℕ}
    (f : K →+* L) (w : Fin n → Weights K) (h : VacuumRegular w) :
    (fun p => f (normalizedVacuum w p))=normalizedVacuum (fun i => (w i).map f) := by
  apply normalizedVacuum_unique _ (h.map f w)
  have hs:=normalizedVacuum_stationary w h
  constructor
  · change f (normalizedVacuum w (empty n))=1
    rw [hs.1,map_one]
  · funext p
    have hh:=congrArg f (congrFun hs.2 p)
    simp only [Matrix.mulVec,dotProduct,map_sum,map_mul] at hh ⊢
    simpa only [←column_map,Matrix.map_apply] using hh

end

 

 

noncomputable section
open scoped Classical

lemma permSpectral_vacuum {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pairing n) :
    permSpectral σ (normalizedVacuum (spectralWeights n) p)=
      normalizedVacuum (fun i => spectralWeights n (σ i)) p := by
  have h:=congrFun (normalizedVacuum_map (permSpectral σ) (spectralWeights n) (spectral_regular n)) p
  simpa using h

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DiagonalFactors
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Circuit.compactWiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph _root_.OAI.CriticalStrip.Diagram.spectralFieldCharZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical



lemma insertSpectral_vacuum {n : ℕ} (i : Fin (n+1)) (p : Pairing n) :
    insertSpectral i (normalizedVacuum (spectralWeights n) p)=
      normalizedVacuum (fun j => spectralWeights (n+1) (i.succAbove j)) p := by
  have h:=congrFun (normalizedVacuum_map (insertSpectral i) (spectralWeights n) (spectral_regular n)) p
  simpa using h

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_AugmentedTail
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
open scoped Classical



theorem lastTransform_leading {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) {m : ℕ} (hP : LastDegree m P)
    (q : Pairing n) :
    (lastTransform w d c C P q.padTop).coeff (m+1) =
      (rawColumn w).mulVec (fun p => (P p.padTop).coeff m) q := by
  classical
  rw [lastTransform_coeff_succ]
  simp only [Pairing.padTop_not_occupied_last, ite_false, Matrix.mulVec, dotProduct]
  symm
  apply Fintype.sum_of_injective Pairing.padTop Pairing.padTop_injective
  · intro p hp
    have hp' : p.Occupied (Fin.last n) := by
      by_contra h
      exact hp ⟨p.restrict Fin.castSuccOrderEmb, Pairing.padTop_restrict p h⟩
    have h₀ := hP p m (by simp [hp'])
    have h₁ := hP p (m+1) (by simp [hp'])
    simp [hp', h₀, h₁]
  · intro p
    have h₁ := hP p.padTop (m+1) (by simp)
    simp [lastCoefficient_padTop, h₁]

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxBraidPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

theorem braid_numerator {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) (k : Fin 51) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) k =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) (mirrorIndex k) := by
  fin_cases k
  · exact braid_numerator_0 q z w hq
  · exact braid_numerator_1 q z w hq
  · exact braid_numerator_2 q z w hq
  · exact braid_numerator_3 q z w hq
  · exact braid_numerator_4 q z w hq
  · exact braid_numerator_5 q z w hq
  · exact braid_numerator_6 q z w hq
  · exact braid_numerator_7 q z w hq
  · exact braid_numerator_8 q z w hq
  · exact braid_numerator_9 q z w hq
  · exact braid_numerator_10 q z w hq
  · exact braid_numerator_11 q z w hq
  · exact braid_numerator_12 q z w hq
  · exact braid_numerator_13 q z w hq
  · exact braid_numerator_14 q z w hq
  · exact braid_numerator_15 q z w hq
  · exact braid_numerator_16 q z w hq
  · exact braid_numerator_17 q z w hq
  · exact braid_numerator_18 q z w hq
  · exact braid_numerator_19 q z w hq
  · exact braid_numerator_20 q z w hq
  · exact braid_numerator_21 q z w hq
  · exact braid_numerator_22 q z w hq
  · exact braid_numerator_23 q z w hq
  · exact braid_numerator_24 q z w hq
  · exact braid_numerator_25 q z w hq
  · exact braid_numerator_26 q z w hq
  · exact braid_numerator_27 q z w hq
  · exact braid_numerator_28 q z w hq
  · exact braid_numerator_29 q z w hq
  · exact braid_numerator_30 q z w hq
  · exact braid_numerator_31 q z w hq
  · exact braid_numerator_32 q z w hq
  · exact braid_numerator_33 q z w hq
  · exact braid_numerator_34 q z w hq
  · exact braid_numerator_35 q z w hq
  · exact braid_numerator_36 q z w hq
  · exact braid_numerator_37 q z w hq
  · exact braid_numerator_38 q z w hq
  · exact braid_numerator_39 q z w hq
  · exact braid_numerator_40 q z w hq
  · exact braid_numerator_41 q z w hq
  · exact braid_numerator_42 q z w hq
  · exact braid_numerator_43 q z w hq
  · exact braid_numerator_44 q z w hq
  · exact braid_numerator_45 q z w hq
  · exact braid_numerator_46 q z w hq
  · exact braid_numerator_47 q z w hq
  · exact braid_numerator_48 q z w hq
  · exact braid_numerator_49 q z w hq
  · exact braid_numerator_50 q z w hq

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PhaseAlgebra
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.ThreeBox.adjStdSymm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset



theorem braid_coefficient {n : ℕ} (z w : SpectralField n)
    (hz : z ≠ 0) (hw : w ≠ 0) (hLz : torusL z ≠ 0) (hLw : torusL w ≠ 0)
    (hLzw : torusL (z*w) ≠ 0) (k : Fin 51) :
    coefficient (torusWeights z).tile (torusWeights (z*w)).tile (torusWeights w).tile k =
    coefficient (torusWeights w).tile (torusWeights (z*w)).tile (torusWeights z).tile
      (mirrorIndex k) := by
  have hN (v : SpectralField n) (hv : v ≠ 0) (hLv : torusL v ≠ 0) :
      (fun t => torusCommon v * (torusWeights v).tile t) =
        tileNumerator (constF n phase) (constF n phase^4) v :=
    funext (torusWeights_cleared v hv hLv)
  have h := braid_numerator (constF n phase) z w (constF_phase_eight n) k
  rw [← hN z hz hLz, ← hN w hw hLw, ← hN (z*w) (mul_ne_zero hz hw) hLzw,
    coefficient_scale, coefficient_scale] at h
  have hc := mul_ne_zero (mul_ne_zero (torusCommon_ne_zero z hz hLz)
    (torusCommon_ne_zero (z*w) (mul_ne_zero hz hw) hLzw)) (torusCommon_ne_zero w hw hLw)
  apply mul_left_cancel₀ hc
  calc
    _ = (torusCommon w * torusCommon (z*w) * torusCommon z) *
        coefficient (torusWeights w).tile (torusWeights (z*w)).tile (torusWeights z).tile
          (mirrorIndex k) := h
    _ = _ := by ring

end

 

 

noncomputable section
open Finset
open scoped Classical



theorem braid_partition {n : ℕ} (z w : SpectralField n)
    (hz : z ≠ 0) (hw : w ≠ 0) (hLz : torusL z ≠ 0) (hLw : torusL w ≠ 0)
    (hLzw : torusL (z*w) ≠ 0) (P : Fin 51 → Prop) :
    (∑ t : Config, if ∃ k, profile t = some k ∧ P k
      then (torusWeights z).tile t.1 * (torusWeights (z*w)).tile t.2.1 *
        (torusWeights w).tile t.2.2 else 0) =
    (∑ t : Config, if ∃ k, profile t = some k ∧ P (mirrorIndex k)
      then (torusWeights w).tile t.1 * (torusWeights (z*w)).tile t.2.1 *
        (torusWeights z).tile t.2.2 else 0) := by
  rw [profile_partition, profile_partition]
  simp_rw [braid_coefficient z w hz hw hLz hLw hLzw]
  let e : Fin 51 ≃ Fin 51 :=
    ⟨mirrorIndex,mirrorIndex,mirrorIndex_involutive,mirrorIndex_involutive⟩
  refine Fintype.sum_equiv e _ _ ?_
  intro k
  change (if P k then _ else 0) =
    (if P (mirrorIndex (mirrorIndex k)) then _ else 0)
  rw [mirrorIndex_involutive]
  rfl

end





end CriticalStrip.Diagram.ThreeBox





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MirrorExterior
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical
namespace TriplePosition
variable {n m : ℕ} (s : TriplePosition n)

 

theorem torus_yang_baxter (z w : SpectralField m)
    (hz : z≠0) (hw : w≠0) (hLz : torusL z≠0) (hLw : torusL w≠0)
    (hLzw : torusL (z*w)≠0) :
    localR s.right (torusWeights w) * localR s.left (torusWeights (z*w)) *
        localR s.right (torusWeights z) =
      localR s.left (torusWeights z) * localR s.right (torusWeights (z*w)) *
        localR s.left (torusWeights w) := by
  ext q p
  rw [triple_expansion,triple_expansion_mirror]
  change (∑ t : ThreeBox.Config, if Circuit.eval p (s.rightCircuit t)=some q
    then (torusWeights z).tile t.1*(torusWeights (z*w)).tile t.2.1*(torusWeights w).tile t.2.2 else 0) =
    (∑ t : ThreeBox.Config, if Circuit.eval p (s.leftCircuit t)=some q
    then (torusWeights w).tile t.1*(torusWeights (z*w)).tile t.2.1*(torusWeights z).tile t.2.2 else 0)
  simp_rw [s.eval_profile_iff,s.mirror_eval_profile_iff,s.mirror_predicate]
  exact ThreeBox.braid_partition z w hz hw hLz hLw hLzw (s.exteriorPredicate p q)

end TriplePosition





end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LocalPadding
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
namespace PartialColumn
variable {n m : ℕ}



theorem torus_column_exchange (r : ℕ) (hr : r+2≤n) (x : Fin n → SpectralField m)
    (z : SpectralField m) (hz : z≠0) (hw : x ⟨r+1,by omega⟩≠0)
    (hLz : torusL z≠0) (hLw : torusL (x ⟨r+1,by omega⟩)≠0)
    (hLx : torusL (x ⟨r,by omega⟩)≠0)
    (hx : z*x ⟨r+1,by omega⟩=x ⟨r,by omega⟩) :
    column (fun i => torusWeights (x i)) * localR (rowPosition r hr) (torusWeights z) =
      localR (rowPosition r hr) (torusWeights z) *
        column (fun i => torusWeights (x (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩ i))) := by
  let w : Fin n → Weights (SpectralField m) := fun i => torusWeights (x i)
  let v : Fin n → Weights (SpectralField m) := fun i =>
    torusWeights (x (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩ i))
  have hyb : localR (position ⟨r+1,by omega⟩) (w ⟨r+1,by omega⟩) *
        localR (position ⟨r,by omega⟩) (w ⟨r,by omega⟩) *
        localR (rowPosition r hr).padBottom (torusWeights z) =
      localR (rowPosition r hr).padTop (torusWeights z) *
        localR (position ⟨r+1,by omega⟩) (v ⟨r+1,by omega⟩) *
        localR (position ⟨r,by omega⟩) (v ⟨r,by omega⟩) := by
    simpa only [w,v,Equiv.swap_apply_left,Equiv.swap_apply_right,hx,
      rowTriple,TriplePosition.left,TriplePosition.right,position,rowPosition,
      Position.padTop,Position.padBottom,Fin.castSucc_mk,Fin.succ_mk,Nat.add_assoc] using
      (rowTriple r hr).torus_yang_baxter z (x ⟨r+1,by omega⟩) hz hw hLz hLw (by rwa [hx])
  have he (i : Fin n) (hi : i.val≠r) (hj : i.val≠r+1) : w i=v i := by
    dsimp [w,v]
    rw [Equiv.swap_apply_of_ne_of_ne (fun he => hi (congrArg Fin.val he))
      (fun he => hj (congrArg Fin.val he))]
  have H := exchange_program w v r hr
    (localR (rowPosition r hr).padTop (torusWeights z))
    (localR (rowPosition r hr).padBottom (torusWeights z)) he
    (fun i hi => localR_commute _ _ (row_disjoint_low r hr i hi) _ _)
    (fun i hi => localR_commute _ _ (row_disjoint_high r hr i hi) _ _) hyb
  have hcw : (program w n le_rfl).matrix.submatrix Pairing.padTop Pairing.padBottom=column w := by
    ext q p
    exact program_column (by omega) w p q
  have hcv : (program v n le_rfl).matrix.submatrix Pairing.padTop Pairing.padBottom=column v := by
    ext q p
    exact program_column (by omega) v p q
  ext q p
  have HH:=congrArg (fun M => M q.padTop p.padBottom) H
  rw [localR_bottom_matrix,localR_top_matrix,hcw,hcv] at HH
  exact HH






end PartialColumn
end





end CriticalStrip.Diagram





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



theorem normalizedVacuum_torus_exchange {n m : ℕ} (r : ℕ) (hr : r+2≤n)
    (x : Fin n → SpectralField m) (z : SpectralField m) (hz : z≠0)
    (hw : x ⟨r+1,by omega⟩≠0) (hLz : torusL z≠0)
    (hLw : torusL (x ⟨r+1,by omega⟩)≠0) (hLx : torusL (x ⟨r,by omega⟩)≠0)
    (hx : z*x ⟨r+1,by omega⟩=x ⟨r,by omega⟩)
    (hreg : VacuumRegular (fun i => torusWeights (x i)))
    (hreg' : VacuumRegular (fun i => torusWeights (x (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩ i)))) :
    normalizedVacuum (fun i => torusWeights (x i)) =
      (localR (PartialColumn.rowPosition r hr) (torusWeights z)).mulVec
        (normalizedVacuum (fun i => torusWeights (x (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩ i)))) := by
  symm
  apply normalizedVacuum_unique _ hreg
  have hs := normalizedVacuum_stationary _ hreg'
  constructor
  · rw [localR_mulVec_empty]; exact hs.1
  · rw [Matrix.mulVec_mulVec,PartialColumn.torus_column_exchange r hr x z hz hw hLz hLw hLx hx,
      ←Matrix.mulVec_mulVec,hs.2]







theorem normalizedVacuum_deletion {n m : ℕ} (r : ℕ) (hr : r+2≤n+2)
    (w : Fin (n+2) → Weights (SpectralField m)) (z : SpectralField m)
    (hz : z≠0) (hL : torusL z≠0) (hL3 : torusL (constF m phase^3*z)≠0)
    (hw₀ : w ⟨r,by omega⟩=torusWeights (constF m phase^3*z))
    (hw₁ : w ⟨r+1,by omega⟩=torusWeights z)
    (hreg : VacuumRegular w)
    (hreg' : VacuumRegular (fun i => w ((⟨r+1,by omega⟩ : Fin (n+2)).succAbove
      ((⟨r,by omega⟩ : Fin (n+1)).succAbove i)))) :
    normalizedVacuum w = (deletionMap r hr).mulVec (normalizedVacuum
      (fun i => w ((⟨r+1,by omega⟩ : Fin (n+2)).succAbove
        ((⟨r,by omega⟩ : Fin (n+1)).succAbove i)))) := by
  let j : Fin (n+2) := ⟨r+1,by omega⟩
  let k : Fin (n+1) := ⟨r,by omega⟩
  have hrows : (fun i => (PartialColumn.twoRows w r swapWeights swapWeights)
      (j.succAbove (k.succAbove i)))=(fun i => w (j.succAbove (k.succAbove i))) := by
    funext i
    symm
    apply PartialColumn.twoRows_other
    · intro h
      have hk:=Fin.succAbove_ne k i
      apply hk
      have hjk : j.succAbove k=⟨r,by omega⟩ := by
        rw [Fin.succAbove_of_castSucc_lt]
        · rfl
        · change r < r+1; omega
      apply Fin.succAbove_right_injective
      rw [hjk]
      exact Fin.ext h
    · exact fun h => Fin.succAbove_ne j (k.succAbove i) (Fin.ext h)
  have he := PartialColumn.column_deletion_intertwiner r hr w z hz hL hL3 hw₀ hw₁
  change column w*deletionMap r hr=deletionMap r hr*column _ at he
  rw [hrows] at he
  symm
  apply normalizedVacuum_unique _ hreg
  have hs:=normalizedVacuum_stationary _ hreg'
  constructor
  · rw [deletionMap_mulVec_empty]; exact hs.1
  · rw [Matrix.mulVec_mulVec,he,←Matrix.mulVec_mulVec,hs.2]

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


theorem nodal_regular {n : ℕ} (i : Fin n) : VacuumRegular (nodalWeights i) := by
  apply regular_of_cleared_specialization
    (algebraMap (SpectralRing n) (SpectralField n))
    (IsFractionRing.injective _ _) (flatEval n).toRingHom
    (Fin.snoc rowDenominator (inverseRowDenominator i))
    (Fin.snoc rowNumerator (inverseRowNumerator i))
    (nodalWeights i) (Fin.snoc (fun _ => deletionWeights) identityWeights)
  · intro j
    induction j using Fin.lastCases with
    | last => simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Fin.snoc_last] using inverseRowDenominator_flat_ne_zero i
    | cast j => simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Fin.snoc_castSucc] using flatEval_rowDenominator_ne_zero j
  · intro j t
    induction j using Fin.lastCases with
    | last => simpa only [evalLaurent, Fin.snoc_last, nodalWeights_last] using inverseRowNumerator_map i t
    | cast j => simpa only [Fin.snoc_castSucc, nodalWeights] using rowNumerator_map j t
  · intro j t
    induction j using Fin.lastCases with
    | last => simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Fin.snoc_last] using inverseRowNumerator_flat i t
    | cast j => simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Fin.snoc_castSucc] using rowNumerator_flatEval j t
  · unfold VacuumRegular
    rw [det_one_nonflat]
    · exact one_ne_zero
    · intro j k hj hk
      induction j using Fin.lastCases with
      | last => exact (hj (Or.inl (Fin.snoc_last ..))).elim
      | cast j => exact (hj (Or.inr (Fin.snoc_castSucc ..))).elim

theorem nodalVacuum_stationary {n : ℕ} (i : Fin n) :
    (column (nodalWeights i)).mulVec (nodalVacuum i) = nodalVacuum i := by
  have h := (normalizedVacuum_stationary (nodalWeights i) (nodal_regular i)).2
  change (column (nodalWeights i)).mulVec (nodalScalar i • normalizedVacuum (nodalWeights i)) =
    nodalScalar i • normalizedVacuum (nodalWeights i)
  rw [Matrix.mulVec_smul, h]


 

 

open scoped Classical

 

lemma spectral_regular_reindex {n m : ℕ} (f : Fin n → Fin m) :
    VacuumRegular (fun i => spectralWeights m (f i)) := by
  apply regular_of_cleared_specialization
    (algebraMap (SpectralRing m) (SpectralField m))
    (IsFractionRing.injective _ _) (flatEval m).toRingHom
    (fun i => rowDenominator (f i)) (fun i => rowNumerator (f i))
    (fun i => spectralWeights m (f i)) (fun _ => deletionWeights)
  · intro i; exact flatEval_rowDenominator_ne_zero (f i)
  · intro i; exact rowNumerator_map (f i)
  · intro i; exact rowNumerator_flatEval (f i)
  · unfold VacuumRegular
    rw [det_one_nonflat]
    · exact one_ne_zero
    · intro i j hi; exact (hi (Or.inr rfl)).elim



theorem spectral_vacuum_exchange {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    normalizedVacuum (spectralWeights n) =
      (localR (PartialColumn.rowPosition r hr)
        (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩))).mulVec
        (normalizedVacuum (fun i => spectralWeights n
          (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩ i))) := by
  apply normalizedVacuum_torus_exchange r hr
    (fun i => constF n phase^3/variableF i)
    (variableF ⟨r+1,by omega⟩/variableF ⟨r,by omega⟩)
  · exact div_ne_zero (variableF_ne_zero _) (variableF_ne_zero _)
  · exact div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) (variableF_ne_zero _)
  · exact torusL_ratio_ne_zero _ _
  · rw [← rowDenominator_map]; exact rowDenominator_map_ne_zero _
  · rw [← rowDenominator_map]; exact rowDenominator_map_ne_zero _
  · field_simp [variableF_ne_zero]
  · exact spectral_regular n
  · exact spectral_regular_reindex _

end

 

 

noncomputable section
open scoped Classical



lemma insertedNode_regular {n : ℕ} (i : Fin n) (j : Fin (n+1)) :
    VacuumRegular (insertedNodeWeights i j) := by
  apply regular_of_cleared_specialization
    (algebraMap (SpectralRing n) (SpectralField n))
    (IsFractionRing.injective _ _) (flatEval n).toRingHom
    (Fin.insertNth j (inverseRowDenominator i) rowDenominator)
    (Fin.insertNth j (inverseRowNumerator i) rowNumerator)
    (insertedNodeWeights i j) (Fin.insertNth j identityWeights (fun _ => deletionWeights))
  · intro k
    refine Fin.succAboveCases j ?_ (fun l => ?_) k <;> simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
    · exact inverseRowDenominator_flat_ne_zero i
    · exact flatEval_rowDenominator_ne_zero l
  · intro k t
    refine Fin.succAboveCases j ?_ (fun l => ?_) k <;> simp only [insertedNodeWeights,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
    · exact inverseRowNumerator_map i t
    · exact rowNumerator_map _ t
  · intro k t
    refine Fin.succAboveCases j ?_ (fun l => ?_) k <;> simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
    · exact inverseRowNumerator_flat i t
    · exact rowNumerator_flatEval _ t
  · unfold VacuumRegular
    rw [det_one_nonflat]
    · exact one_ne_zero
    · intro k l hk
      rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨a,rfl⟩
      · exact (hk (Or.inl (Fin.insertNth_apply_same ..))).elim
      · exact (hk (Or.inr (Fin.insertNth_apply_succAbove ..))).elim

lemma insertedNode_deletion {n : ℕ} (i : Fin (n+1)) :
    normalizedVacuum (insertedNodeWeights i i.succ) =
      (deletionMap i.val (show i.val+2≤n+2 by omega)).mulVec
        (normalizedVacuum (fun k => spectralWeights (n+1) (i.succAbove k))) := by
  have hrows : (fun k => insertedNodeWeights i i.succ
      (i.succ.succAbove (i.succAbove k)))=(fun k => spectralWeights (n+1) (i.succAbove k)) := by
    funext k; exact Fin.insertNth_apply_succAbove _ _ _ _
  have h₀ : insertedNodeWeights i i.succ ⟨i.val,by omega⟩=
      torusWeights (constF (n+1) phase^3*(variableF i)⁻¹) := by
    have hi : i.succ.succAbove i=i.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.castSucc_lt_succ
    change insertedNodeWeights i i.succ i.castSucc=_
    rw [←hi]
    simp only [insertedNodeWeights,Fin.insertNth_apply_succAbove,spectralWeights,div_eq_mul_inv]
  have h₁ : insertedNodeWeights i i.succ ⟨i.val+1,by omega⟩=torusWeights (variableF i)⁻¹ :=
    Fin.insertNth_apply_same ..
  have hL : torusL (constF (n+1) phase^3*(variableF i)⁻¹)≠0 := by
    rw [←div_eq_mul_inv,←rowDenominator_map]
    exact rowDenominator_map_ne_zero i
  have h := normalizedVacuum_deletion i.val (show i.val+2≤n+2 by omega)
    (insertedNodeWeights i i.succ) (variableF i)⁻¹
    (inv_ne_zero (variableF_ne_zero i))
    (by rw [←inverseRowDenominator_map]; exact inverseRowDenominator_map_ne_zero i) hL
    h₀ h₁ (insertedNode_regular i i.succ)
    (by change VacuumRegular (fun k => insertedNodeWeights i i.succ
        (i.succ.succAbove (i.succAbove k)))
        rw [hrows]; exact spectral_regular_reindex i.succAbove)
  change normalizedVacuum (insertedNodeWeights i i.succ) =
    (deletionMap i.val _).mulVec (normalizedVacuum
      (fun k => insertedNodeWeights i i.succ (i.succ.succAbove (i.succAbove k)))) at h
  rw [hrows] at h
  exact h







theorem insertedNode_move {n : ℕ} (i j : Fin n) :
    normalizedVacuum (insertedNodeWeights i j.succ)=
      (localR (PartialColumn.rowPosition j.val (show j.val+2≤n+1 by omega))
        (torusWeights (constF n phase^3 * (variableF i/variableF j)))).mulVec
          (normalizedVacuum (insertedNodeWeights i j.castSucc)) := by
  let a : Fin (n+1):=j.castSucc
  let b : Fin (n+1):=j.succ
  let x : Fin (n+1) → SpectralField n := Fin.insertNth b (variableF i)⁻¹ (fun k => constF n phase^3/variableF k)
  let z := constF n phase^3*(variableF i/variableF j)
  have h₀ : x a=constF n phase^3/variableF j := by
    have h : b.succAbove j=a := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.castSucc_lt_succ
    rw [←h]
    exact Fin.insertNth_apply_succAbove ..
  have h₁ : x b=(variableF i)⁻¹ := Fin.insertNth_apply_same ..
  have hw : (fun k => torusWeights (x k))=insertedNodeWeights i b := by
    funext k
    refine Fin.succAboveCases b ?_ (fun l => ?_) k <;>
      simp only [x,insertedNodeWeights,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,spectralWeights]
  have hx : z*x b=x a := by
    rw [h₀,h₁]
    dsimp only [z]
    field_simp [variableF_ne_zero]
  have hL₀ : torusL (x a)≠0 := by
    rw [h₀,←rowDenominator_map]; exact rowDenominator_map_ne_zero j
  have hL₁ : torusL (x b)≠0 := by
    rw [h₁,←inverseRowDenominator_map]; exact inverseRowDenominator_map_ne_zero i
  have hswap : (insertedNodeWeights i b) ∘ Equiv.swap a b=insertedNodeWeights i a :=
    Fin.insertNth_swap_adjacent a b rfl _ _
  have hh := normalizedVacuum_torus_exchange j.val (show j.val+2≤n+1 by omega) x z
    (mul_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _))
      (div_ne_zero (variableF_ne_zero _) (variableF_ne_zero _)))
    (by change x b≠0; rw [h₁]; exact inv_ne_zero (variableF_ne_zero i))
    (torusL_deletion_ratio_ne_zero i j) hL₁ hL₀ hx
    (by rw [hw]; exact insertedNode_regular i b)
    (by change VacuumRegular ((fun k => torusWeights (x k)) ∘ Equiv.swap a b)
        rw [hw,hswap]; exact insertedNode_regular i a)
  rw [hw] at hh
  have hs : (fun k => torusWeights (x (Equiv.swap ⟨j.val,by omega⟩ ⟨j.val+1,by omega⟩ k)))=
      insertedNodeWeights i a := by
    change (fun k => torusWeights (x k)) ∘ Equiv.swap a b=insertedNodeWeights i a
    rw [hw,hswap]
  rw [hs] at hh
  exact hh









lemma insertedNode_moved {n : ℕ} (i : Fin n) (k : ℕ)
    (hk : i.val+1 ≤ k) (hkn : k ≤ n) :
    normalizedVacuum (insertedNodeWeights i ⟨k,by omega⟩)=
      (movingBoxes i k).mulVec (normalizedVacuum (insertedNodeWeights i i.succ)) := by
  induction k, hk using Nat.le_induction with
  | base =>
      rw [movingBoxes_initial i _ le_rfl,Matrix.one_mulVec]
      rfl
  | succ k hk ih =>
      have hstep:=insertedNode_move i (⟨k,show k<n by omega⟩ : Fin n)
      change normalizedVacuum (insertedNodeWeights i ⟨k+1,by omega⟩)=_
      rw [movingBoxes,dite_eq_left (by omega),←Matrix.mulVec_mulVec]
      rw [←ih (by omega)]
      exact hstep

 

theorem nodalVacuum_movingBoxes {n : ℕ} (i : Fin (n+1)) :
    normalizedVacuum (nodalWeights i)=
      (movingBoxes i (n+1)).mulVec
        ((deletionMap i.val (show i.val+2≤n+2 by omega)).mulVec
          (normalizedVacuum (fun k => spectralWeights (n+1) (i.succAbove k)))) := by
  rw [←insertedNodeWeights_last]
  have h:=insertedNode_moved i (n+1) (by omega) le_rfl
  rw [insertedNode_deletion] at h
  exact h







lemma nodal_regular_reindex {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    VacuumRegular (fun j => nodalWeights (σ i) (topPerm σ j)) := by
  rw [←permSpectral_nodalWeights]
  exact (nodal_regular i).map (permSpectral σ) (nodalWeights i)

lemma permSpectral_nodalVacuum {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n)
    (p : Pairing (n+1)) :
    permSpectral σ (nodalVacuum i p)=nodalScalar (σ i)*
      normalizedVacuum (fun j => nodalWeights (σ i) (topPerm σ j)) p := by
  rw [nodalVacuum,map_mul,permSpectral_nodalScalar]
  have hh:=congrFun (normalizedVacuum_map (permSpectral σ) (nodalWeights i) (nodal_regular i)) p
  rw [permSpectral_nodalWeights] at hh
  rw [hh]

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

lemma insertSpectral_rationalVacuum {n : ℕ} (i : Fin (n+1)) :
    (fun p => insertSpectral i (rationalVacuum n p))=
      insertSpectral i (spectralNormalization n) •
        normalizedVacuum (fun j => spectralWeights (n+1) (i.succAbove j)) := by
  funext p
  simp only [rationalVacuum,map_mul,insertSpectral_vacuum,Pi.smul_apply,smul_eq_mul]

 

theorem nodalVacuum_interpolation_data {n : ℕ} (i : Fin (n+1)) :
    nodalVacuum i = deletionDataFactor i •
      (movingBoxes i (n+1)).mulVec
        ((deletionMap i.val (show i.val+2≤n+2 by omega)).mulVec
          (fun p => insertSpectral i (rationalVacuum n p))) := by
  change nodalScalar i • normalizedVacuum (nodalWeights i)=_
  rw [nodalVacuum_movingBoxes,nodalScalar_factor_smaller,insertSpectral_rationalVacuum,
    Matrix.mulVec_smul,Matrix.mulVec_smul,smul_smul]

end





noncomputable section






open scoped Classical



theorem nodalVacuum_reduced_data {n : ℕ} (i : Fin (n+1)) :
    nodalVacuum i =
      ((spectralA i+deletionBeta i+constF (n+1) rho)*∏ j,reflectionFactor i j) •
        (matrixPrefix (reducedMovingStep i) (n+1)).mulVec
          ((deletionMap i.val (show i.val+2≤n+2 by omega)).mulVec
            (fun p => insertSpectral i (rationalVacuum n p))) := by
  rw [nodalVacuum_interpolation_data,deletionDataFactor,←scalarPairFactor_product]
  rw [←smul_smul,←Matrix.smul_mulVec,reducedMoving_product,Matrix.smul_mulVec,smul_smul]

end





noncomputable section
open scoped Classical

lemma reducedNodalDatum_eq {n : ℕ} (i : Fin (n+1)) (p : Pairing (n+2)) :
    nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1)=
      (∏ j,reflectionFactor i j)*reducedNodalDatum i p := by
  have h:=congrFun (nodalVacuum_reduced_data i) p
  simp only [Pi.smul_apply,smul_eq_mul] at h
  rw [h]
  unfold reducedNodalDatum reducedNodalHead
  by_cases hp:p.Occupied (Fin.last (n+1))
  · rw [ite_eq_left hp,ite_eq_left hp,deletion_occupied_sine_cancellation]
    field_simp [deletionNode_sine_ne_zero i]
  · rw [ite_eq_right hp,ite_eq_right hp,div_one]
    ring

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

lemma nodalDatumL_map {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (i : Fin (n+1)) (p : Pairing (n+2)) :
    evalLaurent (nodalDatumL W i p)=
      nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1) := by
  rw [reducedNodalDatum_eq]
  simp only [nodalDatumL,evalLaurent,map_mul,map_prod]
  change (∏ j,evalLaurent (reflectionFactorL i j))*evalLaurent (nodalHeadL i _) *
    (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))
      ((matrixPrefix (reducedMovingStepL i) (n+1)).mulVec _ p)=_
  simp only [reflectionFactorL_map,nodalHeadL_map]
  simp only [RingHom.map_mulVec,Function.comp_def,reducedMovingTrainL_map,deletionMapL_map]
  have hw (q:Pairing n) : (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (insertLaurent i (W q))=insertSpectral i (rationalVacuum n q) := by
    change evalLaurent (insertLaurent i (W q))=_
    rw [←insertSpectral_evalLaurent,hW]
  simp only [hw]
  exact mul_assoc _ _ _







end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CramerBounds
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


lemma normalizedVacuum_signTwist {K : Type*} [Field K] {n : ℕ}
    (w : Fin n → Weights K) (i : Fin n) (hw : VacuumRegular w)
    (hs : VacuumRegular (Function.update w i (w i).signTwist)) :
    normalizedVacuum (Function.update w i (w i).signTwist)=
      fun p => occupancySign p i*normalizedVacuum w p := by
  symm
  apply normalizedVacuum_unique _ hs
  constructor
  · simp only [occupancySign_empty,one_mul]
    exact (normalizedVacuum_stationary w hw).1
  · funext q
    simp only [Matrix.mulVec,dotProduct,column_signTwist]
    have hh : ∀ p : Pairing n,
        occupancySign q i*occupancySign p i*column w q p*
          (occupancySign p i*normalizedVacuum w p)=
        occupancySign q i*(column w q p*normalizedVacuum w p) := by
      intro p
      calc
        _=occupancySign q i*(occupancySign p i*occupancySign p i)*
          (column w q p*normalizedVacuum w p) := by ring
        _=_ := by rw [occupancySign_mul_self,mul_one]
    simp_rw [hh]
    rw [←mul_sum]
    exact congrArg (occupancySign q i * ·) (congrFun (normalizedVacuum_stationary w hw).2 q)

end

 

 

noncomputable section
open scoped Classical

lemma signSpectral_vacuum {n : ℕ} (i : Fin n) (p : Pairing n) :
    signSpectral i (normalizedVacuum (spectralWeights n) p)=
      occupancySign p i*normalizedVacuum (spectralWeights n) p := by
  have hh:=normalizedVacuum_map (signSpectral i) (spectralWeights n) (spectral_regular n)
  have hr:VacuumRegular (Function.update (spectralWeights n) i (spectralWeights n i).signTwist) := by
    rw [←signSpectral_spectralWeights]
    exact (spectral_regular n).map (signSpectral i) (spectralWeights n)
  rw [signSpectral_spectralWeights,normalizedVacuum_signTwist _ _ (spectral_regular n) hr] at hh
  exact congrFun hh p


theorem rationalVacuum_sign {n : ℕ} (i : Fin n) (p : Pairing n) :
    signSpectral i (rationalVacuum n p)=occupancySign p i*rationalVacuum n p := by
  rw [rationalVacuum,map_mul,signSpectral_normalization,signSpectral_vacuum]
  ring


 

 


 

lemma normalizedVacuum_gauge {K : Type*} [Field K] {n : ℕ}
    (w v : Fin n → Weights K) (hw : VacuumRegular w) (hv : VacuumRegular v)
    (ε : Pairing n → K) (hε : ∀ p,ε p*ε p=1) (he : ε (empty n)=1)
    (hc : ∀ p q,column v q p=ε q*ε p*column w q p) :
    normalizedVacuum v=fun p => ε p*normalizedVacuum w p := by
  symm
  apply normalizedVacuum_unique _ hv
  constructor
  · change ε (empty n)*normalizedVacuum w (empty n)=1
    rw [he,(normalizedVacuum_stationary w hw).1,one_mul]
  · funext q
    simp only [Matrix.mulVec,dotProduct,hc]
    have hh (p : Pairing n) : ε q*ε p*column w q p*(ε p*normalizedVacuum w p)=
        ε q*(column w q p*normalizedVacuum w p) := by
      calc
        _=ε q*(ε p*ε p)*(column w q p*normalizedVacuum w p) := by ring
        _=_ := by rw [hε,mul_one]
    simp_rw [hh]
    rw [←Finset.mul_sum]
    exact congrArg (ε q * ·) (congrFun (normalizedVacuum_stationary w hw).2 q)







lemma signSpectral_nodalVacuum {n : ℕ} (k i : Fin n) (p : Pairing (n+1)) :
    signSpectral k (nodalVacuum i p)=nodeSign k i p*nodalVacuum i p := by
  have hcol (p q : Pairing (n+1)) :
      column (fun j => (nodalWeights i j).map (signSpectral k)) q p=
      nodeSign k i q*nodeSign k i p*column (nodalWeights i) q p := by
    rw [signSpectral_nodalWeights]
    by_cases hi:i=k
    · rw [ite_eq_left hi,column_doubleSignTwist _ _ _ (Fin.castSucc_ne_last k).symm]
      simp only [nodeSign,ite_eq_left hi]
    · rw [ite_eq_right hi,column_signTwist]
      simp only [nodeSign,ite_eq_right hi,mul_one]
  have hg:=normalizedVacuum_gauge (nodalWeights i)
    (fun j => (nodalWeights i j).map (signSpectral k)) (nodal_regular i)
    ((nodal_regular i).map (signSpectral k) (nodalWeights i)) (nodeSign k i)
    (nodeSign_square k i) (by simp [nodeSign]) hcol
  have hm:=normalizedVacuum_map (signSpectral k) (nodalWeights i) (nodal_regular i)
  rw [hg] at hm
  rw [nodalVacuum,map_mul,signSpectral_nodalScalar,congrFun hm p]
  ring

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

lemma rationalVacuum_exchange {n : ℕ} (r : ℕ) (hr : r+2≤n)
    : let σ := Equiv.swap (⟨r,by omega⟩ : Fin n) ⟨r+1,by omega⟩;
    rationalVacuum n = (localR (PartialColumn.rowPosition r hr)
      (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩))).mulVec
        (fun p => permSpectral σ (rationalVacuum n p)) := by
  dsimp only
  let σ := Equiv.swap (⟨r,by omega⟩ : Fin n) ⟨r+1,by omega⟩
  have hh (p : Pairing n) : permSpectral σ (rationalVacuum n p)=
      spectralNormalization n * normalizedVacuum (fun i => spectralWeights n (σ i)) p := by
    rw [rationalVacuum,map_mul,permSpectral_normalization,permSpectral_vacuum]
  change rationalVacuum n = (localR (PartialColumn.rowPosition r hr)
    (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩))).mulVec
      (fun p => permSpectral σ (rationalVacuum n p))
  simp_rw [hh]
  change spectralNormalization n • normalizedVacuum (spectralWeights n)=
    (localR (PartialColumn.rowPosition r hr)
      (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩))).mulVec
      (spectralNormalization n • normalizedVacuum (fun i => spectralWeights n (σ i)))
  rw [Matrix.mulVec_smul,←spectral_vacuum_exchange r hr]

lemma nodalVacuum_exchange {n : ℕ} (r : ℕ) (hr : r+2≤n) (i : Fin n)
    : let σ := Equiv.swap (⟨r,by omega⟩ : Fin n) ⟨r+1,by omega⟩;
    nodalVacuum i = (localR (PartialColumn.rowPosition r hr).padTop
      (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩))).mulVec
        (fun p => permSpectral σ (nodalVacuum (σ i) p)) := by
  dsimp only
  let σ := Equiv.swap (⟨r,by omega⟩ : Fin n) ⟨r+1,by omega⟩
  let a : Fin n:=⟨r,by omega⟩
  let b : Fin n:=⟨r+1,by omega⟩
  let z : SpectralField n:=variableF b/variableF a
  let x : Fin (n+1) → SpectralField n :=
    Fin.snoc (fun j => constF n phase^3/variableF j) (constF n phase^3/deletionNode i)
  have xc (j : Fin n) : x j.castSucc=constF n phase^3/variableF j := by
    simp only [x,Fin.snoc_castSucc]
  have hw : (fun j => torusWeights (x j))=nodalWeights i := by
    funext j
    induction j using Fin.lastCases <;> simp [x,nodalWeights,spectralWeights]
  have hp : (PartialColumn.rowPosition r (show r+2≤n+1 by omega))=
      (PartialColumn.rowPosition r hr).padTop := rfl
  have hswap : Equiv.swap (⟨r,by omega⟩ : Fin (n+1)) ⟨r+1,by omega⟩=topPerm σ :=
    (topPerm_swap a b).symm
  have hs : σ (σ i)=i := Equiv.swap_apply_self a b i
  have hreg := nodal_regular_reindex σ (σ i)
  rw [hs] at hreg
  have hx : z*x ⟨r+1,by omega⟩=x ⟨r,by omega⟩ := by
    change z*x b.castSucc=x a.castSucc
    rw [xc,xc]
    dsimp only [z]
    field_simp [variableF_ne_zero]
  have hL (j : Fin n) : torusL (x j.castSucc)≠0 := by
    rw [xc]
    rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero j
  have H:=normalizedVacuum_torus_exchange r (show r+2≤n+1 by omega) x z
    (div_ne_zero (variableF_ne_zero b) (variableF_ne_zero a))
    (by change x b.castSucc≠0; rw [xc]; exact div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) (variableF_ne_zero b))
    (torusL_ratio_ne_zero a b) (hL b) (hL a) hx
    (by rw [hw]; exact nodal_regular i)
    (by change VacuumRegular (fun j => (fun k => torusWeights (x k)) (Equiv.swap _ _ j));
        rw [hw,hswap]; exact hreg)
  rw [hw,hswap,hp] at H
  have hwpoint (j : Fin (n+1)) := congrFun hw j
  simp_rw [hwpoint] at H
  have hv (p : Pairing (n+1)) : permSpectral σ (nodalVacuum (σ i) p)=
      nodalScalar i*normalizedVacuum (fun j => nodalWeights i (topPerm σ j)) p := by
    rw [permSpectral_nodalVacuum,hs]
  change nodalVacuum i = (localR (PartialColumn.rowPosition r hr).padTop
    (torusWeights z)).mulVec (fun p => permSpectral σ (nodalVacuum (σ i) p))
  simp_rw [hv]
  change nodalScalar i • normalizedVacuum (nodalWeights i)=
    (localR (PartialColumn.rowPosition r hr).padTop (torusWeights z)).mulVec
      (nodalScalar i • normalizedVacuum (fun j => nodalWeights i (topPerm σ j)))
  rw [Matrix.mulVec_smul,←H]

end

 

 

noncomputable section
open scoped Classical
open Finset

lemma nodalExchangePolynomial_leading {n : ℕ} (r : ℕ) (hr : r+2≤n) (p : Pairing n) :
    (nodalExchangePolynomial r hr p.padTop).coeff n=rationalVacuum n p := by
  rw [nodalExchangePolynomial_coeff]
  rw [congrFun (rationalVacuum_exchange r hr) p]
  simp only [Matrix.mulVec,dotProduct]
  symm
  apply Fintype.sum_of_injective Pairing.padTop Pairing.padTop_injective
  · intro q hq
    rw [localR_padTop_outside _ _ q p hq,zero_mul]
  · intro q
    rw [localR_padTop,rationalNodalPolynomial_leading]

lemma nodalExchangePolynomial_node {n : ℕ} (r : ℕ) (hr : r+2≤n)
    (p : Pairing (n+1)) (i : Fin n) :
    (if p.Occupied (Fin.last n) then torusSin (deletionNode i) else 1) *
      (nodalExchangePolynomial r hr p).eval (deletionBeta i) =nodalVacuum i p := by
  let σ := Equiv.swap (⟨r,by omega⟩ : Fin n) ⟨r+1,by omega⟩
  have hσ (j : Fin n) : σ (σ j)=j := Equiv.swap_apply_self _ _ _
  have hβ : permSpectral σ (deletionBeta (σ i))=deletionBeta i := by
    rw [permSpectral_deletionBeta,hσ]
  have hsin : permSpectral σ (torusSin (deletionNode (σ i)))=torusSin (deletionNode i) := by
    simp only [permSpectral_torusSin,permSpectral_deletionNode,hσ]
  rw [congrFun (nodalVacuum_exchange r hr i) p]
  simp only [nodalExchangePolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,mul_sum,Matrix.mulVec,dotProduct]
  apply sum_congr rfl
  intro q _
  change (if p.Occupied (Fin.last n) then torusSin (deletionNode i) else 1) *
    (localR _ _ p q * ((rationalNodalPolynomial n q).map (permSpectral σ)).eval (deletionBeta i)) =
      localR _ _ p q * permSpectral σ (nodalVacuum (σ i) q)
  by_cases hh : p.Occupied (Fin.last n) ↔ q.Occupied (Fin.last n)
  · rw [hh,←rationalNodalPolynomial_at_node q (σ i),map_mul]
    rw [←hβ,Polynomial.eval_map_apply]
    have hs : permSpectral σ (if q.Occupied (Fin.last n) then torusSin (deletionNode (σ i)) else 1)=
        (if q.Occupied (Fin.last n) then torusSin (deletionNode i) else 1) := by
      split_ifs <;> simp only [hsin,map_one]
    rw [hs]
    ring
  · rw [localR_padTop_zero_last _ _ q p hh,zero_mul,mul_zero,zero_mul]

 

theorem rationalNodalPolynomial_covariance {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    rationalNodalPolynomial n=nodalExchangePolynomial r hr := by
  apply lastPolynomial_unique _ _ (rationalNodalPolynomial_degree n)
    (nodalExchangePolynomial_degree r hr) deletionBeta (deletionBeta_injective n)
  · intro p
    rw [rationalNodalPolynomial_leading,nodalExchangePolynomial_leading]
  · intro p i
    have h := (rationalNodalPolynomial_at_node p i).trans
      (nodalExchangePolynomial_node r hr p i).symm
    apply mul_left_cancel₀ _ h
    split_ifs
    · exact deletionNode_sine_ne_zero i
    · exact one_ne_zero

end

 

 

noncomputable section
open scoped Classical

lemma signSpectral_nodal_eval {n : ℕ} (k i : Fin n) (p : Pairing (n+1)) :
    ((rationalNodalPolynomial n p).map (signSpectral k)).eval (deletionBeta i)=
      occupancySign p k.castSucc*(rationalNodalPolynomial n p).eval (deletionBeta i) := by
  have hh:=congrArg (signSpectral k) (rationalNodalPolynomial_at_node p i)
  rw [map_mul,signSpectral_nodalVacuum] at hh
  have hev : signSpectral k ((rationalNodalPolynomial n p).eval (deletionBeta i))=
      ((rationalNodalPolynomial n p).map (signSpectral k)).eval (deletionBeta i) := by
    rw [←Polynomial.eval_map_apply,signSpectral_deletionBeta]
  rw [hev,←rationalNodalPolynomial_at_node p i] at hh
  by_cases hp:p.Occupied (Fin.last n)
  · have hs : occupancySign (K:=SpectralField n) p (Fin.last n)= -1 := by simp [occupancySign,hp]
    simp only [hp,ite_true,signSpectral_torusSin,signSpectral_deletionNode,nodeSign,hs] at hh
    by_cases hi:i=k
    · simp only [ite_eq_left hi,torusSin_neg] at hh
      apply mul_left_cancel₀ (deletionNode_sine_ne_zero i)
      linear_combination -hh
    · simp only [ite_eq_right hi,mul_one] at hh
      apply mul_left_cancel₀ (deletionNode_sine_ne_zero i)
      linear_combination hh
  · have hs : occupancySign (K:=SpectralField n) p (Fin.last n)=1 := by simp [occupancySign,hp]
    simpa only [hp,ite_false,map_one,one_mul,nodeSign,hs,ite_self,mul_one] using hh

 

theorem rationalNodalPolynomial_parity {n : ℕ} (k : Fin n) (p : Pairing (n+1)) :
    (rationalNodalPolynomial n p).map (signSpectral k)=
      Polynomial.C (occupancySign p k.castSucc)*rationalNodalPolynomial n p := by
  have h: (fun p : Pairing (n+1) => (rationalNodalPolynomial n p).map (signSpectral k))=
      (fun p => Polynomial.C (occupancySign p k.castSucc)*rationalNodalPolynomial n p) := by
    apply lastPolynomial_unique
    · intro p j hj
      rw [Polynomial.coeff_map,rationalNodalPolynomial_degree n p j hj,map_zero]
    · intro p j hj
      rw [Polynomial.coeff_C_mul,rationalNodalPolynomial_degree n p j hj,mul_zero]
    case v => exact deletionBeta
    case hv => exact deletionBeta_injective n
    · intro p
      rw [Polynomial.coeff_map,Polynomial.coeff_C_mul,rationalNodalPolynomial_leading,
        rationalVacuum_sign]
      simp [occupancySign]
    · intro p i
      rw [Polynomial.eval_mul,Polynomial.eval_C]
      exact signSpectral_nodal_eval k i p
  exact congrFun h p







lemma nodalDatumL_map_eval {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (i : Fin (n+1)) (p : Pairing (n+2)) :
    evalLaurent (nodalDatumL W i p)=(rationalNodalPolynomial (n+1) p).eval (deletionBeta i) := by
  rw [nodalDatumL_map W hW,rationalNodalPolynomial_eval_div]

lemma nodalDatumL_sign {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (k i : Fin (n+1)) (p : Pairing (n+2)) :
    signLaurent k (nodalDatumL W i p)=
      (if p.Occupied k.castSucc then -nodalDatumL W i p else nodalDatumL W i p) := by
  apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
  change evalLaurent (signLaurent k (nodalDatumL W i p))=evalLaurent _
  rw [←signSpectral_evalLaurent,nodalDatumL_map_eval W hW]
  have h:=signSpectral_nodal_eval k i p
  rw [←Polynomial.eval_map_apply,signSpectral_deletionBeta,h]
  split_ifs with hp
  · simp only [evalLaurent,map_neg,occupancySign,hp,ite_true,neg_one_mul]
    rw [←evalLaurent,nodalDatumL_map_eval W hW]
  · simp only [occupancySign,hp,ite_false,one_mul]
    rw [nodalDatumL_map_eval W hW]

end

 

 

noncomputable section






open Finset
open scoped Classical



theorem rationalVacuum_stationary (n : ℕ) :
    (column (spectralWeights n)).mulVec (rationalVacuum n) = rationalVacuum n := by
  change (column (spectralWeights n)).mulVec
    (spectralNormalization n • normalizedVacuum (spectralWeights n)) =
      spectralNormalization n • normalizedVacuum (spectralWeights n)
  rw [Matrix.mulVec_smul, (spectral_normalizedVacuum_stationary n).2]



theorem rationalResidualPolynomial_at_node {n : ℕ} (p : Pairing (n+1)) (i : Fin n) :
    (rationalResidualPolynomial n p).eval (deletionBeta i) = 0 := by
  have hz : deletionNode i ≠ 0 := mul_ne_zero (variableF_ne_zero i)
    (pow_ne_zero _ (constF_phase_ne_zero n))
  have harg : constF n phase^3 / deletionNode i = (variableF i)⁻¹ := by
    unfold deletionNode
    field_simp [constF_phase_ne_zero]
  have hL : torusL (constF n phase^3 / deletionNode i) ≠ 0 := by
    rw [harg, ← inverseRowDenominator_map]
    exact inverseRowDenominator_map_ne_zero i
  have he := torus_column_lastValue (spectralWeights n) (deletionNode i) hz hL
    (rationalNodalPolynomial n)
  have hdata : lastValue (RingHom.id _) (deletionBeta i) (torusSin (deletionNode i))
      (rationalNodalPolynomial n) = nodalVacuum i := by
    funext q
    simpa only [lastValue, Polynomial.eval₂_id, ite_mul, one_mul] using
      rationalNodalPolynomial_at_node q i
  change (deletionBeta i + constF n C) •
    (column (nodalWeights i)).mulVec
      (lastValue (RingHom.id _) (deletionBeta i) (torusSin (deletionNode i))
        (rationalNodalPolynomial n)) = _ at he
  rw [hdata, nodalVacuum_stationary] at he
  have hep := congrFun he p
  simp only [Pi.smul_apply, smul_eq_mul] at hep
  rw [← congrFun hdata p] at hep
  change (deletionBeta i + constF n C) *
    lastValue (RingHom.id _) (deletionBeta i) (torusSin (deletionNode i))
      (rationalNodalPolynomial n) p =
    lastValue (RingHom.id _) (deletionBeta i) (torusSin (deletionNode i))
      (lastTransform (fun i => (spectralWeights n i).tile) (constF n d) (constF n c)
        (constF n C) (rationalNodalPolynomial n)) p at hep
  by_cases hp : p.Occupied (Fin.last n)
  · simp only [lastValue, hp, ite_true, Polynomial.eval₂_id] at hep
    have hc := deletionNode_sine_ne_zero i
    rw [rationalResidualPolynomial, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    apply sub_eq_zero.mpr
    apply mul_left_cancel₀ hc
    calc
      _ = (deletionBeta i + constF n C) *
          (torusSin (deletionNode i) * (rationalNodalPolynomial n p).eval (deletionBeta i)) := hep.symm
      _ = _ := by ring
  · simp only [lastValue, hp, ite_false, Polynomial.eval₂_id] at hep
    simp only [rationalResidualPolynomial, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_eq_zero.mpr hep.symm



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
open scoped Classical



theorem copiedNode_regular {m n : ℕ} (v : Fin m → Fin n) (i : Fin n) :
    VacuumRegular (copiedNodeWeights v i) := by
  apply regular_of_cleared_specialization
    (algebraMap (SpectralRing n) (SpectralField n))
    (IsFractionRing.injective (SpectralRing n) (SpectralField n)) (flatEval n).toRingHom
    (Fin.snoc (fun j => rowDenominator (v j)) (inverseRowDenominator i))
    (Fin.snoc (fun j => rowNumerator (v j)) (inverseRowNumerator i))
    (copiedNodeWeights v i) (Fin.snoc (fun _ => deletionWeights) identityWeights)
  · intro j
    induction j using Fin.lastCases with
    | last => simpa using inverseRowDenominator_flat_ne_zero i
    | cast j => simpa using flatEval_rowDenominator_ne_zero (v j)
  · intro j t
    induction j using Fin.lastCases with
    | last => simpa only [evalLaurent,copiedNodeWeights,Fin.snoc_last] using inverseRowNumerator_map i t
    | cast j => simpa only [copiedNodeWeights,Fin.snoc_castSucc] using rowNumerator_map (v j) t
  · intro j t
    induction j using Fin.lastCases with
    | last => simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Fin.snoc_last]
        using inverseRowNumerator_flat i t
    | cast j => simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Fin.snoc_castSucc]
        using rowNumerator_flatEval (v j) t
  · unfold VacuumRegular
    rw [det_one_nonflat]
    · exact one_ne_zero
    · intro j k hj hk
      induction j using Fin.lastCases with
      | last => exact (hj (Or.inl (Fin.snoc_last ..))).elim
      | cast j => exact (hj (Or.inr (Fin.snoc_castSucc ..))).elim

lemma rationalAt_copy_vacuum {m n : ℕ} (v : Fin m → Fin n) (i : Fin m) (p : Pairing (m+1)) :
    RationalAt (copyEvaluation v).toRingHom
      (normalizedVacuum (nodalWeights i) p)
      (normalizedVacuum (copiedNodeWeights v (v i)) p) :=
  rationalAt_normalizedVacuum _ _ (rationalAt_copy_weights v i) (copiedNode_regular v (v i)) p







lemma rationalAt_copy_nodalVacuum {m n : ℕ} (v : Fin m → Fin n) (i : Fin m)
    (p : Pairing (m+1)) :
    RationalAt (copyEvaluation v).toRingHom (nodalVacuum i p)
      (copiedNodeScalar v (v i)*normalizedVacuum (copiedNodeWeights v (v i)) p) :=
  (rationalAt_copy_scalar v i).mul (rationalAt_copy_vacuum v i p)

 

theorem nodalVacuum_collision {m n : ℕ} (v : Fin m → Fin n) (i j : Fin m)
    (hij:v i=v j) (p : Pairing (m+1)) :
    ∃ y : SpectralField n,
      RationalAt (copyEvaluation v).toRingHom (nodalVacuum i p) y ∧
      RationalAt (copyEvaluation v).toRingHom (nodalVacuum j p) y := by
  refine ⟨_,rationalAt_copy_nodalVacuum v i p,?_⟩
  rw [hij]
  exact rationalAt_copy_nodalVacuum v j p

 
theorem occupied_nodal_collision {m n : ℕ} (v : Fin m → Fin n) (i j : Fin m)
    (hij:v i=v j) (p : Pairing (m+1)) :
    ∃ y : SpectralField n,
      RationalAt (copyEvaluation v).toRingHom (nodalVacuum i p/torusSin (deletionNode i)) y ∧
      RationalAt (copyEvaluation v).toRingHom (nodalVacuum j p/torusSin (deletionNode j)) y := by
  have hi:=rationalAt_torusSin (copyEvaluation v) (rationalAt_copy_deletionNode v i)
    (mul_ne_zero (variableF_ne_zero (v i)) (pow_ne_zero _ (constF_phase_ne_zero n)))
  have hj:=rationalAt_torusSin (copyEvaluation v) (rationalAt_copy_deletionNode v j)
    (mul_ne_zero (variableF_ne_zero (v j)) (pow_ne_zero _ (constF_phase_ne_zero n)))
  obtain ⟨y,hy,hz⟩:=nodalVacuum_collision v i j hij p
  refine ⟨y/torusSin (deletionNode (v i)),hy.div hi (deletionNode_sine_ne_zero _),?_⟩
  rw [hij]
  exact hz.div hj (deletionNode_sine_ne_zero _)

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CollisionSubstitutions
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

lemma nodalDatumL_copy_collision {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (i : Fin (n+1)) (j : Fin n) (p : Pairing (n+2)) :
    copyEvaluation (collisionCopy i j) (nodalDatumL W i p)=
      copyEvaluation (collisionCopy i j) (nodalDatumL W (i.succAbove j) p) := by
  have hij:collisionCopy i j i=collisionCopy i j (i.succAbove j) := by
    simp only [collisionCopy,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,id_eq]
  have hm (k : Fin (n+1)) :
      RationalAt (copyEvaluation (collisionCopy i j)).toRingHom
        (nodalVacuum k p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode k) else 1))
        (copyEvaluation (collisionCopy i j) (nodalDatumL W k p)) := by
    rw [←nodalDatumL_map W hW k p]
    exact RationalAt.algebraMap _
  by_cases hp:p.Occupied (Fin.last (n+1))
  · obtain ⟨y,hy,hz⟩:=occupied_nodal_collision (collisionCopy i j) i (i.succAbove j) hij p
    have hmi:=hm i
    have hmj:=hm (i.succAbove j)
    simp only [hp,ite_true] at hmi hmj
    exact (hmi.unique hy).trans (hmj.unique hz).symm
  · obtain ⟨y,hy,hz⟩:=nodalVacuum_collision (collisionCopy i j) i (i.succAbove j) hij p
    have hmi:=hm i
    have hmj:=hm (i.succAbove j)
    simp only [hp,ite_false,div_one] at hmi hmj
    exact (hmi.unique hy).trans (hmj.unique hz).symm

lemma nodalDatumL_ordinary_collision {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (i : Fin (n+1)) (j : Fin n) (p : Pairing (n+2)) :
    substituteLaurent i (variableUnit j) (nodalDatumL W i p)=
      substituteLaurent i (variableUnit j) (nodalDatumL W (i.succAbove j) p) := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  exact (copyEvaluation_collision i j _).symm.trans
    ((nodalDatumL_copy_collision W hW i j p).trans (copyEvaluation_collision i j _))







lemma nodalDatumL_collision {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (i : Fin (n+1)) (j : Fin n)
    (p : Pairing (n+2)) (k : Fin 4) :
    collisionSubstitution i j k (nodalDatumL W i p)=
      collisionSubstitution i j k (nodalDatumL W (i.succAbove j) p) := by
  have ho:=nodalDatumL_ordinary_collision W hW i j p
  have hr:=nodalDatumL_reflection W i j p
  fin_cases k
  · exact ho
  · change substituteLaurent i (-(variableUnit j)) _=substituteLaurent i (-(variableUnit j)) _
    rw [substituteLaurent_neg_sign,substituteLaurent_neg_sign,
      nodalDatumL_sign W hW,nodalDatumL_sign W hW]
    split_ifs <;> simp only [map_neg,ho]
  · exact hr.1.trans hr.2.symm
  · change substituteLaurent i (-(reflectionUnit j)) _=substituteLaurent i (-(reflectionUnit j)) _
    rw [substituteLaurent_neg_sign,substituteLaurent_neg_sign,
      nodalDatumL_sign W hW,nodalDatumL_sign W hW]
    split_ifs <;> simp only [map_neg,hr.1,hr.2]

lemma interpolationNumerator_collisionSubstitution {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (i : Fin (n+1)) (j : Fin n)
    (p : Pairing (n+2)) (k : Fin 4) (a : Fin (n+1)) :
    collisionSubstitution i j k
      (interpolationNumerator betaL (fun l => nodalDatumL W l p) a)=0 := by
  rw [interpolationNumerator_map]
  apply interpolationNumerator_collision _ _ i (i.succAbove j) (Fin.succAbove_ne i j).symm
  · rw [collisionSubstitution_beta_self,collisionSubstitution_beta]
    simp only [collisionCopy,Fin.insertNth_apply_succAbove,id_eq]
  · exact nodalDatumL_collision W hW i j p k







theorem nodal_vandermonde_dvd {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (p : Pairing (n+2)) (a : Fin (n+1)) :
    (Matrix.vandermonde (@betaL (n+1))).det ∣
      interpolationNumerator betaL (fun l => nodalDatumL W l p) a := by
  rw [Matrix.det_vandermonde,←prod_upperPair]
  apply prod_dvd_of_evaluation_packets Finset.univ _ edgeSubstitution
  · intro e _ f hf
    exact edgeSubstitution_kernel e f hf
  · intro e _ f _ hef k
    exact edgeSubstitution_cross e f hef k
  · intro e _ k
    exact interpolationNumerator_collisionSubstitution W hW e.val.1 (upperPairOther e) p k a









lemma nodalLow_laurent {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (p : Pairing (n+2)) :
    ∃ P : Polynomial (Laurent (n+1)),P.map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=
      Lagrange.interpolate Finset.univ deletionBeta
        (fun i => nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1)) := by
  have hbmap (i:Fin (n+1)) : (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (betaL i)=deletionBeta i := betaL_map i
  have hdmap (i:Fin (n+1)) : (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (nodalDatumL W i p)=
      nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1) := nodalDatumL_map W hW i p
  have hh:=interpolate_lift_of_vandermonde_dvd
    (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))
    betaL (fun i => nodalDatumL W i p)
    (by simpa only [hbmap] using deletionBeta_injective (n+1))
    (nodal_vandermonde_dvd W hW p)
  simpa only [hbmap,hdmap] using hh

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

lemma nodalLow_laurent_box {n:ℕ} (W:Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p)
    (hb:∀ p,LaurentBox (W p) (fun _ => 2*n-2)) (p:Pairing (n+2)) :
    ∃ P:Polynomial (Laurent (n+1)),
      P.map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=
        Lagrange.interpolate Finset.univ deletionBeta
          (fun i => nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1)) ∧
      PolynomialBox P (fun _ => 2*n+2) := by
  let φ:=algebraMap (SpectralRing (n+1)) (SpectralField (n+1))
  obtain ⟨P,hP⟩:=nodalLow_laurent W hW p
  refine ⟨P,hP,?_⟩
  intro a
  have hcoef:φ (P.coeff a)=
      (Lagrange.interpolate Finset.univ deletionBeta
        (fun i => nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1))).coeff a := by
    rw [←hP,Polynomial.coeff_map]
  by_cases ha:a<n+1
  · have he:interpolationNumerator betaL (fun i => nodalDatumL W i p) ⟨a,ha⟩=
        (Matrix.vandermonde (@betaL (n+1))).det*P.coeff a := by
      apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
      rw [map_mul,hcoef,interpolationNumerator_map,RingHom.map_det]
      have hbmap (i:Fin (n+1)):φ (betaL i)=deletionBeta i := betaL_map i
      have hdmap (i:Fin (n+1)):φ (nodalDatumL W i p)=
          nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1) :=
        nodalDatumL_map W hW i p
      change interpolationNumerator (fun i => φ (betaL i)) (fun i => φ (nodalDatumL W i p)) ⟨a,ha⟩=_
      simp only [hbmap,hdmap]
      rw [interpolationNumerator_eq_det_mul_coeff _ _ (deletionBeta_injective (n+1))]
      congr 2
      ext i j
      change deletionBeta i ^ j.val=φ (betaL i ^ j.val)
      rw [map_pow,hbmap]
    apply LaurentBox.of_peel
    intro k
    have hn:LaurentInterval (peelLaurent k (P.coeff a)*peelLaurent k (Matrix.vandermonde (@betaL (n+1))).det)
        (-(4*n+2:ℤ)) (4*n+2) := by
      have hh:=(interpolationNumerator_box W hb p ⟨a,ha⟩).peel k
      rw [he,map_mul,mul_comm] at hh
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh
    obtain ⟨hg,hlo,hhi⟩:=vandermonde_beta_exact k
    have hq:=hn.quotient hg hlo hhi
    convert hq using 1 <;> push_cast <;> ring
  · have he:P.coeff a=0 := by
      apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
      rw [hcoef,map_zero]
      apply Polynomial.coeff_eq_zero_of_degree_lt
      have hh:=Lagrange.degree_interpolate_lt (s:=Finset.univ)
        (fun i => nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1))
        (deletionBeta_injective (n+1)).injOn
      simp only [Finset.card_univ,Fintype.card_fin] at hh
      exact hh.trans_le (by exact_mod_cast (show n+1≤a by omega))
    rw [he]
    exact LaurentBox.zero _

end

 

 

noncomputable section
open scoped Classical

lemma nodal_betaL_box {n:ℕ} : PolynomialBox (Lagrange.nodal Finset.univ (@betaL n)) (fun _ => 2) := by
  unfold Lagrange.nodal
  have h:=PolynomialBox.prod Finset.univ
    (fun i:Fin n => Polynomial.X-Polynomial.C (betaL i)) (fun i => selfBound i 2)
    (fun i _ => (PolynomialBox.X.mono (fun k => Nat.zero_le _)).sub (PolynomialBox.C (betaL_box i)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext k
  simp only [Finset.sum_apply,selfBound,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

 

lemma rationalNodalPolynomial_laurent_box {n:ℕ}
    (W:Pairing n → Laurent n) (V:Pairing (n+1) → Laurent (n+1))
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p)
    (hV:∀ p,evalLaurent (V p)=rationalVacuum (n+1) p)
    (bW:∀ p,LaurentBox (W p) (fun _ => 2*n-2))
    (bV:∀ p,LaurentBox (V p) (fun _ => 2*n)) (p:Pairing (n+2)) :
    ∃ P:Polynomial (Laurent (n+1)),
      P.map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p ∧
      PolynomialBox P (fun _ => 2*n+2) := by
  obtain ⟨P,hP,bP⟩:=nodalLow_laurent_box W hW bW p
  by_cases hp:p.Occupied (Fin.last (n+1))
  · refine ⟨P,?_,bP⟩
    simpa only [rationalNodalPolynomial,hp,ite_true] using hP
  · refine ⟨Polynomial.C (V (p.restrict Fin.castSuccOrderEmb))*Lagrange.nodal Finset.univ betaL+P,?_,?_⟩
    · simp only [rationalNodalPolynomial,hp,ite_false,Polynomial.map_add,Polynomial.map_mul,
        Polynomial.map_C,hP,div_one]
      rw [show (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (V (p.restrict Fin.castSuccOrderEmb))=
        rationalVacuum (n+1) (p.restrict Fin.castSuccOrderEmb) from hV _]
      congr 2
      have hbmap (i:Fin (n+1)) : (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (betaL i)=deletionBeta i := betaL_map i
      simp only [Lagrange.nodal,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,
        Polynomial.map_C,hbmap]
    · exact ((PolynomialBox.C (bV _)).mul nodal_betaL_box).add bP

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

lemma rationalInterpolant_parity {n:ℕ} (i:Fin n) (p:Pairing (n+1)) :
    signSpectral i.castSucc (rationalInterpolant n p)=occupancySign p i.castSucc*rationalInterpolant n p := by
  have hp:=congrArg (fun P:Polynomial (SpectralField n) => P.eval₂ (liftSpectral n) (spectralA (Fin.last n)))
    (rationalNodalPolynomial_parity i p)
  simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C] at hp
  have ho:liftSpectral n (occupancySign (K:=SpectralField n) p i.castSucc)=occupancySign p i.castSucc := by
    simp only [occupancySign]; split_ifs <;> simp
  rw [ho] at hp
  have hm:(signSpectral i.castSucc).comp (liftSpectral n)=(liftSpectral n).comp (signSpectral i) :=
    RingHom.ext (signSpectral_lift i)
  have hev:signSpectral i.castSucc ((rationalNodalPolynomial n p).eval₂ (liftSpectral n) (spectralA (Fin.last n)))=
      ((rationalNodalPolynomial n p).map (signSpectral i)).eval₂ (liftSpectral n) (spectralA (Fin.last n)) := by
    rw [Polynomial.hom_eval₂,hm,Polynomial.eval₂_map,signSpectral_spectralA]
  unfold rationalInterpolant
  rw [map_mul,hev,hp]
  have hs:signSpectral i.castSucc (torusSin (variableF (Fin.last n)))=torusSin (variableF (Fin.last n)) := by
    rw [signSpectral_torusSin,signSpectral_variable,ite_eq_right (Ne.symm (Fin.castSucc_ne_last i))]
  split_ifs <;> simp only [hs,map_one] <;> ring

theorem rationalInterpolationResidual_parity {n:ℕ} (i:Fin n) (p:Pairing (n+1)) :
    signSpectral i.castSucc (rationalInterpolationResidual n p)=
      occupancySign p i.castSucc*rationalInterpolationResidual n p := by
  have hc:signSpectral i.castSucc ((column (spectralWeights (n+1))).mulVec (rationalInterpolant n) p)=
      occupancySign p i.castSucc*(column (spectralWeights (n+1))).mulVec (rationalInterpolant n) p := by
    simp only [Matrix.mulVec,dotProduct,map_sum,map_mul,signSpectral_column,rationalInterpolant_parity,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    calc
      _=occupancySign p i.castSucc*(occupancySign q i.castSucc*occupancySign q i.castSucc)*
        (column (spectralWeights (n+1)) p q*rationalInterpolant n q) := by ring
      _=_ := by rw [occupancySign_mul_self,mul_one]
  rw [rationalInterpolationResidual,map_mul,map_sub,map_prod]
  simp_rw [signSpectral_rowDenominator]
  rw [hc,rationalInterpolant_parity]
  ring

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



theorem rationalInterpolant_covariance {n:ℕ} (r:ℕ) (hr:r+2≤n) :
    rationalInterpolant n=
      (localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF (⟨r+1,by omega⟩:Fin n).castSucc /
          variableF (⟨r,by omega⟩:Fin n).castSucc))).mulVec
      (fun p =>permSpectral (topPerm (Equiv.swap (⟨r,by omega⟩:Fin n) ⟨r+1,by omega⟩)) (rationalInterpolant n p)) := by
  let σ:=Equiv.swap (⟨r,by omega⟩:Fin n) ⟨r+1,by omega⟩
  let a:=PartialColumn.rowPosition r hr
  let w:=torusWeights (variableF (⟨r+1,by omega⟩:Fin n)/variableF (⟨r,by omega⟩:Fin n))
  have hw:w.map (liftSpectral n)=torusWeights (variableF (⟨r+1,by omega⟩:Fin n).castSucc/variableF (⟨r,by omega⟩:Fin n).castSucc) := by
    simp only [w,torusWeights,Weights.map,map_div₀,map_mul,map_pow,liftSpectral_const,liftSpectral_variable,
      liftSpectral_torusSin,torusL,map_mul,map_pow,liftSpectral_const,
      liftSpectral_torusSin,map_div₀,liftSpectral_variable]
  have hM:(localR a.padTop w).map (liftSpectral n)=localR a.padTop (w.map (liftSpectral n)):=localR_map_hom _ _ _
  funext p
  have hp:=congrArg (fun P:Polynomial (SpectralField n) =>P.eval₂ (liftSpectral n) (spectralA (Fin.last n)))
    (congrFun (rationalNodalPolynomial_covariance r hr) p)
  simp only [nodalExchangePolynomial,Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,Polynomial.eval₂_C] at hp
  simp_rw [permSpectral_interpolant]
  change (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last n)) else 1)*
    (rationalNodalPolynomial n p).eval₂ (liftSpectral n) (spectralA (Fin.last n))=_
  rw [hp,Finset.mul_sum]
  simp only [Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro q _
  have he:liftSpectral n (localR a.padTop w p q)=localR a.padTop (w.map (liftSpectral n)) p q := congrFun (congrFun hM p) q
  change _ * (liftSpectral n (localR a.padTop w p q)*_)=_
  rw [he,hw]
  by_cases ho:p.Occupied (Fin.last n) ↔ q.Occupied (Fin.last n)
  · simp only [ho]; ring
  · have hh:=localR_padTop_zero_last a (w.map (liftSpectral n)) q p ho
    rw [hw] at hh
    rw [hh,zero_mul,mul_zero,zero_mul]

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








open Finset
open scoped Classical



theorem normalizedVacuum_firstZero {K : Type*} [Field K] {n : ℕ}
    (w : Fin n → Weights K) (hw : VacuumRegular w) :
    normalizedVacuum (Fin.cons deletionWeights w) =
      firstZeroRaw (fun i => (w i).tile) (normalizedVacuum w) := by
  have hs := normalizedVacuum_stationary w hw
  have hr : VacuumRegular (Fin.cons deletionWeights w) := by
    unfold VacuumRegular
    rw [det_flat_bottom _ (Or.inr rfl)]
    exact hw
  symm
  apply normalizedVacuum_unique _ hr
  constructor
  · rw [← Pairing.padBottom_empty, firstZeroRaw_vacant]
    change (column w).mulVec (normalizedVacuum w) (empty n) = 1
    rw [hs.2, hs.1]
  · rw [deletion_column_mulVec]
    congr 1
    funext p
    rw [firstZeroRaw_vacant]
    exact congrFun hs.2 p


theorem firstZeroPolynomial_leading {K : Type*} [CommRing K] {n m : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) (hP : LastDegree m P) (q : Pairing (n+1)) :
    (firstZeroPolynomial w d c C P q.padTop).coeff (m+1) =
      firstZeroRaw w (fun p => (P p.padTop).coeff m) q := by
  rw [firstZeroPolynomial, lastTransform_leading _ _ _ _ _ hP.vacantBottomExtension,
    vacantBottomExtension_leading]
  rfl

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FirstFlatSpecialization
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

lemma firstFlatSmaller_regular (n : ℕ) (i : Fin (n+1)) :
    VacuumRegular (firstFlatSmallerWeights n i) := by
  induction i using Fin.cases with
  | zero =>
      unfold VacuumRegular firstFlatSmallerWeights
      simp only [Fin.cons_zero]
      rw [det_flat_top _ (Or.inl (Fin.snoc_last ..))]
      simpa only [firstFlatSmallerWeights,Fin.cons_zero,Fin.snoc_castSucc,VacuumRegular] using spectral_regular n
  | succ i => exact nodal_regular i

lemma rationalAt_firstFlat_normalizedVacuum {n : ℕ} (i : Fin (n+1)) (p : Pairing (n+2)) :
    RationalAt (firstFlatEvaluation n).toRingHom (normalizedVacuum (nodalWeights i) p)
      (firstZeroRaw (fun j => (firstFlatSmallerWeights n i j).tile)
        (normalizedVacuum (firstFlatSmallerWeights n i)) p) := by
  have hr : VacuumRegular (Fin.cons deletionWeights (firstFlatSmallerWeights n i)) := by
    unfold VacuumRegular
    rw [det_flat_bottom _ (Or.inr rfl)]
    exact firstFlatSmaller_regular n i
  have h:=rationalAt_normalizedVacuum _ _ (rationalAt_firstFlat_nodalWeights i) hr p
  rw [normalizedVacuum_firstZero _ (firstFlatSmaller_regular n i)] at h
  exact h







lemma rationalAt_firstFlat_nodalVacuum {n : ℕ} (i : Fin (n+1)) (p : Pairing (n+2)) :
    RationalAt (firstFlatEvaluation n).toRingHom (nodalVacuum i p)
      (((∏ j : Fin n, (spectralA j+constF n C))*
        (((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)+constF n C)*
        firstFlatSmallerScalar n i)*
        firstZeroRaw (fun j => (firstFlatSmallerWeights n i j).tile)
          (normalizedVacuum (firstFlatSmallerWeights n i)) p) :=
  (rationalAt_firstFlat_nodalScalar i).mul (rationalAt_firstFlat_normalizedVacuum i p)







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

lemma spectral_column_exchange {n:ℕ} (r:ℕ) (hr:r+2≤n) :
    column (spectralWeights n)*localR (PartialColumn.rowPosition r hr)
          (torusWeights (variableF ⟨r+1,by omega⟩/variableF ⟨r,by omega⟩))=
      localR (PartialColumn.rowPosition r hr)
          (torusWeights (variableF ⟨r+1,by omega⟩/variableF ⟨r,by omega⟩))*
        (column (spectralWeights n)).map (permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)) := by
  rw [permSpectral_column_map]
  apply PartialColumn.torus_column_exchange r hr (fun i =>constF n phase^3/variableF i)
  · exact div_ne_zero (variableF_ne_zero _) (variableF_ne_zero _)
  · exact div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) (variableF_ne_zero _)
  · exact torusL_ratio_ne_zero _ _
  · rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero _
  · rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero _
  · field_simp [variableF_ne_zero]


theorem rationalInterpolationResidual_covariance {n:ℕ} (r:ℕ) (hr:r+2≤n) :
    rationalInterpolationResidual n=
      (localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF (⟨r+1,by omega⟩:Fin n).castSucc / variableF (⟨r,by omega⟩:Fin n).castSucc))).mulVec
      (fun p =>permSpectral (topPerm (Equiv.swap (⟨r,by omega⟩:Fin n) ⟨r+1,by omega⟩)) (rationalInterpolationResidual n p)) := by
  let σ:=topPerm (Equiv.swap (⟨r,by omega⟩:Fin n) ⟨r+1,by omega⟩)
  let R:=localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF (⟨r+1,by omega⟩:Fin n).castSucc / variableF (⟨r,by omega⟩:Fin n).castSucc))
  have he: column (spectralWeights (n+1))*R=R*(column (spectralWeights (n+1))).map (permSpectral σ) := by
    simpa only [R,σ,topPerm_swap,PartialColumn.rowPosition,Position.padTop,Fin.castSucc_mk] using
      spectral_column_exchange (n:=n+1) r (by omega)
  have hmap: (fun p =>permSpectral σ (rationalInterpolationResidual n p))=
      fun p =>(∏i:Fin (n+1),evalLaurent (rowDenominator i))*
        (((column (spectralWeights (n+1))).map (permSpectral σ)).mulVec
          (fun q =>permSpectral σ (rationalInterpolant n q)) p-permSpectral σ (rationalInterpolant n p)) := by
    funext p
    simp only [rationalInterpolationResidual,map_mul,map_sub,permSpectral_rowProduct,
      Matrix.mulVec,dotProduct,map_sum,Matrix.map_apply]
  rw [hmap]
  exact matrix_residual_covariance _ _ _ _ _ _ (rationalInterpolant_covariance r hr) he







theorem residual_zero_transport {n m:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (r:ℕ) (hr:r+2≤n) (z:Fin (n+1) → SpectralField m) (hz:∀i,z i≠0)
    (hL:torusL (z (⟨r+1,by omega⟩:Fin n).castSucc/z (⟨r,by omega⟩:Fin n).castSucc)≠0)
    (hzero:∀p,torusEvaluation
      (z ∘ topPerm (Equiv.swap (⟨r,by omega⟩:Fin n) ⟨r+1,by omega⟩))
      (fun i =>hz _) (laurentResidual (fun p =>lastLaurent p (P p)) p)=0)
    (p:Pairing (n+1)) :
    torusEvaluation z hz (laurentResidual (fun p =>lastLaurent p (P p)) p)=0 := by
  let σ:=topPerm (Equiv.swap (⟨r,by omega⟩:Fin n) ⟨r+1,by omega⟩)
  let φ:=torusEvaluation z hz
  let a:=(PartialColumn.rowPosition r hr).padTop
  let w:=torusWeights (variableF (⟨r+1,by omega⟩:Fin n).castSucc/variableF (⟨r,by omega⟩:Fin n).castSucc)
  let v:=torusWeights (z (⟨r+1,by omega⟩:Fin n).castSucc/z (⟨r,by omega⟩:Fin n).castSucc)
  have hw:∀t,RationalAt φ.toRingHom (w.tile t) (v.tile t) :=
    rationalAt_torusWeights φ ((rationalAt_variable z hz _).div (rationalAt_variable z hz _) (hz _))
      (div_ne_zero (hz _) (hz _)) hL
  have hv (q:Pairing (n+1)):RationalAt φ.toRingHom (permSpectral σ (rationalInterpolationResidual n q)) 0 := by
    have h:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField (n+1))
      (permLaurent σ (laurentResidual (fun p =>lastLaurent p (P p)) q))
    change RationalAt φ.toRingHom (evalLaurent _) _ at h
    rw [←permSpectral_evalLaurent,laurentResidual_map P hP] at h
    change RationalAt φ.toRingHom _ (torusEvaluation z hz _) at h
    rw [torusEvaluation_permLaurent] at h
    exact (hzero q) ▸ h
  have hright:=RationalAt.mulVec (φ:=φ.toRingHom) (localR a w) (localR a v)
    (fun q =>permSpectral σ (rationalInterpolationResidual n q)) (0:Pairing (n+1) → SpectralField m)
    (rationalAt_localR φ a w v hw) hv p
  have he:=congrFun (rationalInterpolationResidual_covariance r hr) p
  change rationalInterpolationResidual n p=(localR a w).mulVec _ p at he
  rw [←he,Matrix.mulVec_zero] at hright
  have hleft:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField (n+1))
    (laurentResidual (fun p =>lastLaurent p (P p)) p)
  change RationalAt φ.toRingHom (evalLaurent _) _ at hleft
  rw [laurentResidual_map P hP] at hleft
  exact hleft.unique hright







lemma rationalAt_firstFlat_vacuum {n:ℕ} (p:Pairing (n+1)) :
    RationalAt (firstFlatEvaluation n).toRingHom (rationalVacuum (n+1) p)
      ((∏ j : Fin n, (spectralA j+constF n C))*
        firstZeroRaw (fun j => (spectralWeights n j).tile) (rationalVacuum n) p) := by
  have hr:VacuumRegular (Fin.cons deletionWeights (spectralWeights n)) := by
    unfold VacuumRegular
    rw [det_flat_bottom _ (Or.inr rfl)]
    exact spectral_regular n
  have h:=rationalAt_normalizedVacuum _ _ rationalAt_firstFlat_weights hr p
  rw [normalizedVacuum_firstZero _ (spectral_regular n)] at h
  have he:= (rationalAt_firstFlat_normalization n).mul h
  have hs:rationalVacuum n=spectralNormalization n • normalizedVacuum (spectralWeights n) := rfl
  rw [hs,firstZeroRaw_smul]
  simpa only [rationalVacuum,Pi.smul_apply,smul_eq_mul,mul_assoc] using he



lemma firstFlat_smaller_values {n:ℕ}
    (hprev:∀ p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (i:Fin (n+1)) (p:Pairing (n+1)) :
    lastValue (RingHom.id _)
      ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)
      (torusSin ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i))
      (rationalNodalPolynomial n) p=
      firstFlatSmallerScalar n i * normalizedVacuum (firstFlatSmallerWeights n i) p := by
  induction i using Fin.cases with
  | succ i =>
      simp only [Fin.cons_succ,firstFlatSmallerScalar,firstFlatSmallerWeights]
      simpa only [lastValue,Polynomial.eval₂_id,nodalVacuum,ite_mul,one_mul] using rationalNodalPolynomial_at_node p i
  | zero =>
      have hz:constF n phase^3≠0:=pow_ne_zero _ (constF_phase_ne_zero n)
      have hdiv:constF n phase^3/(constF n phase^3)=1:=div_self hz
      have hcos:torusCos ((constF n phase^3)^2/constF n phase^3)=constF n c := by
        rw [pow_two,mul_div_cancel_right₀ _ hz,torusCos_phase_pow]
        rfl
      have hr:VacuumRegular (Fin.snoc (spectralWeights n) (torusWeights (constF n phase^3/(constF n phase^3)))) := by
        rw [hdiv,torusWeights_one]
        exact firstFlatSmaller_regular n 0
      have h:=rationalAt_last_vacuum (constF n phase^3) hz
        (by rw [hdiv]; exact torusL_one_ne_zero n) hr p
      have he:=rationalAt_last_interpolant (constF n phase^3) hz p
      rw [hprev p] at he
      have heq:=he.unique h
      rw [hcos,hdiv,torusWeights_one] at heq
      simp only [constF] at heq
      rw [scalarPolynomial_eval_snoc_flat,scalarPolynomial_eval_spectral] at heq
      simpa only [firstFlatSmallerScalar,firstFlatSmallerWeights,Fin.cons_zero,constF] using heq







lemma firstZeroPolynomial_flatNode {n:ℕ}
    (hprev:∀ p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (i:Fin (n+1)) (p:Pairing (n+2)) :
    lastValue (RingHom.id _)
      ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)
      (torusSin ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i))
      (firstZeroPolynomial (fun j => (spectralWeights n j).tile)
        (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n)) p =
      (((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)+constF n C)*
        firstFlatSmallerScalar n i * firstZeroRaw (fun j => (firstFlatSmallerWeights n i j).tile)
          (normalizedVacuum (firstFlatSmallerWeights n i)) p := by
  have h:=torus_firstZero_lastValue (spectralWeights n)
    ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i)
    (firstFlatNode_ne_zero i) (firstFlatNode_L i) (rationalNodalPolynomial n)
  rw [firstFlatNode_cosine,firstFlatNode_weights] at h
  have hi: lastValue (RingHom.id _)
      ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)
      (torusSin ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i))
      (rationalNodalPolynomial n)=
      firstFlatSmallerScalar n i • normalizedVacuum (firstFlatSmallerWeights n i) := by
    funext q
    exact firstFlat_smaller_values hprev i q
  rw [hi,firstZeroRaw_smul] at h
  have he:=congrFun h p
  simpa only [Pi.smul_apply,smul_eq_mul,mul_assoc] using he.symm

 

theorem rationalNodalPolynomial_firstFlat {n:ℕ}
    (hprev:∀ p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀ p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=
      rationalNodalPolynomial (n+1) p) :
    (fun p => (P p).map (firstFlatEvaluation n).toRingHom)=
      fun p => Polynomial.C (∏ j:Fin n,(spectralA j+constF n C))*
        firstZeroPolynomial (fun j => (spectralWeights n j).tile)
          (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n) p := by
  have hdeg:LastDegree (n+1) P :=
    LastDegree.of_map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))
      (IsFractionRing.injective _ _)
      (by simpa only [hP] using rationalNodalPolynomial_degree (n+1))
  have hrightdeg:LastDegree (n+1) (fun p => Polynomial.C (∏ j:Fin n,(spectralA j+constF n C))*
        firstZeroPolynomial (fun j => (spectralWeights n j).tile)
          (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n) p) := by
    intro p k hk
    rw [Polynomial.coeff_C_mul,firstZeroPolynomial_degree _ _ _ _ _ (rationalNodalPolynomial_degree n) p k hk,mul_zero]
  apply lastPolynomial_unique _ _ (hdeg.map _) hrightdeg _ (firstFlatBeta_injective n)
  · intro p
    rw [Polynomial.coeff_map,Polynomial.coeff_C_mul,
      firstZeroPolynomial_leading _ _ _ _ _ (rationalNodalPolynomial_degree n)]
    have hh: (fun q:Pairing n => (rationalNodalPolynomial n q.padTop).coeff n)=rationalVacuum n := by
      funext q; exact rationalNodalPolynomial_leading q
    rw [hh]
    have ha:=RationalAt.algebraMap (φ:=(firstFlatEvaluation n).toRingHom)
      (F:=SpectralField (n+1)) ((P p.padTop).coeff (n+1))
    have hb:=congrArg (fun Q:Polynomial (SpectralField (n+1)) => Q.coeff (n+1)) (hP p.padTop)
    rw [Polynomial.coeff_map,rationalNodalPolynomial_leading] at hb
    rw [hb] at ha
    exact ha.unique (rationalAt_firstFlat_vacuum p)
  · intro p i
    have hz:=firstFlatNode_ne_zero i
    have hs:=rationalAt_torusSin (firstFlatEvaluation n) (rationalAt_firstFlat_deletionNode i) hz
    have he: RationalAt (firstFlatEvaluation n).toRingHom
        ((rationalNodalPolynomial (n+1) p).eval (deletionBeta i))
        (((P p).map (firstFlatEvaluation n).toRingHom).eval
          ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)) := by
      rw [←hP]
      exact RationalAt.eval_map _ (rationalAt_firstFlat_deletionBeta i) _
    have hsin:RationalAt (firstFlatEvaluation n).toRingHom
        (if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1)
        (if p.Occupied (Fin.last (n+1)) then torusSin
          ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i) else 1) := by
      split_ifs
      · exact hs
      · exact RationalAt.one
    have hb:=hsin.mul he
    rw [rationalNodalPolynomial_at_node] at hb
    have hv:=hb.unique (rationalAt_firstFlat_nodalVacuum i p)
    have hright:=firstZeroPolynomial_flatNode hprev i p
    apply mul_left_cancel₀ (show (if p.Occupied (Fin.last (n+1)) then torusSin
      ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i) else 1)≠0 by
        split_ifs; exact firstFlatNode_sine_ne_zero i; exact one_ne_zero)
    rw [hv,Polynomial.eval_mul,Polynomial.eval_C]
    have hr: (if p.Occupied (Fin.last (n+1)) then torusSin
        ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i) else 1)*
        (firstZeroPolynomial (fun j => (spectralWeights n j).tile)
          (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n) p).eval
          ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)=
        (((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)+constF n C)*
          firstFlatSmallerScalar n i * firstZeroRaw (fun j => (firstFlatSmallerWeights n i j).tile)
            (normalizedVacuum (firstFlatSmallerWeights n i)) p := by
      simpa only [lastValue,Polynomial.eval₂_id,ite_mul,one_mul] using hright
    rw [mul_left_comm,hr]
    ring

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

lemma normalizedVacuum_firstThree {K:Type*} [Field K] {n:ℕ}
    (w:Fin n → Weights K) (hw:VacuumRegular w) :
    normalizedVacuum (Fin.cons identityWeights w)=vacantBottomExtension (normalizedVacuum w) := by
  have hr:VacuumRegular (Fin.cons identityWeights w) := by
    unfold VacuumRegular
    rw [det_flat_bottom _ (Or.inl rfl)]
    exact hw
  symm
  apply normalizedVacuum_unique _ hr
  constructor
  · rw [←Pairing.padBottom_empty,vacantBottomExtension_padBottom]
    exact (normalizedVacuum_stationary w hw).1
  · funext p
    rw [mulVec_vacantBottomExtension]
    by_cases hp:p.Occupied 0
    · simp only [vacantBottomExtension,hp,ite_true]
      apply Finset.sum_eq_zero
      intro q _
      rw [column_identity_bottom_row _ rfl _ _ hp,zero_mul]
    · rw [←p.padBottom_restrict hp,vacantBottomExtension_padBottom]
      simp only [column_padBottom,Fin.cons_succ]
      exact congrFun (normalizedVacuum_stationary w hw).2 _

lemma rationalAt_firstThree_vacuum {n:ℕ} (p:Pairing (n+1)) :
    RationalAt (firstThreeEvaluation n).toRingHom (rationalVacuum (n+1) p)
      ((∏ j:Fin n,(spectralA j+constF n C))*vacantBottomExtension (rationalVacuum n) p) := by
  have hr:VacuumRegular (Fin.cons identityWeights (spectralWeights n)) := by
    unfold VacuumRegular
    rw [det_flat_bottom _ (Or.inl rfl)]
    exact spectral_regular n
  have h:=rationalAt_normalizedVacuum _ _ rationalAt_firstThree_weights hr p
  rw [normalizedVacuum_firstThree _ (spectral_regular n)] at h
  have he:=(rationalAt_firstThree_normalization n).mul h
  have hs:rationalVacuum n=spectralNormalization n • normalizedVacuum (spectralWeights n) := rfl
  rw [hs,vacantBottomExtension_smul]
  simpa only [rationalVacuum,Pi.smul_apply,smul_eq_mul,mul_assoc] using he







lemma rationalNodalPolynomial_firstThree_self {n:ℕ}
    (W:Pairing n → Laurent n) (hW:∀q,evalLaurent (W q)=rationalVacuum n q)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=
      rationalNodalPolynomial (n+1) p) (p:Pairing (n+2)) :
    ((P p).map (firstThreeEvaluation n).toRingHom).eval (-constF n C)=0 := by
  have he:(P p).eval (betaL 0)=nodalDatumL W 0 p := by
    apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
    change evalLaurent ((P p).eval (betaL 0))=evalLaurent (nodalDatumL W 0 p)
    rw [nodalDatumL_map W hW]
    have hh:=rationalNodalPolynomial_at_node p (0:Fin (n+1))
    rw [eq_div_iff (by split_ifs; exact deletionNode_sine_ne_zero 0; exact one_ne_zero)]
    rw [mul_comm]
    rw [←hP] at hh
    have hf:evalLaurent ((P p).eval (betaL 0))=
        ((P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))).eval (deletionBeta 0) := by
      rw [←betaL_map]
      exact (Polynomial.eval_map_apply ..).symm
    rw [hf]
    exact hh
  have hb:firstThreeEvaluation n (betaL (0:Fin (n+1)))= -constF n C := by
    have ha:=RationalAt.algebraMap (φ:=(firstThreeEvaluation n).toRingHom)
      (F:=SpectralField (n+1)) (betaL (0:Fin (n+1)))
    change RationalAt _ (evalLaurent _) _ at ha
    rw [betaL_map] at ha
    exact ha.unique (rationalAt_firstThree_deletionBeta 0)
  have hh:=congrArg (firstThreeEvaluation n) he
  rw [nodalDatumL_firstThree_zero] at hh
  rw [←hb]
  change ((P p).map (firstThreeEvaluation n).toRingHom).eval
    ((firstThreeEvaluation n).toRingHom (betaL 0))=0
  rw [Polynomial.eval_map_apply]
  exact hh

lemma rationalAt_firstThree_nodalVacuum {n:ℕ} (i:Fin n) (p:Pairing (n+2)) :
    RationalAt (firstThreeEvaluation n).toRingHom (nodalVacuum i.succ p)
      ((∏ j:Fin n,(spectralA j+constF n C))*(deletionBeta i+constF n C)*
        vacantBottomExtension (nodalVacuum i) p) := by
  have hr:VacuumRegular (Fin.cons identityWeights (nodalWeights i)) := by
    unfold VacuumRegular
    rw [det_flat_bottom _ (Or.inl rfl)]
    exact nodal_regular i
  have h:=rationalAt_normalizedVacuum _ _ (rationalAt_firstThree_nodalWeights i) hr p
  rw [normalizedVacuum_firstThree _ (nodal_regular i)] at h
  have he:=(rationalAt_firstThree_nodalScalar i).mul h
  have hs:nodalVacuum i=nodalScalar i • normalizedVacuum (nodalWeights i) := rfl
  rw [hs,vacantBottomExtension_smul]
  simpa only [nodalVacuum,Pi.smul_apply,smul_eq_mul,mul_assoc] using he







theorem rationalNodalPolynomial_firstThree {n:ℕ}
    (W:Pairing n → Laurent n) (hW:∀q,evalLaurent (W q)=rationalVacuum n q)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=
      rationalNodalPolynomial (n+1) p) :
    (fun p => (P p).map (firstThreeEvaluation n).toRingHom)=
      fun p => Polynomial.C (∏j:Fin n,(spectralA j+constF n C))*
        firstThreePolynomial (constF n C) (rationalNodalPolynomial n) p := by
  have hdeg:LastDegree (n+1) P :=
    LastDegree.of_map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))
      (IsFractionRing.injective _ _) (by simpa only [hP] using rationalNodalPolynomial_degree (n+1))
  have hright:LastDegree (n+1) (fun p => Polynomial.C (∏j:Fin n,(spectralA j+constF n C))*
        firstThreePolynomial (constF n C) (rationalNodalPolynomial n) p) := by
    intro p k hk
    rw [Polynomial.coeff_C_mul,
      firstThreePolynomial_degree _ _ (rationalNodalPolynomial_degree n) p k hk,mul_zero]
  apply lastPolynomial_unique _ _ (hdeg.map _) hright _ (firstThreeBeta_injective n)
  · intro p
    rw [Polynomial.coeff_map,Polynomial.coeff_C_mul,
      firstThreePolynomial_leading _ _ (rationalNodalPolynomial_degree n)]
    have hh:(fun q:Pairing n => (rationalNodalPolynomial n q.padTop).coeff n)=rationalVacuum n := by
      funext q; exact rationalNodalPolynomial_leading q
    rw [hh]
    have ha:=RationalAt.algebraMap (φ:=(firstThreeEvaluation n).toRingHom)
      (F:=SpectralField (n+1)) ((P p.padTop).coeff (n+1))
    have hb:=congrArg (fun Q:Polynomial (SpectralField (n+1)) => Q.coeff (n+1)) (hP p.padTop)
    rw [Polynomial.coeff_map,rationalNodalPolynomial_leading] at hb
    rw [hb] at ha
    exact ha.unique (rationalAt_firstThree_vacuum p)
  · intro p i
    induction i using Fin.cases with
    | zero =>
        simp only [Fin.cons_zero]
        rw [rationalNodalPolynomial_firstThree_self W hW P hP p]
        simp [firstThreePolynomial,Polynomial.eval_mul,Polynomial.eval_add]
    | succ i =>
        simp only [Fin.cons_succ]
        have hs:=rationalAt_torusSin (firstThreeEvaluation n)
          (rationalAt_firstThree_deletionNode i.succ)
          (firstThreeNode_ne_zero i.succ)
        have he:RationalAt (firstThreeEvaluation n).toRingHom
            ((rationalNodalPolynomial (n+1) p).eval (deletionBeta i.succ))
            (((P p).map (firstThreeEvaluation n).toRingHom).eval (deletionBeta i)) := by
          rw [←hP]
          exact RationalAt.eval_map _ (rationalAt_firstThree_deletionBeta i.succ) _
        have hsin:RationalAt (firstThreeEvaluation n).toRingHom
            (if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i.succ) else 1)
            (if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1) := by
          split_ifs
          · exact hs
          · exact RationalAt.one
        have hb:=hsin.mul he
        rw [rationalNodalPolynomial_at_node] at hb
        have hv:=hb.unique (rationalAt_firstThree_nodalVacuum i p)
        apply mul_left_cancel₀ (show (if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1)≠0 by
          split_ifs; exact deletionNode_sine_ne_zero i; exact one_ne_zero)
        rw [hv,Polynomial.eval_mul,Polynomial.eval_C]
        by_cases hp:p.Occupied 0
        · simp [firstThreePolynomial,vacantBottomExtension,hp]
        · rw [←p.padBottom_restrict hp,firstThreePolynomial_padBottom,vacantBottomExtension_padBottom]
          rw [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
          rw [show (p.restrict (Fin.succOrderEmb (n+1))).padBottom.Occupied (Fin.last (n+1)) ↔
              (p.restrict (Fin.succOrderEmb (n+1))).Occupied (Fin.last n) by
                exact Pairing.padBottom_occupied_succ _ (Fin.last n)]
          rw [←rationalNodalPolynomial_at_node]
          ring







lemma phaseRows_regular {n r:ℕ} (v:Fin r → Fin n) (k:Fin r → ℕ)
    (hk:∀j,k j≤3) (hm:∀i j, (k i≠0 ∧ k i≠3) → (k j≠0 ∧ k j≠3) → i=j) :
    VacuumRegular (fun j =>torusWeights (constF n phase^(k j)/variableF (v j))) := by
  apply torusRegular_of_rationalAt (allOneEvaluation n) _ (fun j =>constF 0 phase^(k j))
    (fun j =>rationalAt_phaseRow (v j) (k j))
    (fun j =>pow_ne_zero _ (constF_phase_ne_zero 0))
    (fun j =>torusL_phase_small_ne_zero 0 (k j) (hk j))
  unfold VacuumRegular
  rw [det_one_nonflat]
  · exact one_ne_zero
  · intro i j hi hj
    apply hm i j
    · constructor
      · intro h; apply hi; left; simp [h, torusWeights_one]
      · intro h; apply hi; right; rw [h,torusWeights_phase_three]
    · constructor
      · intro h; apply hj; left; simp [h,torusWeights_one]
      · intro h; apply hj; right; rw [h,torusWeights_phase_three]

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

lemma pairEarlier_regular (n s:ℕ) : VacuumRegular (pairEarlierWeights n s) :=
  phaseRows_regular (pairIndex n) (pairExponent n s) (pairExponent_le n s) pairExponent_mixed

lemma pairNode_regular (n s:ℕ) (i:Fin (n+2)) : VacuumRegular (pairNodeWeights n s i) := by
  have h:=phaseRows_regular (Fin.snoc (pairIndex n) (pairIndex n i))
    (Fin.snoc (pairExponent n s) 0)
    (fun j =>Fin.lastCases (by simp) (fun j =>by simpa using pairExponent_le n s j) j) ?_
  · convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext j
    induction j using Fin.lastCases <;> simp [pairNodeWeights,pairEarlierWeights]
  · intro j k hj hk
    induction j using Fin.lastCases with
    | last => exact (hj.1 (by simp)).elim
    | cast j => induction k using Fin.lastCases with
      | last => exact (hk.1 (by simp)).elim
      | cast k => exact congrArg Fin.castSucc (pairExponent_mixed (s:=s) j k (by simpa using hj) (by simpa using hk))

lemma rationalAt_pair_nodalVacuum {n s:ℕ} (hs:s≤3) (i:Fin (n+2)) (hi:i≠1) (p:Pairing (n+3)) :
    RationalAt (pairEvaluation n s).toRingHom (nodalVacuum i p)
      (scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.snoc (pairCosines n s) (pairBeta n s i))*
        normalizedVacuum (pairNodeWeights n s i) p) :=
  (rationalAt_pair_nodalScalar s i).mul
    (rationalAt_normalizedVacuum _ _ (rationalAt_pair_nodalWeights hs i hi) (pairNode_regular n s i) p)







lemma normalizedVacuum_deletion_cons {n m:ℕ} (w:Fin n → Weights (SpectralField m))
    (z:SpectralField m) (hz:z≠0) (hL:torusL z≠0) (hL3:torusL (constF m phase^3*z)≠0)
    (hr:VacuumRegular (Fin.cons (torusWeights (constF m phase^3*z)) (Fin.cons (torusWeights z) w)))
    (hr':VacuumRegular w) :
    normalizedVacuum (Fin.cons (torusWeights (constF m phase^3*z)) (Fin.cons (torusWeights z) w))=
      (deletionMap 0 (show 2≤n+2 by omega)).mulVec (normalizedVacuum w) := by
  have he:=normalizedVacuum_deletion 0 (show 2≤n+2 by omega)
    (Fin.cons (torusWeights (constF m phase^3*z)) (Fin.cons (torusWeights z) w))
    z hz hL hL3 rfl rfl hr
  have hrows : (fun i:Fin n => (Fin.cons (torusWeights (constF m phase^3*z)) (Fin.cons (torusWeights z) w) : Fin (n+2) → Weights (SpectralField m))
      ((⟨0+1,by omega⟩ : Fin (n+2)).succAbove ((⟨0,by omega⟩ : Fin (n+1)).succAbove i))) = w :=
    by funext i; simp [Fin.succAbove,Fin.lt_def]
  rw [hrows] at he
  exact he hr'







lemma deleteWeights_regular (n:ℕ) : VacuumRegular (deleteWeights n) :=
  phaseRows_regular Fin.succ (fun _ =>3) (by intros; omega) (by intros i j hi; exact (hi.2 rfl).elim)

lemma normalizedVacuum_pair_delete (n:ℕ) :
    normalizedVacuum (pairEarlierWeights n 3)=
      (deletionMap 0 (show 2≤n+2 by omega)).mulVec (normalizedVacuum (deleteWeights n)) := by
  have h:=normalizedVacuum_deletion_cons (deleteWeights n) ((variableF (0:Fin (n+1)))⁻¹)
    (inv_ne_zero (variableF_ne_zero _))
    (by simpa using torusL_phaseRow_ne_zero (0:Fin (n+1)) 0 (by omega))
    (by simpa only [div_eq_mul_inv] using torusL_phaseRow_ne_zero (0:Fin (n+1)) 3 (by omega))
    (by rw [←pairEarlier_delete]; exact pairEarlier_regular n 3) (deleteWeights_regular n)
  rwa [←pairEarlier_delete] at h

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

lemma mappedNodal_pair_node {n s:ℕ} (hs:s≤3)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (i:Fin (n+2)) (hi:i≠1) :
    lastValue (RingHom.id (SpectralField (n+1))) (pairBeta n s i) (torusSin (deletionNode (pairIndex n i)))
      (fun p =>(P p).map (pairEvaluation n s).toRingHom)=
      scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.snoc (pairCosines n s) (pairBeta n s i)) •
        normalizedVacuum (pairNodeWeights n s i) := by
  funext p
  have hsine:=rationalAt_torusSin (pairEvaluation n s) (rationalAt_pair_deletionNode s i)
    (mul_ne_zero (pairPoint_ne_zero n s i) (pow_ne_zero _ (constF_phase_ne_zero _)))
  rw [pairPoint_of_ne i hi] at hsine
  change RationalAt _ (torusSin (deletionNode i)) (torusSin (deletionNode (pairIndex n i))) at hsine
  have he:RationalAt (pairEvaluation n s).toRingHom
      ((rationalNodalPolynomial (n+2) p).eval (deletionBeta i))
      (((P p).map (pairEvaluation n s).toRingHom).eval (pairBeta n s i)) := by
    rw [←hP]
    exact RationalAt.eval_map _ (rationalAt_pair_deletionBeta s i) _
  have hsin:RationalAt (pairEvaluation n s).toRingHom
      (if p.Occupied (Fin.last (n+2)) then torusSin (deletionNode i) else 1)
      (if p.Occupied (Fin.last (n+2)) then torusSin (deletionNode (pairIndex n i)) else 1) := by
    split_ifs
    · exact hsine
    · exact RationalAt.one
  have hh:=hsin.mul he
  rw [rationalNodalPolynomial_at_node] at hh
  simpa only [lastValue,Polynomial.eval₂_id,Pi.smul_apply,smul_eq_mul,ite_mul,one_mul] using
    hh.unique (rationalAt_pair_nodalVacuum hs i hi p)







lemma deleteMapped_leading {n:ℕ}
    (Q:Pairing (n+1) → Polynomial (Laurent n))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (p:Pairing n) :
    ((Q p.padTop).map (deleteEvaluation n).toRingHom).coeff n=
      scalarValue (algebraMap ℂ (SpectralField (n+1))) (fun i:Fin n =>fcos i.succ (-3))*
        normalizedVacuum (deleteWeights n) p := by
  have h:=mappedNodal_leading Q hQ (deletePoint n) (fun i =>variableF_ne_zero i.succ)
    (fun i =>torusL_phaseRow_ne_zero i.succ 3 (by omega)) (deleteWeights_regular n) p
  rw [deletePoint_cosines] at h
  exact h

lemma deleteMapped_node {n:ℕ}
    (Q:Pairing (n+1) → Polynomial (Laurent n))
    (hQ:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+1) p)
    (i:Fin (n+1)) :
    lastValue (RingHom.id (SpectralField (n+1))) (deletionBeta i) (torusSin (deletionNode i))
      (fun p =>(Q p).map (deleteEvaluation n).toRingHom)=
      scalarValue (algebraMap ℂ (SpectralField (n+1)))
        (Fin.snoc (fun j:Fin n =>fcos j.succ (-3)) (deletionBeta i)) •
          normalizedVacuum (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) i) := by
  funext p
  have he:=lastLaurent_regular_value Q hQ (deletePoint n) (fun j =>variableF_ne_zero j.succ)
    (deletionNode i) (mul_ne_zero (variableF_ne_zero i) (pow_ne_zero _ (constF_phase_ne_zero _))) (deletePoint_node_L i)
    (by rw [deletePoint_node_weights]; exact copiedNode_regular _ _) p
  have hc:(fun j =>torusCos (((Fin.snoc (deletePoint n) (deletionNode i) : Fin (n+1) → SpectralField (n+1)) j)^2/constF (n+1) phase^3))=
      Fin.snoc (fun j:Fin n =>fcos j.succ (-3)) (deletionBeta i) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; rfl
    | cast j => simp only [Fin.snoc_castSucc]; exact congrFun (deletePoint_cosines n) j
  rw [hc,deletePoint_node_weights] at he
  change (if p.Occupied (Fin.last n) then torusSin (deletionNode i) else 1) *
    Polynomial.eval (deletionBeta i) ((Q p).map (deleteEvaluation n).toRingHom) = _ at he
  simpa only [lastValue,Polynomial.eval₂_id,Pi.smul_apply,smul_eq_mul,ite_mul,one_mul,deleteEvaluation] using he

lemma mergeNewWeights_regular (n:ℕ) : VacuumRegular (mergeNewWeights n) := by
  rw [mergeNewWeights_phase]
  exact phaseRows_regular id (mergeExponent n) (mergeExponent_le n) mergeExponent_mixed

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



lemma firstFlatCandidate_value {n:ℕ}
    (hprev:∀p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (p:Pairing (n+2)) :
    firstFlatEvaluation (n+1) (lastLaurent p (P p))=
      (∏j:Fin (n+1),(spectralA j+constF (n+1) C))*
        firstZeroRaw (fun j =>(spectralWeights (n+1) j).tile) (rationalVacuum (n+1)) p := by
  rw [firstFlatEvaluation_lastLaurent]
  have he:=rationalNodalPolynomial_firstFlat hprev P hP
  have hv: lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
      (fun p =>(P p).map (firstFlatEvaluation n).toRingHom) p = _ :=
    congrFun (congrArg (lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))) he) p
  change lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
      (fun p =>(P p).map (firstFlatEvaluation n).toRingHom) p=_
  rw [hv,lastValue_C_mul,lastValue_firstZero_spectral,show rationalInterpolant n=rationalVacuum (n+1) from funext hprev]
  simp only [Pi.smul_apply,smul_eq_mul,map_prod,map_add,liftSpectral_spectralA,liftSpectral_const,
    Fin.prod_univ_castSucc]
  ring

lemma rationalVacuum_raw_stationary (n:ℕ) :
    ((rawColumn (@rowNumerator n)).map (algebraMap (SpectralRing n) (SpectralField n))).mulVec (rationalVacuum n)=
      (∏i:Fin n,evalLaurent (rowDenominator i)) • rationalVacuum n := by
  rw [rawColumn_map]
  simp_rw [rowNumerator_map]
  rw [rawColumn_scale,Matrix.smul_mulVec]
  exact congrArg (fun v =>(∏i:Fin n,evalLaurent (rowDenominator i)) • v) (rationalVacuum_stationary n)

lemma residual_specialization_zero {n m:ℕ} (φ:Laurent n →ₐ[ℂ] SpectralField m)
    (W:Pairing n → Laurent n)
    (hV:∀p,RationalAt φ.toRingHom (rationalVacuum n p) (φ (W p))) (p:Pairing n) :
    φ (laurentResidual W p)=0 := by
  have hm:=RationalAt.mulVec (φ:=φ.toRingHom)
    ((rawColumn (@rowNumerator n)).map (algebraMap (SpectralRing n) (SpectralField n)))
    ((rawColumn (@rowNumerator n)).map φ.toRingHom) (rationalVacuum n) (fun q =>φ (W q))
    (fun q r =>RationalAt.algebraMap _) hV p
  rw [rationalVacuum_raw_stationary] at hm
  have hr: RationalAt φ.toRingHom ((∏i:Fin n,evalLaurent (rowDenominator i))*rationalVacuum n p)
      ((∏i:Fin n,φ (rowDenominator i))*φ (W p)) :=
    (RationalAt.prod _ _ _ (fun i _ =>RationalAt.algebraMap _)).mul (hV p)
  have he:=hm.unique hr
  simp only [Matrix.map_apply,Matrix.mulVec,dotProduct] at he
  simp only [laurentResidual,map_sub,map_mul,map_prod,Matrix.mulVec,dotProduct,map_sum]
  exact sub_eq_zero.mpr he

 
theorem residual_firstFlat {n:ℕ}
    (hprev:∀p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (p:Pairing (n+2)) :
    firstFlatEvaluation (n+1) (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  apply residual_specialization_zero
  intro q
  rw [firstFlatCandidate_value hprev P hP]
  exact rationalAt_firstFlat_vacuum q







lemma firstThreeCandidate_value {n:ℕ}
    (W:Pairing n → Laurent n) (hW:∀q,evalLaurent (W q)=rationalVacuum n q)
    (hprev:∀p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (p:Pairing (n+2)) :
    firstThreeEvaluation (n+1) (lastLaurent p (P p))=
      (∏j:Fin (n+1),(spectralA j+constF (n+1) C))*
        vacantBottomExtension (rationalVacuum (n+1)) p := by
  rw [firstThreeEvaluation_lastLaurent]
  change lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
      (fun p =>(P p).map (firstThreeEvaluation n).toRingHom) p=_
  rw [rationalNodalPolynomial_firstThree W hW P hP,lastValue_C_mul]
  change _ * lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n))) (fun p =>(Polynomial.X+Polynomial.C (constF n C))*
    vacantBottomExtension (rationalNodalPolynomial n) p) p=_
  rw [lastValue_mul_poly_map,lastValue_vacantBottomExtension,lastValue_spectral,
    show rationalInterpolant n = rationalVacuum (n+1) from funext hprev]
  simp only [Pi.smul_apply,smul_eq_mul,map_prod,map_add,liftSpectral_spectralA,liftSpectral_const,
    Fin.prod_univ_castSucc,Polynomial.eval₂_add,Polynomial.eval₂_X,Polynomial.eval₂_C]
  ring

 
theorem residual_firstThree {n:ℕ}
    (W:Pairing n → Laurent n) (hW:∀q,evalLaurent (W q)=rationalVacuum n q)
    (hprev:∀p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (p:Pairing (n+2)) :
    firstThreeEvaluation (n+1) (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  apply residual_specialization_zero
  intro q
  rw [firstThreeCandidate_value W hW hprev P hP]
  exact rationalAt_firstThree_vacuum q

end





noncomputable section
open scoped Classical

 

theorem residual_flat_transport {n m:ℕ}
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (c:SpectralField m)
    (hbase:∀(z:Fin (n+2) → SpectralField m) (hz:∀k,z k≠0),z 0=c → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0)
    (i:Fin (n+1)) (z:Fin (n+2) → SpectralField m) (hz:∀k,z k≠0)
    (hi:z i.castSucc=c)
    (hL:∀j:Fin (n+1),j < i → torusL (z i.castSucc/z j.castSucc)≠0) (p:Pairing (n+2)) :
    torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  induction i using Fin.induction generalizing z p with
  | zero => exact hbase z hz hi p
  | @succ i ih =>
    let σ:=Equiv.swap i.castSucc i.succ
    let z':=z ∘ topPerm σ
    have hz':∀k,z' k≠0 := fun k =>hz _
    have he (k:Fin (n+1)): z' k.castSucc=z (σ k).castSucc := by simp only [z',Function.comp_apply,topPerm_cast]
    have hs:σ i.castSucc=i.succ := Equiv.swap_apply_left _ _
    have hr:i.val+2≤n+1 := by omega
    have hzero:∀q,torusEvaluation z' hz' (laurentResidual (fun q =>lastLaurent q (P q)) q)=0 := by
      intro q
      apply ih z' hz'
      · rw [he,hs]; exact hi
      · intro j hj
        rw [he,hs,he]
        have hja:j≠i.castSucc := Fin.ne_of_lt hj
        have hjb:j≠i.succ := by apply Fin.ne_of_lt; exact hj.trans (Fin.castSucc_lt_succ)
        rw [show σ j=j from Equiv.swap_apply_of_ne_of_ne hja hjb]
        exact hL j (hj.trans (Fin.castSucc_lt_succ))
    exact residual_zero_transport P hP i.val hr z hz
      (hL i.castSucc (Fin.castSucc_lt_succ)) hzero p







theorem residual_pair_transport {n m:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (c:SpectralField m) (h2:2≤n)
    (hbase:∀(z:Fin (n+1) → SpectralField m) (hz:∀k,z k≠0),
      z (⟨1,by omega⟩:Fin n).castSucc=c*z (⟨0,by omega⟩:Fin n).castSucc → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0)
    (i j:Fin n) (hij:i<j) (z:Fin (n+1) → SpectralField m) (hz:∀k,z k≠0)
    (he:z j.castSucc=c*z i.castSucc) (hL:PairExchangeRegular z i j) (p:Pairing (n+1)) :
    torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  generalize hsum:i.val+j.val=t
  induction t using Nat.strong_induction_on generalizing i j z p with
  | h t ih =>
    by_cases hi:i.val=0
    · by_cases hj:j.val=1
      · apply hbase z hz
        have hi0:i=(⟨0,by omega⟩:Fin n) := Fin.ext hi
        have hj1:j=(⟨1,by omega⟩:Fin n) := Fin.ext hj
        simpa only [hi0,hj1] using he
      · let r:=j.val-1
        have hr:r+2≤n := by dsimp [r]; omega
        let a:Fin n:=⟨r,by omega⟩
        let b:Fin n:=⟨r+1,by omega⟩
        let σ:=Equiv.swap a b
        have hb:b=j := by apply Fin.ext; dsimp [b,r]; omega
        have hia:i≠a := by intro h; have:=congrArg Fin.val h; dsimp [a,r] at this; omega
        have hib:i≠b := by rw [hb]; exact Fin.ne_of_lt hij
        have hsi:σ i=i := Equiv.swap_apply_of_ne_of_ne hia hib
        have hsj:σ a=j := by rw [←hb]; exact Equiv.swap_apply_left _ _
        have horder:i<a := by change i.val<a.val; dsimp [a,r]; omega
        have hreg:torusL (z b.castSucc/z a.castSucc)≠0 := by
          apply hL a b (by rw [hb]; exact Fin.ne_of_lt (by change a.val<j.val; dsimp [a,r]; omega))
          intro h; rcases h with h|h
          · exact hia h.1.symm
          · exact hib h.2.symm
        apply residual_zero_transport P hP r hr z hz hreg
        intro q
        apply ih (i.val+a.val) (by dsimp [a,r]; omega) i a horder
          (z ∘ topPerm σ) (fun k =>hz _) _ _ q rfl
        · simpa only [Function.comp_apply,topPerm_cast,hsi,hsj] using he
        · have hh:=hL.perm σ
          have hsym:σ.symm=σ := Equiv.symm_swap _ _
          rw [hsym,hsi,show σ j=a by rw [←hb]; exact Equiv.swap_apply_right _ _] at hh
          exact hh
    · let r:=i.val-1
      have hr:r+2≤n := by dsimp [r]; omega
      let a:Fin n:=⟨r,by omega⟩
      let b:Fin n:=⟨r+1,by omega⟩
      let σ:=Equiv.swap a b
      have hb:b=i := by apply Fin.ext; dsimp [b,r]; omega
      have hja:j≠a := by intro h; have:=congrArg Fin.val h; dsimp [a,r] at this; have:=hij; change i.val<j.val at this; omega
      have hjb:j≠b := by rw [hb]; exact Ne.symm (Fin.ne_of_lt hij)
      have hsj:σ j=j := Equiv.swap_apply_of_ne_of_ne hja hjb
      have hsi:σ a=i := by rw [←hb]; exact Equiv.swap_apply_left _ _
      have horder:a<j := by change a.val<j.val; dsimp [a,r]; have:=hij; change i.val<j.val at this; omega
      have hreg:torusL (z b.castSucc/z a.castSucc)≠0 := by
        apply hL a b (by rw [hb]; exact Fin.ne_of_lt (by change a.val < i.val; dsimp [a,r]; omega))
        intro h; rcases h with h|h
        · exact hjb h.2.symm
        · exact hja h.1.symm
      apply residual_zero_transport P hP r hr z hz hreg
      intro q
      apply ih (a.val+j.val) (by dsimp [a,r]; omega) a j horder
        (z ∘ topPerm σ) (fun k =>hz _) _ _ q rfl
      · simpa only [Function.comp_apply,topPerm_cast,hsi,hsj] using he
      · have hh:=hL.perm σ
        have hsym:σ.symm=σ := Equiv.symm_swap _ _
        rw [hsym,hsj,show σ i=a by rw [←hb]; exact Equiv.swap_apply_right _ _] at hh
        exact hh

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ResidualParityCoefficients
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical LaurentPolynomial

lemma laurentResidual_odd {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (p:Pairing (n+1)) (hp:p.Occupied i.castSucc) :
    signLaurent i.castSucc (laurentResidual (fun q =>lastLaurent q (P q)) p)=
      -laurentResidual (fun q =>lastLaurent q (P q)) p := by
  apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
  change evalLaurent _=evalLaurent _
  rw [←signSpectral_evalLaurent,laurentResidual_map P hP,rationalInterpolationResidual_parity]
  simp only [occupancySign,hp,ite_true,neg_one_mul,evalLaurent,map_neg]
  congr 1
  exact (laurentResidual_map P hP p).symm

lemma laurentResidual_peel_top_zero {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (p:Pairing (n+1)) (hp:p.Occupied i.castSucc) :
    (peelLaurent i.castSucc (laurentResidual (fun q =>lastLaurent q (P q)) p)).coeff (2*(n+1):ℤ)=0 := by
  by_contra h
  obtain ⟨e,he⟩:=(peelLaurent_coeff_ne_zero_iff _ _ _).mp h
  apply he
  apply signLaurent_odd_even_coeff_zero i.castSucc _ (laurentResidual_odd P hP i p hp)
  simp only [Fin.insertNth_apply_same]
  exact even_two_mul (n+1:ℤ)







theorem residual_zero_of_root_grid {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (hb:∀p,LaurentBox (laurentResidual (fun q =>lastLaurent q (P q)) p) (fun _ =>2*(n+1)))
    (p:Pairing (n+1)) (i:Fin n) (hp:p.Occupied i.castSucc)
    (hz:∀v:Fin (n+1) × Fin 4,
      torusEvaluation (Function.update variableF i.castSucc (residualRoot i v))
        (fun j =>by by_cases h:j=i.castSucc <;> simp [h,residualRoot_ne_zero,variableF_ne_zero])
        (laurentResidual (fun q =>lastLaurent q (P q)) p)=0) :
    rationalInterpolationResidual n p=0 := by
  let f:=laurentResidual (fun q =>lastLaurent q (P q)) p
  have ht:(fullPeel i.castSucc f).coeff (2*(n+1):ℤ)=0 := by
    rw [fullPeel_coeff,laurentResidual_peel_top_zero P hP i p hp,map_zero]
  have hzero (z:SpectralField (n+1)) (h:z∈residualRootSet i):z≠0 := by
    obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp h
    exact residualRoot_ne_zero i v
  have hh:fullPeel i.castSucc f=0 := by
    apply laurent_root_saturation _ (2*(n+1)) ((hb p).fullPeel _) ht (residualRootSet i)
      (by rw [residualRootSet_card]; omega) hzero
    intro z h
    obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp h
    rw [fullPeel_eval]
    exact hz v
  have hf:f=0 := fullPeel_injective i.castSucc (by simpa only [map_zero] using hh)
  rw [←laurentResidual_map P hP,show laurentResidual (fun q =>lastLaurent q (P q)) p=f from rfl,hf]
  exact map_zero _

end

 

 

noncomputable section
open scoped Classical







lemma lastEvaluation_residual_zero {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (y:SpectralField n) (hy:y≠0)
    (hA:torusCos (y^2/constF n phase^3)=deletionBeta i) (p:Pairing (n+1)) :
    lastEvaluation y hy (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  let φ:=lastEvaluation y hy
  have hpoly:=RationalAt.eval₂ φ.toRingHom (liftSpectral n) (RingHom.id _)
    (rationalAt_last_lift y hy) (rationalAt_last_spectralA y hy)
    (rationalResidualPolynomial n p)
  rw [Polynomial.eval₂_id,hA,rationalResidualPolynomial_at_node] at hpoly
  have hs:RationalAt φ.toRingHom
      (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last n)) else 1)
      (if p.Occupied (Fin.last n) then torusSin y else 1) := by
    split_ifs
    · exact rationalAt_torusSin φ (rationalAt_last_variable y hy) hy
    · exact RationalAt.one
  have hd:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField (n+1))
    ((∏j:Fin n,rowDenominator j.castSucc) * algebraMap ℂ (Laurent (n+1)) (1/2))
  have hden:evalLaurent ((∏j:Fin n,rowDenominator j.castSucc) * algebraMap ℂ (Laurent (n+1)) (1/2))=
      (∏j:Fin n,evalLaurent (rowDenominator j.castSucc))/2 := by
    change evalLaurent ((∏j:Fin n,rowDenominator j.castSucc) * constantL (n+1) (1/2))=_
    simp only [evalLaurent,map_mul,map_prod,map_constantL]
    congr 1
    change (algebraMap ℂ (SpectralField (n+1))) (1/2)=(2:SpectralField (n+1))⁻¹
    norm_num
    rw [map_ofNat]
    norm_num
  change RationalAt _ (evalLaurent _) _ at hd
  rw [hden] at hd
  have hr:=hd.mul (hs.mul hpoly)
  simp only [mul_zero] at hr
  have he:=rationalInterpolationResidual_transfer (n:=n) p
  simp only [ite_mul,one_mul] at hr
  change RationalAt φ.toRingHom ((∏j:Fin n,evalLaurent (rowDenominator j.castSucc))/2 *
    lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n))) (rationalResidualPolynomial n) p) 0 at hr
  rw [←he] at hr
  have hf:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField (n+1))
    (laurentResidual (fun q =>lastLaurent q (P q)) p)
  change RationalAt _ (evalLaurent _) _ at hf
  rw [laurentResidual_map P hP] at hf
  exact hf.unique hr

lemma residual_last_delete_universal {n m:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0)
    (hzi:z (Fin.last n)=z i.castSucc*constF m phase^3) (p:Pairing (n+1)) :
    torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  let u:=monomialUnit (variableExponent i) (phase^3) (pow_ne_zero _ phase_ne_zero)
  have hu:evalLaurent (u:Laurent n)=deletionNode i := by
    simp [u,monomialUnit,evalLaurent_monomial_product,variableExponent,Pi.single_apply,deletionNode,constF,mul_comm]
  apply generic_substitution_zero (Fin.last n) u
    (Fin.snoc variableF (deletionNode i)) _ _ _ _
    (lastEvaluation_residual_zero P hP i _ (mul_ne_zero (variableF_ne_zero i) (pow_ne_zero _ (constF_phase_ne_zero n))) rfl p) z hz
  · simpa [u,monomialUnit,torusEvaluation_monomial,variableExponent,Pi.single_apply,constF,mul_comm] using hzi
  · rw [Fin.snoc_last,hu]
  · intro j; simp

lemma residual_last_inverse_universal {n m:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0)
    (hzi:z (Fin.last n)=(z i.castSucc)⁻¹) (p:Pairing (n+1)) :
    torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  let u:=monomialUnit (-variableExponent i) 1 one_ne_zero
  have hu:evalLaurent (u:Laurent n)=(variableF i)⁻¹ := by
    simp [u,monomialUnit,evalLaurent_monomial_product,variableExponent,Pi.single_apply,constF]
  have hA:torusCos (((variableF i)⁻¹)^2/constF n phase^3)=deletionBeta i := by
    rw [deletionBeta,deletionNode]
    have he:((variableF i)⁻¹)^2/constF n phase^3=
        ((variableF i*constF n phase^3)^2/constF n phase^3)⁻¹ := by
      field_simp [variableF_ne_zero,constF_phase_ne_zero]
    rw [he,torusCos_inv]
  apply generic_substitution_zero (Fin.last n) u
    (Fin.snoc variableF ((variableF i)⁻¹)) _ _ _ _
    (lastEvaluation_residual_zero P hP i _ (inv_ne_zero (variableF_ne_zero i)) hA p) z hz
  · simpa [u,monomialUnit,torusEvaluation_monomial,variableExponent,Pi.single_apply,constF] using hzi
  · rw [Fin.snoc_last,hu]
  · intro j; simp







lemma positiveRoot_negative_zero {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (p:Pairing (n+1)) (hp:p.Occupied i.castSucc)
    (j:Fin (n+1)) (b:Bool)
    (h:torusEvaluation (Function.update variableF i.castSucc (positiveResidualRoot i j b))
      (fun k =>by by_cases h:k=i.castSucc <;> simp [h,positiveResidualRoot_ne_zero,variableF_ne_zero])
      (laurentResidual (fun q =>lastLaurent q (P q)) p)=0) :
    torusEvaluation (Function.update variableF i.castSucc (-positiveResidualRoot i j b))
      (fun k =>by by_cases h:k=i.castSucc <;> simp [h,positiveResidualRoot_ne_zero,variableF_ne_zero])
      (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  have hh:=torusEvaluation_neg_zero i.castSucc _ _ _ (laurentResidual_odd P hP i p hp) h
  simpa only [Function.update_self,Function.update_idem] using hh

lemma residual_root_grid_of_positive {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (p:Pairing (n+1)) (hp:p.Occupied i.castSucc)
    (hpos:∀j b,torusEvaluation (Function.update variableF i.castSucc (positiveResidualRoot i j b))
      (fun k =>by by_cases h:k=i.castSucc <;> simp [h,positiveResidualRoot_ne_zero,variableF_ne_zero])
      (laurentResidual (fun q =>lastLaurent q (P q)) p)=0)
    (v:Fin (n+1) × Fin 4) :
    torusEvaluation (Function.update variableF i.castSucc (residualRoot i v))
      (fun k =>by by_cases h:k=i.castSucc <;> simp [h,residualRoot_ne_zero,variableF_ne_zero])
      (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  obtain ⟨b,h|h⟩:=residualRoot_signed i v
  · simpa only [h] using hpos v.1 b
  · simpa only [h] using positiveRoot_negative_zero P hP i p hp v.1 b (hpos v.1 b)







theorem residual_positive_roots {n:ℕ}
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (hflat:∀(b:Bool) (z:Fin (n+2) → SpectralField (n+2)) (hz:∀k,z k≠0),
      z 0=(if b then constF (n+2) phase^3 else 1) → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0)
    (hpair:∀(h2:2≤n+1) (s:ℕ),s=2 ∨ s=3 →
      ∀(z:Fin (n+2) → SpectralField (n+2)) (hz:∀k,z k≠0),
      z (⟨1,by omega⟩:Fin (n+1)).castSucc=constF (n+2) phase^s*z (⟨0,by omega⟩:Fin (n+1)).castSucc → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0)
    (i:Fin (n+1)) (j:Fin (n+2)) (b:Bool) (p:Pairing (n+2)) :
    torusEvaluation (Function.update variableF i.castSucc (positiveResidualRoot i j b))
      (fun k =>by by_cases h:k=i.castSucc <;> simp [h,positiveResidualRoot_ne_zero,variableF_ne_zero])
      (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  let z:=Function.update variableF i.castSucc (positiveResidualRoot i j b)
  have hz:∀k,z k≠0 := fun k =>by dsimp [z]; by_cases h:k=i.castSucc <;> simp [h,positiveResidualRoot_ne_zero,variableF_ne_zero]
  change torusEvaluation z hz _=0
  by_cases hji:j=i.castSucc
  · have hroot:positiveResidualRoot i j b=(if b then constF (n+2) phase^3 else 1) := by simp [positiveResidualRoot,hji]
    apply residual_flat_transport P hP _ (hflat b) i z hz
    · simp [z,hroot]
    · intro a ha
      cases b
      · simpa only [z,hroot,Bool.false_eq_true,ite_false,show constF (n+2) (1:ℂ)=1 from map_one (algebraMap ℂ _)] using
          flat_update_regular i a (Ne.symm (Fin.ne_of_lt ha)) 1 one_ne_zero
      · simpa only [z,hroot,ite_true,constF,map_pow] using
          flat_update_regular i a (Ne.symm (Fin.ne_of_lt ha)) (phase^3) (pow_ne_zero _ phase_ne_zero)
  · by_cases hjlast:j=Fin.last (n+1)
    · have hilast:(Fin.last (n+1):Fin (n+2))≠i.castSucc := Ne.symm (Fin.castSucc_ne_last i)
      cases b
      · apply residual_last_delete_universal P hP i z hz
        simp only [z,positiveResidualRoot,hjlast,hilast,ite_false,ite_true,Function.update_self,Function.update_of_ne hilast,Bool.false_eq_true]
        field_simp [constF_phase_ne_zero]
      · apply residual_last_inverse_universal P hP i z hz
        simp [z,positiveResidualRoot,hjlast,hilast]
    · obtain ⟨a,ha⟩:∃a:Fin (n+1),a.castSucc=j := by
        have hjv : j.val < n+1 := by
          have hne : j.val ≠ n+1 := by
            intro h
            apply hjlast
            exact Fin.ext h
          have := j.isLt
          omega
        exact ⟨⟨j.val,hjv⟩,rfl⟩
      subst j
      have hai:a≠i := fun h =>hji (congrArg Fin.castSucc h)
      let s:ℕ:=if b then 3 else 2
      have hs:s=2 ∨ s=3 := by cases b <;> simp [s]
      have h2:2≤n+1 := by have:=i.isLt; have:=a.isLt; have hne:i.val≠a.val := fun h =>hai (Fin.ext h.symm); omega
      by_cases hlt:a < i
      · have hroot:positiveResidualRoot i a.castSucc b=constF (n+2) phase^s*variableF a.castSucc := by
          simp [positiveResidualRoot,hji,hjlast,show a.val < i.val from hlt,s]
        have hr:PairExchangeRegular z i a := by
          simpa only [z,hroot,constF,map_pow] using pair_update_regular i a hai.symm (phase^s) (pow_ne_zero _ phase_ne_zero)
        apply residual_pair_transport P hP _ h2 (hpair h2 s hs) a i hlt z hz _ hr.symm p
        simp only [z,Function.update_self,Function.update_of_ne (fun h =>hai (Fin.castSucc_injective (n+1) h)),hroot]
      · have hia:i < a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hai)
        have hroot:positiveResidualRoot i a.castSucc b=(constF (n+2) phase^s)⁻¹*variableF a.castSucc := by
          simp [positiveResidualRoot,hji,hjlast,show ¬a.val < i.val from hlt,s]
        have hr:PairExchangeRegular z i a := by
          simpa only [z,hroot,constF,map_inv₀,map_pow] using pair_update_regular i a hai.symm (phase^s)⁻¹ (inv_ne_zero (pow_ne_zero _ phase_ne_zero))
        apply residual_pair_transport P hP _ h2 (hpair h2 s hs) i a hia z hz _ hr p
        simp only [z,Function.update_self,Function.update_of_ne (fun h =>hai (Fin.castSucc_injective (n+1) h)),hroot]
        field_simp [constF_phase_ne_zero]

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







lemma stationary_eq_empty_mul_normalized {K:Type*} [Field K] {n:ℕ}
    (w:Fin n → Weights K) (hw:VacuumRegular w) (v:Pairing n → K)
    (h: (column w).mulVec v=v) : v=fun p =>v (empty n)*normalizedVacuum w p := by
  let u:=v+(1-v (empty n)) • normalizedVacuum w
  have hu:IsNormalizedStationary w u := by
    constructor
    · simp [u,normalizedVacuum,attachEmpty]
    · simp only [u,Matrix.mulVec_add,Matrix.mulVec_smul,h,(normalizedVacuum_stationary w hw).2]
  have hh:=normalizedVacuum_unique w hw u hu
  funext p
  have he:=congrFun hh p
  change v p+(1-v (empty n))*normalizedVacuum w p=normalizedVacuum w p at he
  linear_combination he

lemma interpolant_eq_vacuum_of_residual {n:ℕ} (h:∀p,rationalInterpolationResidual n p=0) :
    rationalInterpolant n=rationalVacuum (n+1) := by
  have hs:(column (spectralWeights (n+1))).mulVec (rationalInterpolant n)=rationalInterpolant n := by
    funext p
    have hh:=h p
    unfold rationalInterpolationResidual at hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left
      (Finset.prod_ne_zero_iff.mpr (fun i _ =>rowDenominator_map_ne_zero i)))
  have he:=stationary_eq_empty_mul_normalized (spectralWeights (n+1)) (spectral_regular (n+1))
    (rationalInterpolant n) hs
  simp only [rationalInterpolant_empty] at he ⊢
  exact he

lemma rationalInterpolationResidual_empty (n:ℕ) : rationalInterpolationResidual n (empty (n+1))=0 := by
  simp only [rationalInterpolationResidual,column_mulVec_empty,sub_self,mul_zero]









theorem residual_saturation {n:ℕ}
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (bP:∀p,PolynomialBox (P p) (fun _ =>2*(n+1)))
    (hflat:∀(b:Bool) (z:Fin (n+2) → SpectralField (n+2)) (hz:∀k,z k≠0),
      z 0=(if b then constF (n+2) phase^3 else 1) → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0)
    (hpair:∀(h2:2≤n+1) (s:ℕ),s=2 ∨ s=3 →
      ∀(z:Fin (n+2) → SpectralField (n+2)) (hz:∀k,z k≠0),
      z (⟨1,by omega⟩:Fin (n+1)).castSucc=constF (n+2) phase^s*z (⟨0,by omega⟩:Fin (n+1)).castSucc → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0) :
    ∀p,rationalInterpolationResidual (n+1) p=0 := by
  have hd:LastDegree (n+1) P :=
    LastDegree.of_map _ (IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1)))
      (by simpa only [hP] using rationalNodalPolynomial_degree (n+1))
  have hb:∀p,LaurentBox (laurentResidual (fun q =>lastLaurent q (P q)) p) (fun _ =>2*((n+1)+1)) := by
    intro p
    convert laurentResidual_box (fun q =>lastLaurent q (P q)) (2*(n+1))
      (fun q =>lastLaurent_box q (P q) (bP q) (hd q)) p using 1
    all_goals try with_reducible_and_instances rfl
  intro p
  by_cases hp:p=empty (n+2)
  · subst p; exact rationalInterpolationResidual_empty _
  · obtain ⟨i,hi⟩:=p.exists_earlier_occupied hp
    exact residual_zero_of_root_grid P hP hb p i hi
      (residual_root_grid_of_positive P hP i p hi (fun j b =>residual_positive_roots P hP hflat hpair i j b p))







lemma deleteEvaluation_vacuum {n:ℕ} (W:Pairing n → Laurent n)
    (hW:∀p,evalLaurent (W p)=rationalVacuum n p) (p:Pairing n) :
    deleteEvaluation n (W p)=scalarValue (algebraMap ℂ (SpectralField (n+1)))
      (fun i:Fin n =>fcos i.succ (-3))*normalizedVacuum (deleteWeights n) p := by
  have h:=torusEvaluation_vacuum W hW (deletePoint n) (fun i =>variableF_ne_zero i.succ)
    (fun i =>torusL_phaseRow_ne_zero i.succ 3 (by omega)) (deleteWeights_regular n) p
  rw [deletePoint_cosines] at h
  exact h






lemma residual_flat_universal {n:ℕ}
    (W:Pairing n → Laurent n) (hW:∀p,evalLaurent (W p)=rationalVacuum n p)
    (D:VacuumPolynomialData n)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (b:Bool) (z:Fin (n+2) → SpectralField (n+2)) (hz:∀k,z k≠0)
    (h:z 0=(if b then constF (n+2) phase^3 else 1)) (p:Pairing (n+2)) :
    torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  cases b
  · exact firstFlatEvaluation_zero_universal _ (residual_firstFlat D.interpolant P hP p) z hz h
  · exact firstThreeEvaluation_zero_universal _ (residual_firstThree W hW D.interpolant P hP p) z hz h

lemma vacuumData_one_exists : Nonempty (VacuumPolynomialData 1) := by
  let W:Pairing 0 → Laurent 0:=fun _ =>1
  have hW:∀p,evalLaurent (W p)=rationalVacuum 0 p := by
    intro p; rw [rationalVacuum_zero]; exact map_one _
  have bW:∀p,LaurentBox (W p) (fun _ =>2*0-2) := by
    intro p; exact LaurentBox.one
  let D:=vacuumData_zero
  choose P hP bP using rationalNodalPolynomial_laurent_box W D.W hW D.eval_P bW D.box
  have hs:∀p,rationalInterpolationResidual 1 p=0 :=
    residual_saturation P hP (by simpa using bP) (residual_flat_universal W hW D P hP)
      (by intro h2; omega)
  have he:=interpolant_eq_vacuum_of_residual hs
  exact ⟨⟨P,hP,by simpa using bP,fun p =>by rw [lastLaurent_map p (P p) (hP p)]; exact congrFun he p⟩⟩

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



def integratedNorthSource (n : ℕ) : SourcePairing n → SpectralField n :=
  (1 - sourceTransfer (fun i => (spectralWeights n i).tile))⁻¹.mulVec
    ((northSource (fun i => (spectralWeights n i).tile)).mulVec
      (normalizedVacuum (spectralWeights n)))

end




end CriticalStrip.Diagram

end OAI
end


