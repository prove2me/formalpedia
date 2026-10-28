-- Prove2me | Definitions.Def_OAIQ042S015
-- name    : OAIQ042S015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T02:06:14.847718+00:00
-- url     : https://prove2.me/theorems/b92fd207-c07c-40c5-8dc2-73d6cfb4ce44
-- title:
--   Definitions bundle OAIQ042S015 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 9 definitions and 22 theorems. The definitions and types are `OAI.CriticalStrip.Diagram.angleAugmented`, `OAI.CriticalStrip.Diagram.angleNorthSource`, `OAI.CriticalStrip.Diagram.angleScalar`, `OAI.CriticalStrip.Diagram.angleVacuum`, `OAI.CriticalStrip.Diagram.polynomialNorthGluing`, `OAI.CriticalStrip.Diagram.polynomialNorthSource`, `OAI.CriticalStrip.Diagram.polynomialVacuumVector`, `OAI.CriticalStrip.Diagram.realNorthSeparator`, `OAI.CriticalStrip.Diagram.vacuumData`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: [`StripMass_AugmentedColumn`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/AugmentedColumn.lean), [`StripMass_MergePairCandidate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/MergePairCandidate.lean), [`StripMass_NodalEmpty`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/NodalEmpty.lean), [`StripMass_NodalTorusValue`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/NodalTorusValue.lean), [`StripMass_NorthBijection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/NorthBijection.lean), [`StripMass_NorthMerging`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/NorthMerging.lean), [`StripMass_PairSelfNode`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/PairSelfNode.lean), [`StripMass_PhysicalStationarity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/PhysicalStationarity.lean), [`StripMass_SwapVacancy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/SwapVacancy.lean), [`StripMass_VacuumDegree`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/VacuumDegree.lean).
--
--   **Imports.** It imports the bundles `OAIQ042S013` and `OAIQ042S014` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.CriticalStrip.Diagram.deformationAngles_scalar_ne_zero`, `OAI.CriticalStrip.Diagram.homogeneous_angleScalar_ne_zero`, `OAI.CriticalStrip.Diagram.physical_augmented_stationary`, `OAI.CriticalStrip.Diagram.polynomialNorthGluing_delete`, `OAI.CriticalStrip.Diagram.polynomialNorthGluing_eq_archCandidate`, `OAI.CriticalStrip.Diagram.polynomialNorthGluing_merge`, `OAI.CriticalStrip.Diagram.polynomialNorthGluing_row_reflection` and `OAI.CriticalStrip.Diagram.reversed_augmented_stationary`; the proofs of `OAI.CriticalStrip.Diagram.deformationAngles_scalar_ne_zero`, `OAI.CriticalStrip.Diagram.homogeneous_angleScalar_ne_zero`, `OAI.CriticalStrip.Diagram.physical_augmented_stationary`, `OAI.CriticalStrip.Diagram.polynomialNorthGluing_delete`, `OAI.CriticalStrip.Diagram.polynomialNorthGluing_eq_archCandidate`, `OAI.CriticalStrip.Diagram.polynomialNorthGluing_merge`, `OAI.CriticalStrip.Diagram.polynomialNorthGluing_row_reflection`, `OAI.CriticalStrip.Diagram.reversed_augmented_stationary`, `OAI.CriticalStrip.HoneycombBranch.physical_stepped_flux` and `OAI.CriticalStrip.critical_strip_mass`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ042S013
import Definitions.Def_OAIQ042S014

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


theorem normalizedVacuum_merge {n m : ℕ} (r : ℕ) (hr : r+2≤n+1)
    (w : Fin (n+1) → Weights (SpectralField m)) (z : SpectralField m)
    (hz : z≠0) (hL : torusL z≠0) (hL1 : torusL (constF m phase*z)≠0)
    (hL2 : torusL (constF m phase^2*z)≠0)
    (hw₀ : w ⟨r,by omega⟩=torusWeights (constF m phase^2*z))
    (hw₁ : w ⟨r+1,by omega⟩=torusWeights z)
    (hreg : VacuumRegular w)
    (hreg' : VacuumRegular (fun i => (PartialColumn.twoRows w r
      (torusWeights (constF m phase*z)) swapWeights) ((⟨r+1,by omega⟩ : Fin (n+1)).succAbove i))) :
    normalizedVacuum w = (mergeMap r hr).mulVec (normalizedVacuum
      (fun i => (PartialColumn.twoRows w r (torusWeights (constF m phase*z)) swapWeights)
        ((⟨r+1,by omega⟩ : Fin (n+1)).succAbove i))) := by
  symm
  apply normalizedVacuum_unique _ hreg
  have hs:=normalizedVacuum_stationary _ hreg'
  constructor
  · rw [mergeMap_mulVec_empty]; exact hs.1
  · have he := PartialColumn.column_merge_intertwiner r hr w z hz hL hL1 hL2 hw₀ hw₁
    change column w*mergeMap r hr = mergeMap r hr*column _ at he
    rw [Matrix.mulVec_mulVec,he,←Matrix.mulVec_mulVec,hs.2]

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

lemma rationalNodalPolynomial_laurent_at_node {n:ℕ}
    (W:Pairing n → Laurent n) (hW:∀q,evalLaurent (W q)=rationalVacuum n q)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (p:Pairing (n+2)) (i:Fin (n+1)) :
    (P p).eval (betaL i)=nodalDatumL W i p := by
  apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
  change evalLaurent ((P p).eval (betaL i))=evalLaurent (nodalDatumL W i p)
  rw [nodalDatumL_map W hW]
  have hh:=rationalNodalPolynomial_at_node p i
  rw [eq_div_iff (by split_ifs; exact deletionNode_sine_ne_zero i; exact one_ne_zero)]
  rw [mul_comm]
  rw [←hP] at hh
  have hf:evalLaurent ((P p).eval (betaL i))=
      ((P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))).eval (deletionBeta i) := by
    rw [←betaL_map]
    exact (Polynomial.eval_map_apply ..).symm
  rw [hf]
  exact hh

 

theorem rationalNodalPolynomial_pair_self {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀q,evalLaurent (W q)=rationalVacuum (n+1) q)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (s:ℕ) (hs:s=2 ∨ s=3) (p:Pairing (n+3)) :
    ((P p).map (pairEvaluation n s).toRingHom).eval (pairEvaluation n s (betaL 1))=0 := by
  change ((P p).map (pairEvaluation n s).toRingHom).eval ((pairEvaluation n s).toRingHom (betaL 1))=0
  rw [Polynomial.eval_map_apply,rationalNodalPolynomial_laurent_at_node W hW P hP]
  exact nodalDatumL_pair_self_zero W s hs p







lemma normalizedVacuum_merge_cons {n m:ℕ} (w:Fin n → Weights (SpectralField m))
    (z:SpectralField m) (hz:z≠0) (hL:torusL z≠0)
    (hL1:torusL (constF m phase*z)≠0) (hL2:torusL (constF m phase^2*z)≠0)
    (hr:VacuumRegular (Fin.cons (torusWeights (constF m phase^2*z)) (Fin.cons (torusWeights z) w)))
    (hr':VacuumRegular (Fin.cons (torusWeights (constF m phase*z)) w)) :
    normalizedVacuum (Fin.cons (torusWeights (constF m phase^2*z)) (Fin.cons (torusWeights z) w))=
      (mergeMap 0 (show 2≤n+2 by omega)).mulVec
        (normalizedVacuum (Fin.cons (torusWeights (constF m phase*z)) w)) := by
  have he:=normalizedVacuum_merge 0 (show 2≤n+2 by omega)
    (Fin.cons (torusWeights (constF m phase^2*z)) (Fin.cons (torusWeights z) w))
    z hz hL hL1 hL2 rfl rfl hr
  have hrows : (fun i => PartialColumn.twoRows
      (Fin.cons (torusWeights (constF m phase^2*z)) (Fin.cons (torusWeights z) w)) 0
      (torusWeights (constF m phase*z)) swapWeights
      ((⟨0+1,by omega⟩ : Fin (n+2)).succAbove i)) = Fin.cons (torusWeights (constF m phase*z)) w :=
    twoRows_omit_one _ _ _ _ _
  rw [hrows] at he
  exact he hr'

lemma normalizedVacuum_pairNode_delete {n:ℕ} (i:Fin (n+2)) :
    normalizedVacuum (pairNodeWeights n 3 i)=
      (deletionMap 0 (show 2≤n+3 by omega)).mulVec
        (normalizedVacuum (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) (pairIndex n i))) := by
  have h:=normalizedVacuum_deletion_cons (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) (pairIndex n i))
    ((variableF (0:Fin (n+1)))⁻¹) (inv_ne_zero (variableF_ne_zero _))
    (by simpa using torusL_phaseRow_ne_zero (0:Fin (n+1)) 0 (by omega))
    (by simpa only [div_eq_mul_inv] using torusL_phaseRow_ne_zero (0:Fin (n+1)) 3 (by omega))
    (by rw [←pairNode_delete i]; exact pairNode_regular n 3 i) (copiedNode_regular _ _)
  rwa [←pairNode_delete i] at h

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

lemma pairMapped_delete_leading {n:ℕ}
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (p:Pairing (n+2)) :
    ((P p.padTop).map (pairEvaluation n 3).toRingHom).coeff (n+2)=
      deletePairScalar n*scalarValue (algebraMap ℂ (SpectralField (n+1))) (fun i:Fin n =>fcos i.succ (-3))*
        (deletionMap 0 (show 2≤n+2 by omega)).mulVec (normalizedVacuum (deleteWeights n)) p := by
  have hw:(fun i =>torusWeights (constF (n+1) phase^3/pairPoint n 3 i))=pairEarlierWeights n 3 :=
    funext (fun i =>congrArg torusWeights (pairArgument (by omega) i))
  have h:=mappedNodal_leading P hP (pairPoint n 3) (pairPoint_ne_zero n 3)
    (pairEarlier_L (by omega)) (by rw [hw]; exact pairEarlier_regular n 3) p
  rw [show (fun i =>torusCos ((pairPoint n 3 i)^2/constF (n+1) phase^3))=pairCosines n 3 from funext (fun i =>pairPoint_cosine i),
    hw,scalar_pair_delete,normalizedVacuum_pair_delete] at h
  exact h









theorem rationalNodalPolynomial_pair_delete {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p)
    (Q:Pairing (n+1) → Polynomial (Laurent n))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (hprev:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+1) p)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p) :
    (fun p =>(P p).map (pairEvaluation n 3).toRingHom)=
      fun p =>deletePairPolynomial n*
        matrixPolynomial (deletionMap 0 (show 2≤n+3 by omega))
          (fun q =>(Q q).map (deleteEvaluation n).toRingHom) p := by
  let Q':Pairing (n+1) → Polynomial (SpectralField (n+1)):=fun p =>(Q p).map (deleteEvaluation n).toRingHom
  let M:Matrix (Pairing (n+3)) (Pairing (n+1)) (SpectralField (n+1)):=deletionMap 0 (by omega)
  have hQd:LastDegree n Q':=mappedNodal_degree Q hQ _
  have hM:LastMatrix M:=deletionMap_last 0 (show 2≤n+2 by omega)
  have hMd:LastDegree n (matrixPolynomial M Q'):=hM.degree Q' hQd
  have hright:LastDegree (n+2) (fun p =>deletePairPolynomial n*matrixPolynomial M Q' p):=
    LastDegree.mul_poly _ hMd _ (deletePairPolynomial_degree n)
  apply lastPolynomial_unique _ _ (mappedNodal_degree P hP _) hright _ (pairBeta_injective n 3 (Or.inr rfl))
  · intro p
    rw [pairMapped_delete_leading P hP p]
    rw [LastDegree.mul_poly_top _ hMd _ (deletePairPolynomial_degree n) p,deletePairPolynomial_top]
    rw [hM.leading (deletionMap 0 (show 2≤n+2 by omega)) (fun p q =>deletionMap_padTop 0 (by omega) p q)]
    have he:(fun q:Pairing n =>(Q' q.padTop).coeff n)=
        scalarValue (algebraMap ℂ (SpectralField (n+1))) (fun i:Fin n =>fcos i.succ (-3)) •
          normalizedVacuum (deleteWeights n) := funext (deleteMapped_leading Q hQ)
    rw [he,Matrix.mulVec_smul]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  · intro p i
    by_cases hi:i=1
    · subst i
      rw [show pairBeta n 3 1=pairEvaluation n 3 (betaL 1) from (pairEvaluation_betaL 3 1).symm,
        rationalNodalPolynomial_pair_self W hW P hP 3 (Or.inr rfl)]
      rw [pairEvaluation_betaL,Polynomial.eval_mul,deletePairPolynomial_eval]
      change 0=deletePairScalar n*((fcos 0 9-fcos 0 (-9))*(fcos 0 9-fcos 0 9))*_
      ring
    · have he: lastValue (RingHom.id (SpectralField (n+1))) (pairBeta n 3 i) (torusSin (deletionNode (pairIndex n i)))
          (fun p =>(P p).map (pairEvaluation n 3).toRingHom)=
          lastValue (RingHom.id (SpectralField (n+1))) (pairBeta n 3 i) (torusSin (deletionNode (pairIndex n i)))
            (fun p =>deletePairPolynomial n*matrixPolynomial M Q' p) := by
        rw [mappedNodal_pair_node (by omega) P hP i hi,lastValue_mul_poly,hM.lastValue]
        rw [pairBeta_of_ne i hi,deleteMapped_node Q hprev]
        rw [Matrix.mulVec_smul,smul_smul]
        rw [normalizedVacuum_pairNode_delete,deletePairPolynomial_eval]
        have hs:=scalar_pair_delete_snoc (n:=n) (deletionBeta (pairIndex n i))
        rw [hs]
      have hp:=congrFun he p
      by_cases ho:p.Occupied (Fin.last (n+2))
      · simp only [lastValue,Polynomial.eval₂_id,ho,ite_true] at hp
        exact mul_left_cancel₀ (deletionNode_sine_ne_zero _) hp
      · simpa only [lastValue,Polynomial.eval₂_id,ho,ite_false] using hp







lemma normalizedVacuum_pair_merge (n:ℕ) :
    normalizedVacuum (pairEarlierWeights n 2)=
      (mergeMap 0 (show 2≤n+2 by omega)).mulVec (normalizedVacuum (mergeNewWeights n)) := by
  have h:=normalizedVacuum_merge_cons (deleteWeights n) (mergeZ n) (mergeZ_ne_zero n)
    (mergeZ_L n) (mergeZ_one_L n) (mergeZ_two_L n)
    (by rw [←pairEarlier_merge]; exact pairEarlier_regular n 2) (mergeNewWeights_regular n)
  rwa [←pairEarlier_merge] at h

lemma mergeNode_regular {n:ℕ} (i:Fin (n+1)) : VacuumRegular (mergeNodeWeights i) := by
  have hw:mergeNodeWeights i=fun j =>torusWeights
      (constF (n+1) phase^((Fin.snoc (mergeExponent n) 0 : Fin (n+2) → ℕ) j)/
        variableF ((Fin.snoc id i : Fin (n+2) → Fin (n+1)) j)) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp [mergeNodeWeights]
    | cast j => simpa only [mergeNodeWeights,Fin.snoc_castSucc,id_eq] using congrFun (mergeNewWeights_phase n) j
  rw [hw]
  apply phaseRows_regular
  · intro j
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simpa only [Fin.snoc_castSucc] using mergeExponent_le n j
  · intro j k hj hk
    induction j using Fin.lastCases with
    | last => exact (hj.1 (by simp)).elim
    | cast j => induction k using Fin.lastCases with
      | last => exact (hk.1 (by simp)).elim
      | cast k =>
        simp only [Fin.snoc_castSucc] at hj hk
        exact congrArg Fin.castSucc (mergeExponent_mixed j k hj hk)

lemma normalizedVacuum_pairNode_merge {n:ℕ} (i:Fin (n+2)) :
    normalizedVacuum (pairNodeWeights n 2 i)=
      (mergeMap 0 (show 2≤n+3 by omega)).mulVec
        (normalizedVacuum (mergeNodeWeights (pairIndex n i))) := by
  rw [pairNode_merge,mergeNode_cons]
  exact normalizedVacuum_merge_cons (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) (pairIndex n i))
    (mergeZ n) (mergeZ_ne_zero n) (mergeZ_L n) (mergeZ_one_L n) (mergeZ_two_L n)
    (by rw [←pairNode_merge i]; exact pairNode_regular n 2 i)
    (by rw [←mergeNode_cons]; exact mergeNode_regular _)

lemma mergeMapped_leading {n:ℕ}
    (Q:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (p:Pairing (n+1)) :
    ((Q p.padTop).map (mergeEvaluation n).toRingHom).coeff (n+1)=
      scalarValue (algebraMap ℂ (SpectralField (n+1)))
        (Fin.cons (fcos 0 (-1)) (fun i:Fin n =>fcos i.succ (-3)))*
        normalizedVacuum (mergeNewWeights n) p := by
  have h:=mappedNodal_leading Q hQ (mergePoint n) (mergePoint_ne_zero n)
    (mergePoint_L n) (by rw [mergePoint_weights]; exact mergeNewWeights_regular n) p
  rw [mergePoint_cosines,mergePoint_weights] at h
  exact h

lemma mergeMapped_node {n:ℕ}
    (Q:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hQ:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+2) p)
    (i:Fin (n+1)) :
    lastValue (RingHom.id (SpectralField (n+1))) (deletionBeta i) (torusSin (deletionNode i))
      (fun p =>(Q p).map (mergeEvaluation n).toRingHom)=
      scalarValue (algebraMap ℂ (SpectralField (n+1)))
        (Fin.snoc (Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3))) (deletionBeta i)) •
          normalizedVacuum (mergeNodeWeights i) := by
  funext p
  have he:=lastLaurent_regular_value Q hQ (mergePoint n) (mergePoint_ne_zero n)
    (deletionNode i) (mul_ne_zero (variableF_ne_zero i) (pow_ne_zero _ (constF_phase_ne_zero _))) (mergePoint_node_L i)
    (by rw [mergePoint_node_weights]; exact mergeNode_regular _) p
  have hc:(fun j =>torusCos (((Fin.snoc (mergePoint n) (deletionNode i) : Fin (n+2) → SpectralField (n+1)) j)^2/constF (n+1) phase^3))=
      Fin.snoc (Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3))) (deletionBeta i) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; rfl
    | cast j => simp only [Fin.snoc_castSucc]; exact congrFun (mergePoint_cosines n) j
  rw [hc,mergePoint_node_weights] at he
  change (if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1) *
    Polynomial.eval (deletionBeta i) ((Q p).map (mergeEvaluation n).toRingHom) = _ at he
  simpa only [lastValue,Polynomial.eval₂_id,Pi.smul_apply,smul_eq_mul,ite_mul,one_mul,mergeEvaluation] using he

lemma pairMapped_merge_leading {n:ℕ}
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (p:Pairing (n+2)) :
    ((P p.padTop).map (pairEvaluation n 2).toRingHom).coeff (n+2)=
      mergePairScalar n*scalarValue (algebraMap ℂ (SpectralField (n+1)))
        (Fin.cons (fcos 0 (-1)) (fun i:Fin n =>fcos i.succ (-3)))*
        (mergeMap 0 (show 2≤n+2 by omega)).mulVec (normalizedVacuum (mergeNewWeights n)) p := by
  have hw:(fun i =>torusWeights (constF (n+1) phase^3/pairPoint n 2 i))=pairEarlierWeights n 2 :=
    funext (fun i =>congrArg torusWeights (pairArgument (by omega) i))
  have h:=mappedNodal_leading P hP (pairPoint n 2) (pairPoint_ne_zero n 2)
    (pairEarlier_L (by omega)) (by rw [hw]; exact pairEarlier_regular n 2) p
  rw [show (fun i =>torusCos ((pairPoint n 2 i)^2/constF (n+1) phase^3))=pairCosines n 2 from funext (fun i =>pairPoint_cosine i),
    hw,scalar_pair_merge,normalizedVacuum_pair_merge] at h
  exact h

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

 

theorem rationalNodalPolynomial_pair_merge {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p)
    (Q:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (hprev:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+2) p)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p) :
    (fun p =>(P p).map (pairEvaluation n 2).toRingHom)=
      fun p =>mergePairPolynomial n*
        matrixPolynomial (mergeMap 0 (show 2≤n+3 by omega))
          (fun q =>(Q q).map (mergeEvaluation n).toRingHom) p := by
  let Q':Pairing (n+2) → Polynomial (SpectralField (n+1)):=fun p =>(Q p).map (mergeEvaluation n).toRingHom
  let M:Matrix (Pairing (n+3)) (Pairing (n+2)) (SpectralField (n+1)):=mergeMap 0 (by omega)
  have hQd:LastDegree (n+1) Q':=mappedNodal_degree Q hQ _
  have hM:LastMatrix M:=mergeMap_last 0 (show 2≤n+2 by omega)
  have hMd:LastDegree (n+1) (matrixPolynomial M Q'):=hM.degree Q' hQd
  have hright:LastDegree (n+2) (fun p =>mergePairPolynomial n*matrixPolynomial M Q' p):=
    LastDegree.mul_poly _ hMd _ (mergePairPolynomial_degree n)
  apply lastPolynomial_unique _ _ (mappedNodal_degree P hP _) hright _ (pairBeta_injective n 2 (Or.inl rfl))
  · intro p
    rw [pairMapped_merge_leading P hP p]
    rw [LastDegree.mul_poly_top _ hMd _ (mergePairPolynomial_degree n) p,mergePairPolynomial_top]
    rw [hM.leading (mergeMap 0 (show 2≤n+2 by omega)) (fun p q =>mergeMap_padTop 0 (by omega) p q)]
    have he:(fun q:Pairing (n+1) =>(Q' q.padTop).coeff (n+1))=
        scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.cons (fcos 0 (-1)) (fun i:Fin n =>fcos i.succ (-3))) •
          normalizedVacuum (mergeNewWeights n) := funext (mergeMapped_leading Q hQ)
    rw [he,Matrix.mulVec_smul]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  · intro p i
    by_cases hi:i=1
    · subst i
      rw [show pairBeta n 2 1=pairEvaluation n 2 (betaL 1) from (pairEvaluation_betaL 2 1).symm,
        rationalNodalPolynomial_pair_self W hW P hP 2 (Or.inl rfl)]
      rw [pairEvaluation_betaL,Polynomial.eval_mul,mergePairPolynomial_eval]
      change 0=mergePairScalar n*(fcos 0 7+fcos 0 (-1))*_
      have hf:=fcos_sub_eight (0:Fin (n+1)) 7
      norm_num only at hf
      rw [hf]
      ring
    · have he: lastValue (RingHom.id (SpectralField (n+1))) (pairBeta n 2 i) (torusSin (deletionNode (pairIndex n i)))
          (fun p =>(P p).map (pairEvaluation n 2).toRingHom)=
          lastValue (RingHom.id (SpectralField (n+1))) (pairBeta n 2 i) (torusSin (deletionNode (pairIndex n i)))
            (fun p =>mergePairPolynomial n*matrixPolynomial M Q' p) := by
        rw [mappedNodal_pair_node (by omega) P hP i hi,lastValue_mul_poly,hM.lastValue]
        rw [pairBeta_of_ne i hi,mergeMapped_node Q hprev]
        rw [Matrix.mulVec_smul,smul_smul]
        rw [normalizedVacuum_pairNode_merge,mergePairPolynomial_eval]
        have hs:=scalar_pair_merge_snoc (n:=n) i hi
        rw [pairBeta_of_ne i hi] at hs
        rw [hs]
      have hp:=congrFun he p
      by_cases ho:p.Occupied (Fin.last (n+2))
      · simp only [lastValue,Polynomial.eval₂_id,ho,ite_true] at hp
        exact mul_left_cancel₀ (deletionNode_sine_ne_zero _) hp
      · simpa only [lastValue,Polynomial.eval₂_id,ho,ite_false] using hp







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

lemma rationalAt_pair_vacuum {n s:ℕ} (hs:s≤3) (p:Pairing (n+2)) :
    RationalAt (pairEvaluation n s).toRingHom (rationalVacuum (n+2) p)
      (scalarValue (algebraMap ℂ (SpectralField (n+1))) (pairCosines n s)*
        normalizedVacuum (pairEarlierWeights n s) p) := by
  have h:=rationalAt_torusVacuum (pairPoint n s) (pairPoint_ne_zero n s)
    (pairEarlier_L hs) (by rw [pairPoint_weights hs]; exact pairEarlier_regular n s) p
  rw [pairPoint_weights hs,show (fun i =>torusCos ((pairPoint n s i)^2/constF (n+1) phase^3))=
    pairCosines n s from funext (fun i =>pairPoint_cosine i)] at h
  exact h

lemma mergeEvaluation_vacuum {n:ℕ} (W:Pairing (n+1) → Laurent (n+1))
    (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p) (p:Pairing (n+1)) :
    mergeEvaluation n (W p)=scalarValue (algebraMap ℂ (SpectralField (n+1)))
      (Fin.cons (fcos 0 (-1)) (fun i:Fin n =>fcos i.succ (-3)))*normalizedVacuum (mergeNewWeights n) p := by
  have h:=torusEvaluation_vacuum W hW (mergePoint n) (mergePoint_ne_zero n)
    (mergePoint_L n) (by rw [mergePoint_weights]; exact mergeNewWeights_regular n) p
  rw [mergePoint_cosines,mergePoint_weights] at h
  exact h

lemma deletePairCandidate_value {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p)
    (Q:Pairing (n+1) → Polynomial (Laurent n))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (hprev:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+1) p)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (p:Pairing (n+3)) :
    pairEvaluation (n+1) 3 (lastLaurent p (P p))=
      scalarValue (algebraMap ℂ (SpectralField (n+2))) (pairCosines (n+1) 3)*
        normalizedVacuum (pairEarlierWeights (n+1) 3) p := by
  rw [pairEvaluation_lastLaurent]
  change lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
    (fun p =>(P p).map (pairEvaluation n 3).toRingHom) p=_
  rw [rationalNodalPolynomial_pair_delete W hW Q hQ hprev P hP,lastValue_mul_poly_map,
    (deletionMap_last 0 (show 2≤n+2 by omega)).lastValue_map,deletePairPolynomial_free,deletionMap_map]
  have he:lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
      (fun q =>(Q q).map (deleteEvaluation n).toRingHom)=
      fun q =>deleteEvaluation (n+1) (lastLaurent q (Q q)) := by
    funext q
    exact (deleteEvaluation_lastLaurent q (Q q)).symm
  rw [he]
  simp_rw [deleteEvaluation_vacuum _ hprev]
  change deletePairScalar (n+1)*((deletionMap 0 (show 2≤n+3 by omega)).mulVec
    (scalarValue (algebraMap ℂ (SpectralField (n+2))) (fun i:Fin (n+1) =>fcos i.succ (-3)) • normalizedVacuum (deleteWeights (n+1))) p)=_
  rw [Matrix.mulVec_smul,scalar_pair_delete,normalizedVacuum_pair_delete]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

lemma mergePairCandidate_value {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p)
    (Q:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (hprev:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+2) p)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (p:Pairing (n+3)) :
    pairEvaluation (n+1) 2 (lastLaurent p (P p))=
      scalarValue (algebraMap ℂ (SpectralField (n+2))) (pairCosines (n+1) 2)*
        normalizedVacuum (pairEarlierWeights (n+1) 2) p := by
  rw [pairEvaluation_lastLaurent]
  change lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
    (fun p =>(P p).map (pairEvaluation n 2).toRingHom) p=_
  rw [rationalNodalPolynomial_pair_merge W hW Q hQ hprev P hP,lastValue_mul_poly_map,
    (mergeMap_last 0 (show 2≤n+2 by omega)).lastValue_map,mergePairPolynomial_free,mergeMap_lift]
  have he:lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
      (fun q =>(Q q).map (mergeEvaluation n).toRingHom)=
      fun q =>mergeEvaluation (n+1) (lastLaurent q (Q q)) := by
    funext q
    exact (mergeEvaluation_lastLaurent q (Q q)).symm
  rw [he]
  simp_rw [mergeEvaluation_vacuum _ hprev]
  change mergePairScalar (n+1)*((mergeMap 0 (show 2≤n+3 by omega)).mulVec
    (scalarValue (algebraMap ℂ (SpectralField (n+2)))
      (Fin.cons (fcos 0 (-1)) (fun i:Fin (n+1) =>fcos i.succ (-3))) • normalizedVacuum (mergeNewWeights (n+1))) p)=_
  rw [Matrix.mulVec_smul,scalar_pair_merge,normalizedVacuum_pair_merge]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

 

theorem residual_pair_delete {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p)
    (Q:Pairing (n+1) → Polynomial (Laurent n))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (hprev:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+1) p)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (p:Pairing (n+3)) :
    pairEvaluation (n+1) 3 (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  apply residual_specialization_zero
  intro q
  rw [deletePairCandidate_value W hW Q hQ hprev P hP]
  exact rationalAt_pair_vacuum (by omega) q

theorem residual_pair_merge {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p)
    (Q:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (hprev:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+2) p)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (p:Pairing (n+3)) :
    pairEvaluation (n+1) 2 (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  apply residual_specialization_zero
  intro q
  rw [mergePairCandidate_value W hW Q hQ hprev P hP]
  exact rationalAt_pair_vacuum (by omega) q






lemma vacuumData_step_exists {n:ℕ} (D:VacuumPolynomialData n) (E:VacuumPolynomialData (n+1)) :
    Nonempty (VacuumPolynomialData (n+2)) := by
  have bD:∀p,LaurentBox (D.W p) (fun _ =>2*(n+1)-2) := by
    simpa [Nat.mul_add] using D.box
  choose P hP bP using rationalNodalPolynomial_laurent_box D.W E.W D.eval_P E.eval_P bD E.box
  have hpair : ∀(h2:2≤(n+1)+1) (s:ℕ),s=2 ∨ s=3 →
      ∀(z:Fin ((n+1)+2) → SpectralField ((n+1)+2)) (hz:∀k,z k≠0),
      z (⟨1,by omega⟩:Fin ((n+1)+1)).castSucc=constF ((n+1)+2) phase^s*z (⟨0,by omega⟩:Fin ((n+1)+1)).castSucc → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
    intro h2 s hs z hz hh p
    rcases hs with rfl|rfl
    · exact pairEvaluation_zero_universal 2 _
        (residual_pair_merge D.W D.eval_P E.P E.map_P E.eval_P P hP p) z hz hh
    · exact pairEvaluation_zero_universal 3 _
        (residual_pair_delete D.W D.eval_P D.P D.map_P D.eval_P P hP p) z hz hh
  have hs:∀p,rationalInterpolationResidual (n+2) p=0 :=
    residual_saturation P hP (by simpa [Nat.mul_add] using bP)
      (residual_flat_universal D.W D.eval_P E P hP) hpair
  have he:=interpolant_eq_vacuum_of_residual hs
  exact ⟨⟨P,hP,by simpa [Nat.mul_add] using bP,
    fun p =>by rw [lastLaurent_map p (P p) (hP p)]; exact congrFun he p⟩⟩

theorem vacuumData_exists : ∀n,Nonempty (VacuumPolynomialData n) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨vacuumData_zero⟩
  | one => exact vacuumData_one_exists
  | more n hn hn1 =>
    obtain ⟨D⟩:=hn
    obtain ⟨E⟩:=hn1
    exact vacuumData_step_exists D E

noncomputable def vacuumData (n:ℕ) : VacuumPolynomialData n := Classical.choice (vacuumData_exists n)



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
open scoped Classical


def polynomialVacuumVector : (n:ℕ) → Pairing n → Laurent n
  | 0 =>fun _ =>1
  | n+1 =>(vacuumData n).W

end




noncomputable section
open scoped BigOperators Classical



def polynomialNorthSource (n : ℕ) (p : SourcePairing n) : Laurent n :=
  constantL n (1/(2*(d:ℂ))) * ((vacuumData n).P p.val).coeff (n-1)

end




end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NorthMerging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators



def polynomialNorthGluing (n : ℕ) : Laurent n :=
  sourceGlue (K:=Laurent n) n (fun p => reflectLaurent n (polynomialNorthSource n p))
    (polynomialNorthSource n)

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PhysicalStationarity
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators Classical
open Finset _root_.Matrix

 
def angleScalar {n : ℕ} (u : Fin n → ℝ) : ℂ :=
  angleEvaluation u (polynomialVacuumVector n (empty n))

 

def angleVacuum {n : ℕ} (u : Fin n → ℝ) (p : Pairing n) : ℝ :=
  (angleEvaluation u (polynomialVacuumVector n p)/angleScalar u).re

def angleNorthSource {n : ℕ} (u : Fin n → ℝ) (p : SourcePairing n) : ℝ :=
  (angleEvaluation u (polynomialNorthSource n p)/angleScalar u).re

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_AugmentedColumn
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators Classical
open Finset _root_.Matrix



def angleAugmented {n : ℕ} (u : Fin n → ℝ) : Pairing (n+1) → ℝ :=
  augmentVector (angleVacuum u) (angleNorthSource u)

end





end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NorthBijection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip.Diagram





noncomputable section
open scoped BigOperators Classical

 

def realNorthSeparator (n : ℕ) : ℝ :=
  sourceGlue n (angleNorthSource (fun _ : Fin n=>2*lambda))
    (angleNorthSource (fun _ : Fin n=>lambda))

end
end CriticalStrip.Diagram

end OAI
end


