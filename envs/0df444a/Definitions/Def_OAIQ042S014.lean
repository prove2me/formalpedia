-- Prove2me | Definitions.Def_OAIQ042S014
-- name    : OAIQ042S014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T02:04:30.24218+00:00
-- url     : https://prove2.me/theorems/588ae5e7-b432-4f3e-8a41-e746bdc6da75
-- title:
--   Definitions bundle OAIQ042S014 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 1 definition and 5 theorems. The definitions and types are `OAI.CriticalStrip.Diagram.rowGauge`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: [`StripMass_ArchRoots`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/ArchRoots.lean), [`StripMass_BottomGauge`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/BottomGauge.lean), [`StripMass_PairSelfNode`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/PairSelfNode.lean), [`StripMass_ScalarMergeTrig`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/ScalarMergeTrig.lean).
--
--   **Imports.** It imports the bundle `OAIQ042S011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ042S015`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ042S011

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarMergeTrig
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section






open scoped Classical


lemma scalarValue_fcos_merge {m r:ℕ} (i:Fin m) (k:ℤ)
    (s:Fin r → Fin m) (hs:Function.Injective s) (hi:∀j,s j≠i) (l:Fin r → ℤ) :
    scalarValue (algebraMap ℂ (SpectralField m))
      (Fin.cons (fcos i (k-2)) (Fin.cons (fcos i (k+2)) (fun j =>fcos (s j) (l j))))=
      (fcos i (k-2)+fcos i (k+2)+constF m rho)*
        (∏j,(fcos (s j) (l j)+fcos i k))*
          scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i k) (fun j =>fcos (s j) (l j))) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero =>
      have he:(Fin.cons (fcos i (k+2)) (fun j:Fin 0 =>fcos (s j) (l j)):Fin 1 → SpectralField m)=fun _ =>fcos i (k+2) := by ext j; fin_cases j; rfl
      have ht:(Fin.cons (fcos i k) (fun j:Fin 0 =>fcos (s j) (l j)):Fin 1 → SpectralField m)=fun _ =>fcos i k := by ext j; fin_cases j; rfl
      rw [he,ht,scalarValue_two,scalarValue_one]
      simp [constF]
    | succ n =>
      let a:Fin n → SpectralField m:=fun j =>fcos (s j.succ) (l j.succ)
      have htail:=ih n (by omega) (fun j =>s j.succ) (hs.comp (Fin.succ_injective _)) (fun j =>hi j.succ) (fun j =>l j.succ)
      change scalarValue _ (Fin.cons (fcos i (k-2)) (Fin.cons (fcos i (k+2)) a))=_ at htail
      let P:=scalarMergeDiff (algebraMap ℂ (SpectralField m)) (fcos i (k-2)) (fcos i (k+2)) (fcos i k) a
      have hd:P.natDegree≤n+1:=scalarMergeDiff_degree_reduced _ _ _ _ a htail
      let roots:Fin (n+2) → SpectralField m:=Fin.cons (constF m c) (Fin.cons (fcos i (k+8)) (fun j =>fcos (s j.succ) (l j.succ+6)))
      have hinj:Function.Injective roots:=scalarMerge_nodes_injective i k _ (hs.comp (Fin.succ_injective _)) (fun j =>hi j.succ) _
      have hr:∀j,P.eval (roots j)=0 := by
        intro j
        induction j using Fin.cases with
        | zero => exact scalarMergeDiff_eval_flat i k a htail
        | succ j =>
          induction j using Fin.cases with
          | zero => simpa only [roots,Fin.cons_succ,Fin.cons_zero,fcos_eight] using scalarMergeDiff_eval_neg i k a
          | succ j =>
            cases n with
            | zero => exact Fin.elim0 j
            | succ v =>
              have hdel:=ih v (by omega) (fun t =>s (j.succAbove t).succ)
                (hs.comp ((Fin.succ_injective _).comp (Fin.succAbove_right_injective)))
                (fun t =>hi (j.succAbove t).succ) (fun t =>l (j.succAbove t).succ)
              exact scalarMergeDiff_eval_deletion i k a j (s j.succ) (l j.succ) rfl hdel
      have hp:P=0:=Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hinj hr (by simp only [Fintype.card_fin]; omega)
      have he:=congrArg (fun Q:Polynomial (SpectralField m) =>Q.eval (fcos (s 0) (l 0))) hp
      simp only [Polynomial.eval_zero] at he
      rw [scalarMergeDiff_eval] at he
      have ha:(fun j =>fcos (s j) (l j))=Fin.cons (fcos (s 0) (l 0)) a:= by ext j; induction j using Fin.cases <;> rfl
      rw [ha,scalarValue_rotate3,scalarValue_swap_head _ (fcos i k) (fcos (s 0) (l 0))]
      simp only [Fin.prod_univ_succ]
      dsimp only [constF] at *
      linear_combination he

end

 

 

noncomputable section
open scoped Classical



theorem scalarValue_fcos_merge_all {m r:ℕ} (i:Fin m) (k:ℤ)
    (s:Fin r → Fin m) (l:Fin r → ℤ) :
    scalarValue (algebraMap ℂ (SpectralField m))
      (Fin.cons (fcos i (k-2)) (Fin.cons (fcos i (k+2)) (fun j =>fcos (s j) (l j))))=
      (fcos i (k-2)+fcos i (k+2)+constF m rho)*
        (∏j,(fcos (s j) (l j)+fcos i k))*
          scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i k) (fun j =>fcos (s j) (l j))) := by
  let v:Fin (r+1) → Fin m:=Fin.cons i s
  let φ:=copyEvaluation v
  have h:=scalarValue_fcos_merge (0:Fin (r+1)) k Fin.succ (Fin.succ_injective _) (fun j =>Fin.succ_ne_zero j) l
  have ht:RationalAt φ.toRingHom
      (scalarValue (algebraMap ℂ (SpectralField (r+1))) (Fin.cons (fcos 0 (k-2)) (Fin.cons (fcos 0 (k+2)) (fun j =>fcos j.succ (l j)))))
      (scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i (k-2)) (Fin.cons (fcos i (k+2)) (fun j =>fcos (s j) (l j))))) := by
    apply rationalAt_scalarValue
    intro j
    induction j using Fin.cases with
    | zero => exact rationalAt_copy_fcos v 0 (k-2)
    | succ j => induction j using Fin.cases with
      | zero => exact rationalAt_copy_fcos v 0 (k+2)
      | succ j => exact rationalAt_copy_fcos v j.succ (l j)
  have hv:RationalAt φ.toRingHom
      (scalarValue (algebraMap ℂ (SpectralField (r+1))) (Fin.cons (fcos 0 k) (fun j =>fcos j.succ (l j))))
      (scalarValue (algebraMap ℂ (SpectralField m)) (Fin.cons (fcos i k) (fun j =>fcos (s j) (l j)))) := by
    apply rationalAt_scalarValue
    intro j
    induction j using Fin.cases with
    | zero => exact rationalAt_copy_fcos v 0 k
    | succ j => exact rationalAt_copy_fcos v j.succ (l j)
  have hp:=RationalAt.prod Finset.univ
    (fun j:Fin r =>fcos j.succ (l j)+fcos (0:Fin (r+1)) k)
    (fun j:Fin r =>fcos (s j) (l j)+fcos i k)
    (fun j _ => (rationalAt_copy_fcos v j.succ (l j)).add (rationalAt_copy_fcos v 0 k))
  have hq:=((rationalAt_copy_fcos v 0 (k-2)).add (rationalAt_copy_fcos v 0 (k+2))).add (rationalAt_const φ rho)
  rw [h] at ht
  exact ht.unique ((hq.mul hp).mul hv)







end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PairSelfNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma scalar_pair_merge (n:ℕ) :
    scalarValue (algebraMap ℂ (SpectralField (n+1))) (pairCosines n 2)=
      mergePairScalar n*scalarValue (algebraMap ℂ (SpectralField (n+1)))
        (Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3))) := by
  exact scalarValue_fcos_merge_all 0 (-1) Fin.succ (fun _:Fin n =>(-3))

lemma scalar_pair_merge_snoc {n:ℕ} (i:Fin (n+2)) (hi:i≠1) :
    scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.snoc (pairCosines n 2) (pairBeta n 2 i))=
      mergePairScalar n*(pairBeta n 2 i+fcos 0 (-1))*
        scalarValue (algebraMap ℂ (SpectralField (n+1)))
          (Fin.snoc (Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3))) (pairBeta n 2 i)) := by
  rw [pairBeta_of_ne i hi]
  have he:=scalarValue_fcos_merge_all (0:Fin (n+1)) (-1)
    (Fin.snoc Fin.succ (pairIndex n i)) (Fin.snoc (fun _:Fin n =>(-3:ℤ)) 3)
  have hf:(fun j =>fcos ((Fin.snoc Fin.succ (pairIndex n i) : Fin (n+1) → Fin (n+1)) j)
      ((Fin.snoc (fun _:Fin n =>(-3:ℤ)) 3 : Fin (n+1) → ℤ) j))=
      Fin.snoc (fun j:Fin n =>fcos j.succ (-3)) (deletionBeta (pairIndex n i)) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp only [Fin.snoc_last,deletionBeta_shiftedCosine]
    | cast j => simp only [Fin.snoc_castSucc]
  rw [hf] at he
  simp only [Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last] at he
  unfold pairCosines
  rw [Fin.snoc_twoCons]
  norm_num only at he ⊢
  rw [he]
  simp only [deletionBeta_shiftedCosine]
  dsimp only [mergePairScalar]
  rw [←Fin.cons_snoc_eq_snoc_cons]
  ring







end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BottomGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators


def rowGauge {n : ℕ} (i : Fin n) : SpectralField n :=
  (spectralWeights n i).A / (spectralWeights n i).U

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

lemma archRoot_ne_zero {n : ℕ} (k : ArchRootIndex n) : archRoot k≠0 := by
  intro h
  have he : monomialL (archRootExponent k) (archRootScalar k)=0 :=
    IsFractionRing.injective (SpectralRing (n+2)) (SpectralField (n+2))
      (by simpa only [archRoot, evalLaurent,map_zero] using h)
  exact archRootScalar_ne_zero k (AddMonoidAlgebra.single_eq_zero.mp he)

end




end CriticalStrip.Diagram

end OAI
end


