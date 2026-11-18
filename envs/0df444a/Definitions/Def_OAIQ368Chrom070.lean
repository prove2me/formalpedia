-- Prove2me | Definitions.Def_OAIQ368Chrom070
-- name    : OAIQ368Chrom070
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T20:24:51.781788+00:00
-- url     : https://prove2.me/theorems/97cb9a3d-05f9-487e-ad45-1d396a53f1d7
-- title:
--   Definitions bundle OAIQ368Chrom070 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 2 definitions and 10 theorems. The definitions and types are `OAI.ElementaryPositivity.FiniteSearch.selectedTable`, `OAI.elementaryPositivityWitness`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Main`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Main.lean), [`Chromatic_Witness_ElementaryAlphabetRigidity`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/ElementaryAlphabetRigidity.lean), [`Chromatic_Witness_HistoryMainWitness`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/HistoryMainWitness.lean).
--
--   **Imports.** It imports the published bundle `Def_ElementaryPositivity`; the bundles `OAIQ368Chrom065` and `OAIQ368Chrom069` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.elementaryPositivityWitness_exists`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom065
import Definitions.Def_OAIQ368Chrom069

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_HistoryMainWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteSearch
open scoped BigOperators
open Packets
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

lemma rowPartition_eq_profile (v:Row n):rowPartition v=profilePartition (rowProfile v) (rowProfile_degree v):=rfl

lemma matrix_coefficient {R:Type*} [CommSemiring R] (v:Row n) (a:Fin n →₀ ℕ) :
    (MvPolynomial.esymmPart (Fin n) R (rowPartition v)).coeff a=(matrixCount v a:R) := by
  rw [rowPartition_eq_profile,esymmPart_profile,ElementaryMatrix.elementary_product_coeff]
  simp only [matrixCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro s hs
  have hr:ElementaryMatrix.rowCount s=rowProfile v ↔ ∀i,(s i).card=(v.val i).val:=
    ElementaryMatrix.rowCount_eq s _
  have hc:ElementaryMatrix.colCount s=a ↔ ∀c,(Finset.univ.filter (fun i=>c∈s i)).card=a c:=by
    rw [Finsupp.ext_iff]
    simp only [ElementaryMatrix.colCount_apply,ElementaryMatrix.transpose]
  simp only [hr,hc]

lemma witness_coefficient (t:Table n) (a:Fin n →₀ ℕ) (k:ℕ) :
    ((∑σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ},MvPolynomial.C (Polynomial.X^G.graphInversions σ.val)*
      MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (rowPartition (t σ.val))).coeff a).coeff k=
      witnessCount G t a k := by
  rw [←Equiv.sum_comp (wordEquiv G).symm]
  rw [MvPolynomial.coeff_sum,Polynomial.finsetSum_coeff]
  change (∑w:{w:Fin n → Fin n // WordOK G w},
    ((MvPolynomial.C (Polynomial.X^wordEnergy G w.val)*
      MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (rowPartition (t w.val))).coeff a).coeff k)=_
  simp only [MvPolynomial.coeff_C_mul,matrix_coefficient,Polynomial.coeff_mul_natCast,Polynomial.coeff_X_pow,Nat.cast_id]
  rw [sum_subtype_ite (WordOK G) (fun w => (if k = wordEnergy G w then 1 else 0) * (matrixCount (t w) a : ℕ))]
  unfold witnessCount
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hp:WordOK G w
  · by_cases hk:wordEnergy G w=k
    · simp [hp,hk]
    · have hk':k≠wordEnergy G w:=Ne.symm hk
      simp [hp,hk,hk']
  · simp [hp]

lemma row_degree_zero (v:Row n) (a:Fin n →₀ ℕ) (ha:a.degree≠n) :
    (MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (rowPartition v)).coeff a=0 := by
  rw [rowPartition_eq_profile,esymmPart_profile]
  exact ElementaryMatrix.elementary_product_coeff_zero _ _ (by simpa only [rowProfile_degree] using ha)

end
end ElementaryPositivity.FiniteSearch

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_ElementaryAlphabetRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteSearch
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

lemma test_of_expansion (t:Table n)
    (h:G.chromatic n=∑σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ},
      MvPolynomial.C (Polynomial.X^G.graphInversions σ.val)*
        MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (rowPartition (t σ.val))) : Test G t := by
  intro a k
  let af:Fin n →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun c=>(a c).val)
  have H:=congrArg (fun p:MvPolynomial (Fin n) (Polynomial ℕ)=>(p.coeff af).coeff k.val) h
  rw [chromatic_coefficient,witness_coefficient] at H
  exact H

lemma expansion_of_test (t:Table n) (ht:Test G t) :
    G.chromatic n=∑σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ},
      MvPolynomial.C (Polynomial.X^G.graphInversions σ.val)*
        MvPolynomial.esymmPart (Fin n) (Polynomial ℕ) (rowPartition (t σ.val)) := by
  apply MvPolynomial.ext
  intro a
  by_cases ha:a.degree=n
  · apply Polynomial.ext
    intro k
    rw [chromatic_coefficient,witness_coefficient]
    by_cases hk:k≤G.edgeCount
    · let af:Fin n → Fin (n+1):=fun c=>⟨a c,by have H:=Finsupp.le_degree c a; omega⟩
      exact ht af ⟨k,Nat.lt_succ_of_le hk⟩
    · rw [colorCount_zero_high G a k (by omega),witnessCount_zero_high G t a k (by omega)]
  · rw [chromatic_degree_zero G a ha,MvPolynomial.coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro σ hσ
    rw [MvPolynomial.coeff_C_mul,row_degree_zero _ _ ha,mul_zero]

lemma uniform_expansion_of_test (W:G.PermutationWitness) (t:Table n) (ht:Test G t) (r:ℕ) :
    G.chromatic r=∑σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ},
      MvPolynomial.C (Polynomial.X^G.graphInversions σ.val)*
        MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (rowPartition (t σ.val)) := by
  trans ∑σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ},
    MvPolynomial.C (Polynomial.X^G.graphInversions σ.val)*
      MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (W.theta σ)
  · exact W.expansion r
  · apply ElementaryRigidity.uniform_of_at_n
      (fun σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ}=>G.graphInversions σ.val)
      W.theta (fun σ=>rowPartition (t σ.val))
    trans G.chromatic n
    · exact (W.expansion n).symm
    · exact expansion_of_test G t ht

lemma exists_test (W:G.PermutationWitness) : ∃t:Table n,Test G t := by
  let p0:Nat.Partition n:=Nat.Partition.ofSums n {n} (by simp)
  let p:(Fin n → Fin n) → Nat.Partition n:=fun w=>
    if hw:WordOK G w then W.theta ⟨Equiv.ofBijective w hw.1,hw.2⟩ else p0
  let t:Table n:=fun w=>Classical.choose (rowPartition_surjective n (p w))
  have he:∀σ:{σ:Equiv.Perm (Fin n) // G.Nondescent σ},rowPartition (t σ.val)=W.theta σ:=by
    intro σ
    have H:rowPartition (t σ.val)=p σ.val:=Classical.choose_spec (rowPartition_surjective n (p σ.val))
    rw [H]
    have hp:WordOK G σ.val:=⟨σ.val.bijective,σ.property⟩
    dsimp only [p]
    rw [dite_eq_left hp]
    congr 1
    apply Subtype.ext
    exact Equiv.ext (fun _=>rfl)
  refine ⟨t,test_of_expansion G t ?_⟩
  simp_rw [he]
  exact W.expansion n
end
end ElementaryPositivity.FiniteSearch

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteSearch
variable {n : ℕ} (G : NaturalUnitIntervalGraph n)

theorem exists_successful_table : ∃ t : Table n, Test G t :=
  exists_test G G.historyWitness

def selectedTable : Table n := Encodable.choose (exists_successful_table G)

theorem selectedTable_test : Test G (selectedTable G) :=
  Encodable.choose_spec (exists_successful_table G)

end ElementaryPositivity.FiniteSearch

def elementaryPositivityWitness (n : ℕ)
    (G : ElementaryPositivity.NaturalUnitIntervalGraph n) : G.PermutationWitness where
  theta σ := ElementaryPositivity.FiniteSearch.rowPartition
    (ElementaryPositivity.FiniteSearch.selectedTable G σ.val)
  expansion r := ElementaryPositivity.FiniteSearch.uniform_expansion_of_test
    G G.historyWitness _ (ElementaryPositivity.FiniteSearch.selectedTable_test G) r

end

end OAI
end


