-- Prove2me | Definitions.Def_OAIQ368Chrom064
-- name    : OAIQ368Chrom064
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:35:39.721771+00:00
-- url     : https://prove2.me/theorems/16996cda-dd2a-49b0-8908-b02d9f08aa0d
-- title:
--   Definitions bundle OAIQ368Chrom064 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 6 definitions, 2 instances and 1 theorem. The definitions and types are `OAI.ElementaryPositivity.FiniteSearch.Test`, `OAI.ElementaryPositivity.FiniteSearch.WordOK`, `OAI.ElementaryPositivity.FiniteSearch.colorCount`, `OAI.ElementaryPositivity.FiniteSearch.witnessCount`, `OAI.ElementaryPositivity.FiniteSearch.wordEnergy`, `OAI.ElementaryPositivity.FiniteSearch.wordEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Witness_HistoryMainWitness`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/HistoryMainWitness.lean).
--
--   **Imports.** It imports the published bundle `Def_ElementaryPositivity`; the bundles `OAIQ368Chrom058` and `OAIQ368Chrom062` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom065` and `OAIQ368Chrom067`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom058
import Definitions.Def_OAIQ368Chrom062

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
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

def WordOK (w:Fin n → Fin n):Prop:=Function.Bijective w ∧
  ∀i j:Fin n,i.val+1=j.val → w j<w i → G.Edge (w i) (w j)
instance instDecidableWordOK (w:Fin n → Fin n):Decidable (WordOK G w):=
  inferInstanceAs (Decidable (Function.Bijective w ∧ ∀i j:Fin n,
    i.val+1=j.val → w j<w i → G.Edge (w i) (w j)))

def wordEnergy (w:Fin n → Fin n):ℕ:=
  (Finset.univ.filter fun ij:Fin n × Fin n=>
    ij.1 < ij.2 ∧ w ij.2 < w ij.1 ∧ G.Edge (w ij.1) (w ij.2)).card

def colorCount (a:Fin n → ℕ) (k:ℕ):ℕ:=∑κ:Fin n → Fin n,
  if G.Proper κ ∧ (∀c,(Finset.univ.filter (fun j=>κ j=c)).card=a c) ∧ G.coloringAscents κ=k then 1 else 0

def witnessCount (t:Table n) (a:Fin n → ℕ) (k:ℕ):ℕ:=∑w:Fin n → Fin n,
  if WordOK G w ∧ wordEnergy G w=k then matrixCount (t w) a else 0

def Test (t:Table n):Prop:=∀a:Fin n → Fin (n+1),∀k:Fin (G.edgeCount+1),
  colorCount G (fun c=>(a c).val) k.val=witnessCount G t (fun c=>(a c).val) k.val
instance instDecidableTest (t:Table n):Decidable (Test G t):=inferInstanceAs (Decidable (∀a:Fin n → Fin (n+1),
  ∀k:Fin (G.edgeCount+1),colorCount G (fun c=>(a c).val) k.val=witnessCount G t (fun c=>(a c).val) k.val))

end ElementaryPositivity.FiniteSearch

end
section
namespace ElementaryPositivity.FiniteSearch
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

def wordEquiv : {σ:Equiv.Perm (Fin n) // G.Nondescent σ} ≃ {w:Fin n → Fin n // WordOK G w} where
  toFun σ:=⟨σ.val,σ.val.bijective,σ.property⟩
  invFun w:=⟨Equiv.ofBijective w.val w.property.1,w.property.2⟩
  left_inv σ:=by apply Subtype.ext; exact Equiv.ext (fun _=>rfl)
  right_inv _:=rfl

lemma colorCount_zero_high (a:Fin n → ℕ) (k:ℕ) (hk:G.edgeCount<k):colorCount G a k=0 := by
  unfold colorCount
  apply Finset.sum_eq_zero
  intro κ hκ
  rw [ite_eq_right]
  rintro ⟨hp,_,he⟩
  have h:=G.coloringInversions_add_ascents κ hp
  omega
end
end ElementaryPositivity.FiniteSearch

end

end OAI
end


