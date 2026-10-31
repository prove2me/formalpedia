-- Prove2me | solution 1 for AlgebraicPCSP.Colouring.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:07:10.460502+00:00
-- url     : https://prove2.me/submissions/a776a60c-3777-4d9f-a46e-e38dc78ee68a

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Colouring_Minion
import Definitions.Def_AlgebraicPCSP_Colouring_Structures
import Theorems.Thm_AlgebraicPCSP_Colouring_theorem_6_5_core

open PCSPBLPAff.Symmetric
open AlgebraicPCSP.Colouring

namespace Lemma64Proof

def π0 : Fin 6 → Fin 2 := ![0, 0, 1, 1, 1, 0]
def π1 : Fin 6 → Fin 2 := ![0, 1, 0, 1, 0, 1]
def π2 : Fin 6 → Fin 2 := ![1, 0, 0, 0, 1, 1]

def exampleMatrix : Fin 6 → Fin 3 → Fin 2 :=
  fun l c =>
    match c with
    | 0 => π0 l
    | 1 => π1 l
    | 2 => π2 l

lemma comp_π0 {α : Type*} (u : Fin 2 → α) :
    u ∘ π0 = ![u 0, u 0, u 1, u 1, u 1, u 0] := by
  ext i
  fin_cases i <;> rfl

lemma comp_π1 {α : Type*} (u : Fin 2 → α) :
    u ∘ π1 = ![u 0, u 1, u 0, u 1, u 0, u 1] := by
  ext i
  fin_cases i <;> rfl

lemma comp_π2 {α : Type*} (u : Fin 2 → α) :
    u ∘ π2 = ![u 1, u 0, u 0, u 0, u 1, u 1] := by
  ext i
  fin_cases i <;> rfl

end Lemma64Proof

theorem solution (k : ℕ) (hk : 3 ≤ k) :
    ¬ ContainsOlsak
      (Pol (Kgraph k) (Kgraph (2 * k - 1)) (Kgraph_template (by omega))) := by
  obtain ⟨K, hK, ξ, hmem, hmin⟩ := theorem_6_5_core k hk
  rintro ⟨o, ho, hols⟩
  have hg : ξ 6 o ∈ (HMinion K hK).mem 6 := hmem 6 o ho
  have hrows : ∀ l : Fin 6, Lemma64Proof.exampleMatrix l ∈ (Hgraph 2).rel () := by
    intro l
    change ¬ (Lemma64Proof.exampleMatrix l 0 = Lemma64Proof.exampleMatrix l 1 ∧
      Lemma64Proof.exampleMatrix l 1 = Lemma64Proof.exampleMatrix l 2)
    fin_cases l <;> decide
  have hcol := hg.2 () Lemma64Proof.exampleMatrix hrows
  change ¬ (ξ 6 o Lemma64Proof.π0 = ξ 6 o Lemma64Proof.π1 ∧
    ξ 6 o Lemma64Proof.π1 = ξ 6 o Lemma64Proof.π2) at hcol
  have ho01 : (fun x : Fin 2 → Fin k => o (x ∘ Lemma64Proof.π0)) =
      (fun x : Fin 2 → Fin k => o (x ∘ Lemma64Proof.π1)) := by
    funext u
    rw [Lemma64Proof.comp_π0, Lemma64Proof.comp_π1]
    exact (hols (u 0) (u 1)).1
  have ho12 : (fun x : Fin 2 → Fin k => o (x ∘ Lemma64Proof.π1)) =
      (fun x : Fin 2 → Fin k => o (x ∘ Lemma64Proof.π2)) := by
    funext u
    rw [Lemma64Proof.comp_π1, Lemma64Proof.comp_π2]
    exact (hols (u 0) (u 1)).2
  have hξ0 : ξ 6 o Lemma64Proof.π0 = ξ 2 (fun x => o (x ∘ Lemma64Proof.π0)) id := by
    have := congr_fun (hmin 6 2 Lemma64Proof.π0 o ho) id
    exact this.symm
  have hξ1 : ξ 6 o Lemma64Proof.π1 = ξ 2 (fun x => o (x ∘ Lemma64Proof.π1)) id := by
    have := congr_fun (hmin 6 2 Lemma64Proof.π1 o ho) id
    exact this.symm
  have hξ2 : ξ 6 o Lemma64Proof.π2 = ξ 2 (fun x => o (x ∘ Lemma64Proof.π2)) id := by
    have := congr_fun (hmin 6 2 Lemma64Proof.π2 o ho) id
    exact this.symm
  apply hcol
  rw [hξ0, hξ1, hξ2, ho01, ho12]
  exact ⟨rfl, rfl⟩
