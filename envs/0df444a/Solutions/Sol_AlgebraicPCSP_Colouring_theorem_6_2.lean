-- Prove2me | solution 1 for AlgebraicPCSP.Colouring.theorem_6_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:07:11.017629+00:00
-- url     : https://prove2.me/submissions/8f2750e8-8806-4a58-abc1-c42f04947293

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Colouring_Minion
import Definitions.Def_AlgebraicPCSP_Colouring_Structures

open PCSPBLPAff.Symmetric
open AlgebraicPCSP.Colouring

namespace Thm62Proof

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

def rowIdx (r : Fin 3 → Fin 2) : Fin 6 :=
  if r 0 = 0 then
    if r 1 = 0 then 0
    else if r 2 = 0 then 1 else 5
  else
    if r 1 = 0 then
      if r 2 = 0 then 2 else 4
    else 3

lemma exampleMatrix_rowIdx (r : Fin 3 → Fin 2) (hr : ¬ (r 0 = r 1 ∧ r 1 = r 2)) :
    (exampleMatrix (rowIdx r) 0 = r 0 ∧
     exampleMatrix (rowIdx r) 1 = r 1 ∧
     exampleMatrix (rowIdx r) 2 = r 2) := by
  unfold rowIdx
  revert hr
  generalize r 0 = r0, r 1 = r1, r 2 = r2
  intro hr
  fin_cases r0 <;> fin_cases r1 <;> fin_cases r2 <;> revert hr <;> decide

end Thm62Proof

theorem solution {A B : Type} [Fintype A] [Fintype B] (M : Minion A B) :
    (∃ (K : ℕ) (hK : 2 ≤ K)
        (ξ : (n : ℕ) → ((Fin n → A) → B) → ((Fin n → Fin 2) → Fin K)),
        IsMinionHom M (HMinion K hK) ξ) ↔
      ¬ ContainsOlsak M := by
  constructor
  · rintro ⟨K, hK, ξ, hmem, hmin⟩ ⟨o, ho, hols⟩
    have hg : ξ 6 o ∈ (HMinion K hK).mem 6 := hmem 6 o ho
    have hrows : ∀ l : Fin 6, Thm62Proof.exampleMatrix l ∈ (Hgraph 2).rel () := by
      intro l
      change ¬ (Thm62Proof.exampleMatrix l 0 = Thm62Proof.exampleMatrix l 1 ∧
        Thm62Proof.exampleMatrix l 1 = Thm62Proof.exampleMatrix l 2)
      fin_cases l <;> decide
    have hcol := hg.2 () Thm62Proof.exampleMatrix hrows
    change ¬ (ξ 6 o Thm62Proof.π0 = ξ 6 o Thm62Proof.π1 ∧
      ξ 6 o Thm62Proof.π1 = ξ 6 o Thm62Proof.π2) at hcol
    have ho01 : (fun x : Fin 2 → A => o (x ∘ Thm62Proof.π0)) =
        (fun x : Fin 2 → A => o (x ∘ Thm62Proof.π1)) := by
      funext u
      rw [Thm62Proof.comp_π0, Thm62Proof.comp_π1]
      exact (hols (u 0) (u 1)).1
    have ho12 : (fun x : Fin 2 → A => o (x ∘ Thm62Proof.π1)) =
        (fun x : Fin 2 → A => o (x ∘ Thm62Proof.π2)) := by
      funext u
      rw [Thm62Proof.comp_π1, Thm62Proof.comp_π2]
      exact (hols (u 0) (u 1)).2
    have hξ0 : ξ 6 o Thm62Proof.π0 = ξ 2 (fun x => o (x ∘ Thm62Proof.π0)) id := by
      have := congr_fun (hmin 6 2 Thm62Proof.π0 o ho) id
      exact this.symm
    have hξ1 : ξ 6 o Thm62Proof.π1 = ξ 2 (fun x => o (x ∘ Thm62Proof.π1)) id := by
      have := congr_fun (hmin 6 2 Thm62Proof.π1 o ho) id
      exact this.symm
    have hξ2 : ξ 6 o Thm62Proof.π2 = ξ 2 (fun x => o (x ∘ Thm62Proof.π2)) id := by
      have := congr_fun (hmin 6 2 Thm62Proof.π2 o ho) id
      exact this.symm
    apply hcol
    rw [hξ0, hξ1, hξ2, ho01, ho12]
    exact ⟨rfl, rfl⟩
  · intro hno
    classical
    let e := Fintype.equivFin ((Fin 2 → A) → B)
    let K := max 2 (Fintype.card ((Fin 2 → A) → B))
    have hK : 2 ≤ K := le_max_left _ _
    have hle : Fintype.card ((Fin 2 → A) → B) ≤ K := le_max_right _ _
    let emb : ((Fin 2 → A) → B) → Fin K := fun b => Fin.castLE hle (e b)
    have hemb : Function.Injective emb := (Fin.castLE_injective hle).comp e.injective
    let ξ : (n : ℕ) → ((Fin n → A) → B) → ((Fin n → Fin 2) → Fin K) :=
      fun n f v => emb (fun u => f (u ∘ v))
    refine ⟨K, hK, ξ, ?_, ?_⟩
    · intro n f hf
      refine ⟨Nat.pos_of_ne_zero fun hn => ?_, ?_⟩
      · subst hn
        rw [M.mem_zero] at hf
        exact hf
      · intro _ mat hmat
        rintro ⟨h01, h12⟩
        have hf01 : (fun u : Fin 2 → A => f (u ∘ fun l => mat l 0)) =
            (fun u : Fin 2 → A => f (u ∘ fun l => mat l 1)) := hemb h01
        have hf12 : (fun u : Fin 2 → A => f (u ∘ fun l => mat l 1)) =
            (fun u : Fin 2 → A => f (u ∘ fun l => mat l 2)) := hemb h12
        let ρ : Fin n → Fin 6 := fun l => Thm62Proof.rowIdx (mat l)
        have hmat0 : (fun l => mat l 0) = Thm62Proof.π0 ∘ ρ := by
          funext l
          exact (Thm62Proof.exampleMatrix_rowIdx (mat l) (hmat l)).1.symm
        have hmat1 : (fun l => mat l 1) = Thm62Proof.π1 ∘ ρ := by
          funext l
          exact (Thm62Proof.exampleMatrix_rowIdx (mat l) (hmat l)).2.1.symm
        have hmat2 : (fun l => mat l 2) = Thm62Proof.π2 ∘ ρ := by
          funext l
          exact (Thm62Proof.exampleMatrix_rowIdx (mat l) (hmat l)).2.2.symm
        let o : (Fin 6 → A) → B := fun w => f (w ∘ ρ)
        have ho : o ∈ M.mem 6 := M.minor_closed ρ f hf
        apply hno
        refine ⟨o, ho, fun x y => ?_⟩
        let u : Fin 2 → A := ![x, y]
        have hu0 : ![x, x, y, y, y, x] = u ∘ Thm62Proof.π0 := (Thm62Proof.comp_π0 u).symm
        have hu1 : ![x, y, x, y, x, y] = u ∘ Thm62Proof.π1 := (Thm62Proof.comp_π1 u).symm
        have hu2 : ![y, x, x, x, y, y] = u ∘ Thm62Proof.π2 := (Thm62Proof.comp_π2 u).symm
        change o ![x, x, y, y, y, x] = o ![x, y, x, y, x, y] ∧
          o ![x, y, x, y, x, y] = o ![y, x, x, x, y, y]
        rw [hu0, hu1, hu2]
        dsimp [o]
        rw [Function.comp_assoc, Function.comp_assoc, Function.comp_assoc,
          ← hmat0, ← hmat1, ← hmat2]
        exact ⟨congr_fun hf01 u, congr_fun hf12 u⟩
    · intro m n π g _
      rfl
