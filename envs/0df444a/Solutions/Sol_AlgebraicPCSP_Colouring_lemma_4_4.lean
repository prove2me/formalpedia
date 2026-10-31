-- Prove2me | solution 1 for AlgebraicPCSP.Colouring.lemma_4_4
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:57:56.374662+00:00
-- url     : https://prove2.me/submissions/55143b17-d040-4622-9e1c-4e706d574221

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Colouring_Minion
import Definitions.Def_AlgebraicPCSP_Colouring_FreeStructure

open PCSPBLPAff.Symmetric
open AlgebraicPCSP.Colouring

def unitMinion : Minion Unit Unit where
  mem n := { _f | 0 < n }
  mem_zero := by ext; simp
  nonempty := ⟨1, fun _ => (), Nat.one_pos⟩
  minor_closed := by
    intro m n π _ hm
    exact Fin.pos (π ⟨0, hm⟩)

theorem solution :
    ¬ (∀ {τ : Type} {ar : τ → ℕ} {A B A' B' : Type} {n : ℕ}
        (M : Minion A' B') (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B)
        (h : IsPromiseTemplate 𝔸 𝔹) (e : Fin n ≃ A),
        (∀ ξ : (m : ℕ) → ((Fin m → A') → B') → ((Fin m → A) → B),
            IsMinionHom M (Pol 𝔸 𝔹 h) ξ →
              IsHom (FreeStruct M 𝔸 e) 𝔹 (fun f => ξ n f.1 (fun i => e i))) ∧
        (∀ c : {f // f ∈ M.mem n} → B, IsHom (FreeStruct M 𝔸 e) 𝔹 c →
          ∃ ξ : (m : ℕ) → ((Fin m → A') → B') → ((Fin m → A) → B),
            IsMinionHom M (Pol 𝔸 𝔹 h) ξ ∧
            (∀ f : {f // f ∈ M.mem n}, ξ n f.1 (fun i => e i) = c f) ∧
            ∀ χ : (m : ℕ) → ((Fin m → A') → B') → ((Fin m → A) → B),
              IsMinionHom M (Pol 𝔸 𝔹 h) χ →
              (∀ f : {f // f ∈ M.mem n}, χ n f.1 (fun i => e i) = c f) →
              ∀ (m : ℕ) (g : (Fin m → A') → B'), g ∈ M.mem m → χ m g = ξ m g)) := by
  intro H
  let 𝔸 : RelStruct Empty (fun _ => 0) Empty := ⟨fun _ => ∅⟩
  let 𝔹 : RelStruct Empty (fun _ => 0) Empty := ⟨fun _ => ∅⟩
  have h : IsPromiseTemplate 𝔸 𝔹 := ⟨Empty.elim, fun R => R.elim⟩
  let e : Fin 0 ≃ Empty := ⟨Fin.elim0, Empty.elim, fun i => i.elim0, fun a => a.elim⟩
  let c : {f // f ∈ unitMinion.mem 0} → Empty := fun f => False.elim (Nat.lt_irrefl 0 f.2)
  have hc : IsHom (FreeStruct unitMinion 𝔸 e) 𝔹 c := fun R => R.elim
  rcases (H unitMinion 𝔸 𝔹 h e).2 c hc with ⟨ξ, -⟩
  exact Empty.elim (ξ 0 (fun _ => ()) Fin.elim0)
