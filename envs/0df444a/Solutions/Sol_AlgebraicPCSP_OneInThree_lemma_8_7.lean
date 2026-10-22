-- Prove2me | solution 1 for AlgebraicPCSP.OneInThree.lemma_8_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:47:12.722498+00:00
-- url     : https://prove2.me/submissions/73ade455-793f-4773-9107-cd852b362b26

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices
set_option autoImplicit false
open AlgebraicPCSP.OneInThree
open PCSPBLPAff.Symmetric

lemma ss_cover_cases : ∀ a b c : Fin 2, a.val + b.val + c.val = 1 →
    (![a, b, c] : Fin 3 → Fin 2) = ![1, 0, 0] ∨ (![a, b, c] : Fin 3 → Fin 2) = ![0, 1, 0] ∨
      (![a, b, c] : Fin 3 → Fin 2) = ![0, 0, 1] := by decide

theorem solution {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (X Y Z : Fin p → Fin p → Fin 2) (hcover : IsCover X Y Z) :
    ¬ (GEquiv f g s X Y ∧ GEquiv f g s Y Z) := by
  rintro ⟨hXY, hYZ⟩
  have hrow : ∀ i j, (![f (X i j), f (Y i j), f (Z i j)] : Fin 3 → D) ∈ R := by
    intro i j
    have hmem : (![X i j, Y i j, Z i j] : Fin 3 → Fin 2) ∈ oneInThree.rel () := by
      have := ss_cover_cases (X i j) (Y i j) (Z i j) (hcover i j)
      exact this
    have := hf () _ hmem
    have e : (f ∘ (![X i j, Y i j, Z i j] : Fin 3 → Fin 2)) =
        (![f (X i j), f (Y i j), f (Z i j)] : Fin 3 → D) := by
      ext k; fin_cases k <;> rfl
    rw [e] at this
    exact this
  have hcol : ∀ j, (fun c : Fin 3 => s (fun i : Fin p => (![f (X i j), f (Y i j), f (Z i j)] : Fin 3 → D) c)) ∈ R := by
    intro j
    exact hs () (fun i => (![f (X i j), f (Y i j), f (Z i j)] : Fin 3 → D)) (fun i => hrow i j)
  have htot := hs () (fun j => fun c : Fin 3 => s (fun i : Fin p => (![f (X i j), f (Y i j), f (Z i j)] : Fin 3 → D) c)) hcol
  have hgt := hg () _ htot
  have e2 : (g ∘ fun c : Fin 3 => s (fun j : Fin p => (fun c : Fin 3 => s (fun i : Fin p => (![f (X i j), f (Y i j), f (Z i j)] : Fin 3 → D) c)) c)) =
      ![g (tOp s (fun i j => f (X i j))), g (tOp s (fun i j => f (Y i j))), g (tOp s (fun i j => f (Z i j)))] := by
    ext k; fin_cases k <;> rfl
  have hgt' : (![g (tOp s (fun i j => f (X i j))), g (tOp s (fun i j => f (Y i j))), g (tOp s (fun i j => f (Z i j)))] : Fin 3 → Fin 2) ∈ nae.rel () := by
    rw [← e2]; exact hgt
  unfold GEquiv at hXY hYZ
  rw [← hYZ, ← hXY] at hgt'
  obtain ⟨h0, h1⟩ := hgt'
  generalize g (tOp s (fun i j => f (X i j))) = a at h0 h1
  fin_cases a
  · exact h0 rfl
  · exact h1 rfl
