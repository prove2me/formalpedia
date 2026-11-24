-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SplPlane
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SplPlane
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:07.880348+00:00
-- url     : https://prove2.me/theorems/eb5fd0ec-968d-42c4-8892-2ea7393e79ce
-- title:
--   Spl Plane
-- statement:
--   Definitions and structural lemmas for Spl Plane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SplPlane.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.LocCartanPair
variable {R : Type} [CommRing R] [StarRing R]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
def splBasis (E : Fin 2 ⊕ κ ≃ ι) (x y : ι → R) : Matrix ι (Fin 2 ⊕ κ) R :=
  fun i c => Sum.elim (fun a => ![x, y] a i) (fun j => (1 : Matrix ι ι R) i (E (.inr j))) c
def splCorr (E : Fin 2 ⊕ κ ≃ ι) (A : Matrix ι ι R) (x y : ι → R) : Matrix (Fin 2) κ R :=
  fun a j => ![-(star y ⬝ᵥ (A *ᵥ fun i => (1 : Matrix ι ι R) i (E (.inr j)))),
    -(star x ⬝ᵥ (A *ᵥ fun i => (1 : Matrix ι ι R) i (E (.inr j))))] a
section Local
variable {R : Type} [CommRing R] [StarRing R]
def splEquiv {ι : Type} [DecidableEq ι] (i₀ j₀ : ι) (hne : i₀ ≠ j₀) :
    Fin 2 ⊕ {j // j ≠ i₀ ∧ j ≠ j₀} ≃ ι where
  toFun := Sum.elim ![i₀, j₀] Subtype.val
  invFun j := if h0 : j = i₀ then .inl 0 else if h1 : j = j₀ then .inl 1 else .inr ⟨j, h0, h1⟩
  left_inv := by
    rintro (a | ⟨j, h0, h1⟩)
    · fin_cases a
      · simp
      · simp [hne.symm]
    · simp [h0, h1]
  right_inv := by
    intro j
    by_cases h0 : j = i₀
    · subst h0; simp
    · by_cases h1 : j = j₀
      · subst h1; simp [h0]
      · simp [h0, h1]
end Local
end PI.LocCartanPair


