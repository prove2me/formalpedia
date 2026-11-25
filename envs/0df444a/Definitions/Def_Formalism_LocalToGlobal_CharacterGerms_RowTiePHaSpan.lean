-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:09.262107+00:00
-- url     : https://prove2.me/theorems/33034251-00b6-445f-abc7-3048c151d949
-- title:
--   Row Tie PHa Span
-- statement:
--   Definitions and structural lemmas for Row Tie PHa Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
section Sub
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) (k : Type) [Field k] (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
theorem hha_zero : (0 : MvPolynomial (Letter Ty r n) k) ∈ HHa r n k cc isX a := by
  refine ⟨Submodule.zero_mem _, fun σ i i' _ t => map_zero _, fun m hm => by simp at hm⟩
theorem hha_add {P Q : MvPolynomial (Letter Ty r n) k} (hP : P ∈ HHa r n k cc isX a) (hQ : Q ∈ HHa r n k cc isX a) :
    P + Q ∈ HHa r n k cc isX a := by
  obtain ⟨hP1, hP2, hP3⟩ := hP
  obtain ⟨hQ1, hQ2, hQ3⟩ := hQ
  refine ⟨Submodule.add_mem _ hP1 hQ1, fun σ i i' hii t => ?_, fun m hm => ?_⟩
  · rw [map_add, hP2 σ i i' hii t, hQ2 σ i i' hii t]
  · rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hP3 m h
    · exact hQ3 m h
theorem hha_smul (c : k) {P : MvPolynomial (Letter Ty r n) k} (hP : P ∈ HHa r n k cc isX a) :
    c • P ∈ HHa r n k cc isX a := by
  obtain ⟨hP1, hP2, hP3⟩ := hP
  refine ⟨Submodule.smul_mem _ c hP1, fun σ i i' hii t => ?_, fun m hm => hP3 m (support_smul hm)⟩
  rw [map_smul, hP2 σ i i' hii t]
end Sub
section Maps
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ)
end Maps
section Comp
variable {K : Type} [Field K] [CharZero K] {σ : Type}
def comp (lam : K →ₗ[ℚ] ℚ) (P : MvPolynomial σ K) : MvPolynomial σ ℚ :=
  ∑ m ∈ P.support, monomial m (lam (P.coeff m))
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) {cc : Ty → Ty} {isX : Ty → Prop} {a : Ty → ℕ → ℕ}
end Comp
section Up
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {cc : Ty → Ty} {isX : Ty → Prop} {a : Ty → ℕ → ℕ}
end Up
section Poly
variable {L : Type}
def poly {R : Type} [CommRing R] (Bd : Finset (L →₀ ℕ)) (v : Bd → R) : MvPolynomial L R :=
  ∑ b : Bd, monomial b.1 (v b)
theorem coeff_poly {R : Type} [CommRing R] (Bd : Finset (L →₀ ℕ)) (v : Bd → R) (m : L →₀ ℕ) :
    coeff m (poly Bd v) = if h : m ∈ Bd then v ⟨m, h⟩ else 0 := by
  unfold poly
  rw [coeff_sum]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hbm
      exact hb (Subtype.ext hbm)
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hbm
    exact h (hbm ▸ b.2)
theorem coeff_map_poly {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (Bd : Finset (L →₀ ℕ)) (v : Bd → R)
    (m : L →₀ ℕ) : coeff m (map φ (poly Bd v)) = if h : m ∈ Bd then φ (v ⟨m, h⟩) else 0 := by
  rw [coeff_map, coeff_poly, apply_dite φ, map_zero]
end Poly
section Main
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
def Wsub (Bd : Finset (Letter Ty r n →₀ ℕ)) : Submodule ℤ (Bd → ℤ) where
  carrier := {z | map (Int.castRingHom ℚ) (poly Bd z) ∈ HHa r n ℚ cc isX a}
  add_mem' := by
    intro x y hx hy
    have e : map (Int.castRingHom ℚ) (poly Bd (x + y)) =
        map (Int.castRingHom ℚ) (poly Bd x) + map (Int.castRingHom ℚ) (poly Bd y) := by
      ext m
      rw [coeff_add, coeff_map_poly, coeff_map_poly, coeff_map_poly]
      split_ifs <;> simp
    show map (Int.castRingHom ℚ) (poly Bd (x + y)) ∈ HHa r n ℚ cc isX a
    rw [e]
    exact hha_add r n ℚ cc isX a hx hy
  zero_mem' := by
    have e : map (Int.castRingHom ℚ) (poly Bd (0 : Bd → ℤ)) = 0 := by
      ext m
      rw [coeff_zero, coeff_map_poly]
      split_ifs <;> simp
    show map (Int.castRingHom ℚ) (poly Bd (0 : Bd → ℤ)) ∈ HHa r n ℚ cc isX a
    rw [e]
    exact hha_zero r n ℚ cc isX a
  smul_mem' := by
    intro c x hx
    have e : map (Int.castRingHom ℚ) (poly Bd (c • x)) = (c : ℚ) • map (Int.castRingHom ℚ) (poly Bd x) := by
      ext m
      rw [coeff_smul, coeff_map_poly, coeff_map_poly]
      split_ifs <;> simp
    show map (Int.castRingHom ℚ) (poly Bd (c • x)) ∈ HHa r n ℚ cc isX a
    rw [e]
    exact hha_smul r n ℚ cc isX a _ hx
end Main
section Assembly
end Assembly
end Formalism.L2.FormalSeriesBounds.HaP


