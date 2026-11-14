-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBSOGen
-- name    : RPLib_S4_AlgGrpBSOGen
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:57:11.237198+00:00
-- url     : https://prove2.me/theorems/c27bf165-4fe4-40ac-8cc7-e601918ccd01
-- title:
--   Larsen's alternative library: `Lie H ⊇ so(B)` forces `H ⊇ SO(B)` for `SO`, O5b)
-- statement:
--   `K` algebraically closed of characteristic 0, `B` symmetric nondegenerate, `3 ≤ n`. A Zariski closed
--   subgroup `H` of `GL_n(K)` with `so(B) = {X | Xᵀ B + B X = 0} ⊆ Lie H` contains `SO(B)`
--   (`so_mem_of_so_le_lieS`). Proof: `fix_induct` with `M = isoSub B ⊓ detOne`; the step is
--   `pair_trans_SO` when `{e, f, S}^⊥ ≠ 0`, `plane_base` (torus `tor` or a reflection, excluded by the
--   determinant) when it is `0`, and `aniso_base` when `orthS B S` has no isotropic vector.
--   `n = 2` (`SO(2)` is a torus) is not covered.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBSOBase
import Definitions.Def_RPLib_S4_AlgGrpBSOMove
import Definitions.Def_RPLib_S4_AlgGrpBSOTorus

/-!
# S4-AlgGrpB, file SOGen: `Lie H ⊇ so(B)` forces `H ⊇ SO(B)` (spike API (A4) for `SO`, O5b)

`K` algebraically closed of characteristic 0, `B` symmetric nondegenerate, `3 ≤ n`. A Zariski closed
subgroup `H` of `GL_n(K)` with `so(B) = {X | Xᵀ B + B X = 0} ⊆ Lie H` contains `SO(B)`
(`so_mem_of_so_le_lieS`). Proof: `fix_induct` with `M = isoSub B ⊓ detOne`; the step is
`pair_trans_SO` when `{e, f, S}^⊥ ≠ 0`, `plane_base` (torus `tor` or a reflection, excluded by the
determinant) when it is `0`, and `aniso_base` when `orthS B S` has no isotropic vector.
`n = 2` (`SO(2)` is a torus) is not covered.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

section Gen

attribute [local instance] zarTop

variable [CharZero K] [IsAlgClosed K] {B : Matrix n n K} (hB : Bᵀ = B)

include hB in
/-- A hyperbolic pair has a nonzero orthogonal complement when `3 ≤ card n`. -/
theorem orth_pair_ne_bot (hn : 3 ≤ Fintype.card n) {e f : n → K} (hee : bf B e e = 0)
    (hff : bf B f f = 0) (hef : bf B e f = 1) :
    DecS B (insert e (insert f ∅)) ∧ orthS B (insert e (insert f ∅)) ≠ ⊥ := by
  classical
  have h0 : ∀ x : n → K, x ∈ orthS B ∅ := fun _ s hs => absurd hs (Set.notMem_empty s)
  have hD := decS_insert (decS_empty B) (h0 e) (h0 f) hee hff hef
    (by rw [bf_swap_sym hB e f, hef]; exact one_ne_zero)
  refine ⟨hD, fun hbot => ?_⟩
  have htop : (⊤ : Submodule K (n → K)) ≤
      Submodule.span K (({e, f} : Finset (n → K)) : Set (n → K)) := by
    intro v _
    obtain ⟨s, hs, hvs⟩ := hD v
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hvs
    rw [hvs]
    refine Submodule.span_mono ?_ hs
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_singleton_iff] at hx ⊢
    exact hx
  have h1 := Submodule.finrank_mono htop
  rw [finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  have h2 := finrank_span_finset_le_card (R := K) ({e, f} : Finset (n → K))
  have h3 : ({e, f} : Finset (n → K)).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  unfold Set.finrank at h2
  omega

include hB in
/-- Base case `{e, f, S}^⊥ = 0`: `g` is a torus element (in `H`) or a reflection (impossible). -/
theorem plane_base (hnd : B.Nondegenerate) (hn : 3 ≤ Fintype.card n)
    {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K)))
    (hso : ∀ X : Matrix n n K, Xᵀ * B + B * X = 0 →
      X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    {S : Set (n → K)} (hD : DecS B S) {e f : n → K} (he : e ∈ orthS B S) (hf : f ∈ orthS B S)
    (hee : bf B e e = 0) (hff : bf B f f = 0) (hef : bf B e f = 1)
    (h0 : orthS B (insert e (insert f S)) = ⊥) {g : Matrix.GeneralLinearGroup n K}
    (hg : g ∈ isoSub B) (hdet : (g : Matrix n n K).det = 1)
    (hfix : ∀ s ∈ S, (g : Matrix n n K) *ᵥ s = s) : g ∈ H := by
  have hfe : bf B f e = 1 := by rw [bf_swap_sym hB e f, hef]
  have hD' := decS_insert hD he hf hee hff hef (by rw [hfe]; exact one_ne_zero)
  have span2 : ∀ w ∈ orthS B S, w = bf B f w • e + bf B e w • f := by
    intro w hw
    have hm : w - (bf B f w • e + bf B e w • f) ∈ orthS B (insert e (insert f S)) := by
      intro s hs
      rcases hs with rfl | rfl | hs
      · simp only [bf_sub_right, bf_add_right, bf_smul_right, hee, hef]; ring
      · simp only [bf_sub_right, bf_add_right, bf_smul_right, hff, hfe]; ring
      · simp only [bf_sub_right, bf_add_right, bf_smul_right, hw s hs, he s hs, hf s hs]; ring
    rw [h0, Submodule.mem_bot, sub_eq_zero] at hm
    exact hm
  have hge := span2 _ (iso_orthS hg hfix he)
  have hgf := span2 _ (iso_orthS hg hfix hf)
  set α := bf B f ((g : Matrix n n K) *ᵥ e)
  set β := bf B e ((g : Matrix n n K) *ᵥ e)
  set γ := bf B f ((g : Matrix n n K) *ᵥ f)
  set δ := bf B e ((g : Matrix n n K) *ᵥ f)
  have q1 : 2 * (α * β) = 0 := by
    have h := bf_iso hg e e
    rw [hge, hee] at h
    simp only [bf_add_left, bf_add_right, bf_smul_left, bf_smul_right, hee, hff, hef, hfe] at h
    linear_combination h
  have q2 : 2 * (γ * δ) = 0 := by
    have h := bf_iso hg f f
    rw [hgf, hff] at h
    simp only [bf_add_left, bf_add_right, bf_smul_left, bf_smul_right, hee, hff, hef, hfe] at h
    linear_combination h
  have q3 : α * δ + β * γ = 1 := by
    have h := bf_iso hg e f
    rw [hge, hgf, hef] at h
    simp only [bf_add_left, bf_add_right, bf_smul_left, bf_smul_right, hee, hff, hef, hfe] at h
    linear_combination h
  by_cases hβ : β = 0
  · have hαδ : α * δ = 1 := by rw [hβ, zero_mul, add_zero] at q3; exact q3
    have hδ : δ ≠ 0 := right_ne_zero_of_mul_eq_one hαδ
    have hγ : γ = 0 := (mul_eq_zero.1 ((mul_eq_zero.1 q2).resolve_left two_ne_zero)).resolve_right hδ
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self α
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hs
      rw [hs, zero_mul] at hαδ
      exact zero_ne_one hαδ
    obtain ⟨hDz, hz0⟩ := orth_pair_ne_bot hB hn hee hff hef
    obtain ⟨z0, hz0m, hz0z⟩ := exists_aniso hB hnd hDz hz0
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self (-2 / bf B z0 z0)
    have hez : bf B e (r • z0) = 0 := by
      rw [bf_smul_right, hz0m e (Set.mem_insert _ _), mul_zero]
    have hfz : bf B f (r • z0) = 0 := by
      rw [bf_smul_right, hz0m f (Set.mem_insert_of_mem _ (Set.mem_insert _ _)), mul_zero]
    have hzz : bf B (r • z0) (r • z0) = -2 := by
      rw [bf_smul_left, bf_smul_right, ← mul_assoc, ← hr, div_mul_cancel₀ _ hz0z]
    have hss : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
    have hgt : g = tor hB hee hff hez hfz s s⁻¹ := by
      refine Units.ext (eq_of_agree hD' h0 fun x hx => ?_)
      rcases hx with rfl | rfl | hx
      · rw [tor_e hB hee hff hez hfz hef hzz hss, hge, hβ, zero_smul, add_zero, sq, ← hs]
      · rw [tor_f hB hee hff hez hfz hef hzz hss, hgf, hγ, zero_smul, zero_add, inv_pow, sq, ← hs,
          ← eq_inv_of_mul_eq_one_right hαδ]
      · rw [hfix x hx, tor_fix hB hee hff hez hfz hef hzz hss
          (by rw [bf_swap_sym hB x e]; exact he x hx) (by rw [bf_swap_sym hB x f]; exact hf x hx)]
    rw [hgt]
    exact (tor_good hB hH hso hee hff hez hfz s s⁻¹).1.1
  · have hα : α = 0 :=
      (mul_eq_zero.1 ((mul_eq_zero.1 q1).resolve_left two_ne_zero)).resolve_right hβ
    have hβγ : β * γ = 1 := by rw [hα, zero_mul, zero_add] at q3; exact q3
    have hγ0 : γ ≠ 0 := right_ne_zero_of_mul_eq_one hβγ
    have hδ : δ = 0 := (mul_eq_zero.1 ((mul_eq_zero.1 q2).resolve_left two_ne_zero)).resolve_left hγ0
    exfalso
    refine not_refl hD' h0 hdet (x := e - β • f) (c := β⁻¹) ?_ fun x hx => ?_
    · simp only [bf_sub_left, bf_sub_right, bf_smul_left, bf_smul_right, hee, hff, hef, hfe]
      field_simp
      ring
    · rw [reflM_mulVec]
      rcases hx with rfl | rfl | hx
      · have hc : β⁻¹ * bf B (x - β • f) x = -1 := by
          rw [bf_sub_left, bf_smul_left, hee, hfe, zero_sub, mul_one, mul_neg, inv_mul_cancel₀ hβ]
        rw [hc, hge, hα, zero_smul, zero_add]
        module
      · have hc : β⁻¹ * bf B (e - β • x) x = β⁻¹ := by
          rw [bf_sub_left, bf_smul_left, hef, hff, mul_zero, sub_zero, mul_one]
        rw [hc, hgf, hδ, zero_smul, add_zero, eq_inv_of_mul_eq_one_right hβγ, smul_sub, smul_smul,
          inv_mul_cancel₀ hβ, one_smul]
        abel
      · rw [hfix x hx, bf_sub_left, bf_smul_left, bf_swap_sym hB x e, he x hx, bf_swap_sym hB x f,
          hf x hx]
        simp

include hB in
/-- `(A4)` for `SO(B)` (`K` algebraically closed, char 0, `B` symmetric nondegenerate, `3 ≤ n`):
a Zariski closed `H` with `so(B) ⊆ Lie H` contains every `g ∈ O(B)` with `det g = 1`. -/
theorem so_mem_of_so_le_lieS (hnd : B.Nondegenerate) (hn : 3 ≤ Fintype.card n)
    {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K)))
    (hso : ∀ X : Matrix n n K, Xᵀ * B + B * X = 0 →
      X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    {g : Matrix.GeneralLinearGroup n K} (hg : g ∈ isoSub B) (hdet : (g : Matrix n n K).det = 1) :
    g ∈ H := by
  refine fix_induct (B := B) (M := isoSub B ⊓ detOne) (fun S hD g hg hfix => ?_) g
    (Subgroup.mem_inf.2 ⟨hg, hdet⟩)
  have hgi : g ∈ isoSub B := (Subgroup.mem_inf.1 hg).1
  have hgd : (g : Matrix n n K).det = 1 := (Subgroup.mem_inf.1 hg).2
  by_cases h0 : orthS B S = ⊥
  · left
    rw [eq_one_of_fix hD h0 hfix]
    exact H.one_mem
  by_cases hani : ∀ e ∈ orthS B S, bf B e e = 0 → e = 0
  · left
    rw [aniso_base hB hD h0 hani hgi hgd hfix]
    exact H.one_mem
  push_neg at hani
  obtain ⟨e, he, hee, he0⟩ := hani
  obtain ⟨f, hf, hff, hef⟩ := exists_partner hB hnd hD he he0 hee
  by_cases h0' : orthS B (insert e (insert f S)) = ⊥
  · left
    exact plane_base hB hnd hn hH hso hD he hf hee hff hef h0' hgi hgd hfix
  · right
    obtain ⟨u, hu, k1, k2⟩ := pair_trans_SO hB hH hso hnd hD he hf (iso_orthS hgi hfix he)
      (iso_orthS hgi hfix hf) hee hff hef (by rw [bf_iso hgi, hee]) (by rw [bf_iso hgi, hff])
      (by rw [bf_iso hgi, hef]) h0'
    exact ⟨e, f, he, hf, hee, hff, hef, by rw [bf_swap_sym hB e f, hef]; exact one_ne_zero,
      u, hu.1.1, Subgroup.mem_inf.2 ⟨hu.1.2.1, hu.2⟩, hu.1.2.2, k1, k2⟩

include hB in
/-- `(A4)` for `SO(B)`, equality form: a closed `H ≤ SO(B)` with `so(B) ⊆ Lie H` is `SO(B)`. -/
theorem eq_soSub_of_so_le_lieS (hnd : B.Nondegenerate) (hn : 3 ≤ Fintype.card n)
    {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K))) (hle : H ≤ isoSub B ⊓ detOne)
    (hso : ∀ X : Matrix n n K, Xᵀ * B + B * X = 0 →
      X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K))) :
    H = isoSub B ⊓ detOne :=
  le_antisymm hle fun _ hg =>
    so_mem_of_so_le_lieS hB hnd hn hH hso (Subgroup.mem_inf.1 hg).1 (Subgroup.mem_inf.1 hg).2

end Gen

end RamanujanPetersson.AlgGrpB

end


