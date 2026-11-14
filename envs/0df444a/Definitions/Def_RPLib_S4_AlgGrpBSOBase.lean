-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBSOBase
-- name    : RPLib_S4_AlgGrpBSOBase
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:55:49.644554+00:00
-- url     : https://prove2.me/theorems/4432186c-8090-4591-ad09-6b64940075fe
-- title:
--   Larsen's alternative library: base cases of the `SO(B)` induction
-- statement:
--   `detOne` is the determinant-one subgroup of `GL_n(K)`. `not_refl`: a determinant-one matrix cannot
--   agree with a reflection on a decomposing set `S` with `orthS B S = 0` (char 0). `aniso_base`
--   (`K` algebraically closed, char 0, `B` symmetric): if `W = orthS B S ≠ 0` has no nonzero isotropic
--   vector, then `W` is a line and every determinant-one isometry fixing `S` is `1`.
--   `exists_partner`: a nonzero isotropic `e ∈ W` has an isotropic partner `f ∈ W` with `B(e, f) = 1`.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBSO

/-!
# S4-AlgGrpB, file SOBase: base cases of the `SO(B)` induction (O5b-SO part 4)

`detOne` is the determinant-one subgroup of `GL_n(K)`. `not_refl`: a determinant-one matrix cannot
agree with a reflection on a decomposing set `S` with `orthS B S = 0` (char 0). `aniso_base`
(`K` algebraically closed, char 0, `B` symmetric): if `W = orthS B S ≠ 0` has no nonzero isotropic
vector, then `W` is a line and every determinant-one isometry fixing `S` is `1`.
`exists_partner`: a nonzero isotropic `e ∈ W` has an isotropic partner `f ∈ W` with `B(e, f) = 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- The determinant-one subgroup of `GL_n(K)`. -/
def detOne : Subgroup (Matrix.GeneralLinearGroup n K) where
  carrier := {g | (g : Matrix n n K).det = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Units.val_mul, Matrix.det_mul, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h := congrArg Matrix.det (show ((a⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) *
      (a : Matrix n n K) = 1 by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    rwa [Matrix.det_mul, ha, mul_one, Matrix.det_one] at h

theorem mem_detOne {g : Matrix.GeneralLinearGroup n K} :
    g ∈ detOne ↔ (g : Matrix n n K).det = 1 := Iff.rfl

section Base

variable [CharZero K] {B : Matrix n n K}

/-- A determinant-one `g` cannot agree with a reflection (`c B(x, x) = -2`) on `S`. -/
theorem not_refl {S : Set (n → K)} (hD : DecS B S) (h0 : orthS B S = ⊥)
    {g : Matrix.GeneralLinearGroup n K} (hdet : (g : Matrix n n K).det = 1) {x : n → K} {c : K}
    (hc : c * bf B x x = -2) (h : ∀ s ∈ S, (g : Matrix n n K) *ᵥ s = reflM B x c *ᵥ s) : False := by
  have hd := det_reflM (B := B) x c
  rw [← eq_of_agree hD h0 h, hdet, hc] at hd
  norm_num at hd

variable (hB : Bᵀ = B)

include hB in
theorem aniso_base [IsAlgClosed K] {S : Set (n → K)} (hD : DecS B S) (h0 : orthS B S ≠ ⊥)
    (hani : ∀ e ∈ orthS B S, bf B e e = 0 → e = 0) {g : Matrix.GeneralLinearGroup n K}
    (hg : g ∈ isoSub B) (hdet : (g : Matrix n n K).det = 1)
    (hfix : ∀ s ∈ S, (g : Matrix n n K) *ᵥ s = s) : g = 1 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hq : bf B x x ≠ 0 := fun h => hx0 (hani x hx h)
  have key : ∀ w ∈ orthS B S, w = (bf B x w / bf B x x) • x := by
    intro w hw
    by_contra hne
    set w' := w - (bf B x w / bf B x x) • x with hw'
    have hw'W : w' ∈ orthS B S := Submodule.sub_mem _ hw (Submodule.smul_mem _ _ hx)
    have hxw' : bf B x w' = 0 := by
      rw [hw', bf_sub_right, bf_smul_right, div_mul_cancel₀ _ hq, sub_self]
    have hw'x : bf B w' x = 0 := by rw [bf_swap_sym hB x w', hxw']
    have hw'0 : w' ≠ 0 := fun h => hne (sub_eq_zero.1 h)
    have hq' : bf B w' w' ≠ 0 := fun h => hw'0 (hani w' hw'W h)
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self (-(bf B x x) / bf B w' w')
    have hr' : r * r * bf B w' w' = -bf B x x := by rw [← hr, div_mul_cancel₀ _ hq']
    have hv := hani (x + r • w') (Submodule.add_mem _ hx (Submodule.smul_mem _ _ hw'W)) (by
      simp only [bf_add_left, bf_add_right, bf_smul_left, bf_smul_right, hxw', hw'x]
      linear_combination hr')
    have h1 : bf B x (x + r • w') = bf B x x := by
      rw [bf_add_right, bf_smul_right, hxw', mul_zero, add_zero]
    rw [hv, bf_zero_right] at h1
    exact hq h1.symm
  have hgx := key _ (iso_orthS hg hfix hx)
  set κ := bf B x ((g : Matrix n n K) *ᵥ x) / bf B x x with hκdef
  have hκ : κ * κ = 1 := by
    have h1 := bf_iso hg x x
    rw [hgx, bf_smul_left, bf_smul_right, ← mul_assoc] at h1
    exact mul_right_cancel₀ hq (by rw [h1, one_mul])
  have hD' : DecS B (insert x S) := by
    intro v
    obtain ⟨s, hs, hvs⟩ := hD v
    refine ⟨s + (bf B x (v - s) / bf B x x) • x,
      Submodule.add_mem _ (Submodule.span_mono (Set.subset_insert _ _) hs)
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))), ?_⟩
    have h := key _ hvs
    rw [show v - (s + (bf B x (v - s) / bf B x x) • x) =
      v - s - (bf B x (v - s) / bf B x x) • x by abel, ← h, sub_self]
    exact Submodule.zero_mem _
  have h0' : orthS B (insert x S) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
    have hwW : w ∈ orthS B S := orthS_anti (Set.subset_insert _ _) hw
    rw [key w hwW, hw x (Set.mem_insert _ _), zero_div, zero_smul]
  have hsx : ∀ s ∈ S, bf B x s = 0 := fun s hs => by rw [bf_swap_sym hB s x]; exact hx s hs
  rcases mul_self_eq_one_iff.1 hκ with h1 | h1
  · refine eq_one_of_fix hD' h0' fun s hs => ?_
    rcases hs with rfl | hs
    · rw [hgx, h1, one_smul]
    · exact hfix s hs
  · exfalso
    refine not_refl hD' h0' hdet (x := x) (c := -2 / bf B x x) (by rw [div_mul_cancel₀ _ hq])
      fun s hs => ?_
    rw [reflM_mulVec]
    rcases hs with rfl | hs
    · rw [hgx, h1, div_mul_cancel₀ _ hq]
      module
    · rw [hfix s hs, hsx s hs, mul_zero, zero_smul, add_zero]

include hB in
theorem exists_partner (hnd : B.Nondegenerate) {S : Set (n → K)} (hD : DecS B S) {e : n → K}
    (he : e ∈ orthS B S) (he0 : e ≠ 0) (hee : bf B e e = 0) :
    ∃ f ∈ orthS B S, bf B f f = 0 ∧ bf B e f = 1 := by
  obtain ⟨z, hz, hez⟩ := exists_bf_ne_sym hB hnd hD he he0
  set z1 := (bf B e z)⁻¹ • z with hz1
  have h1 : bf B e z1 = 1 := by rw [hz1, bf_smul_right, inv_mul_cancel₀ hez]
  have h1' : bf B z1 e = 1 := by rw [bf_swap_sym hB e z1, h1]
  refine ⟨z1 - (2⁻¹ * bf B z1 z1) • e,
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hz) (Submodule.smul_mem _ _ he), ?_, ?_⟩
  · have h2 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ two_ne_zero
    simp only [bf_sub_left, bf_sub_right, bf_smul_left, bf_smul_right, hee, h1, h1']
    linear_combination (-bf B z1 z1) * h2
  · rw [bf_sub_right, h1, bf_smul_right, hee, mul_zero, sub_zero]

end Base

end RamanujanPetersson.AlgGrpB

end


