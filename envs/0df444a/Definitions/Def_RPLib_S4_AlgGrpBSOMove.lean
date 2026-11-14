-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBSOMove
-- name    : RPLib_S4_AlgGrpBSOMove
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:56:01.356631+00:00
-- url     : https://prove2.me/theorems/8cd19d5e-3e69-4e24-aa91-80ab8293d7a3
-- title:
--   Larsen's alternative library: transitivity of Eichler elements on hyperbolic pairs
-- statement:
--   `B` symmetric nondegenerate, `K` algebraically closed of characteristic 0, `H` Zariski closed with
--   `so(B) ⊆ Lie H`. For a hyperbolic pair `(e, f)` of `W = orthS B S` whose orthogonal complement
--   `W' = orthS B {e, f, S}` is nonzero, the elements `u ∈ H` of determinant one that preserve `B` and
--   fix `S` act transitively on hyperbolic pairs of `W` (`pair_trans_SO`). The move `e ↦ e'` uses one
--   Eichler element `eich y (e' - e) 1` with `y = f + βe + γz` (`moveY`, `move_gamma`), `γ` a root of
--   a quadratic (`move1`, needs `B(e, e') ≠ 0`), or two moves `e ↦ f ↦ e'` (`move_e`).
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBSO

/-!
# S4-AlgGrpB, file SOMove: transitivity of Eichler elements on hyperbolic pairs (O5b-SO part 2)

`B` symmetric nondegenerate, `K` algebraically closed of characteristic 0, `H` Zariski closed with
`so(B) ⊆ Lie H`. For a hyperbolic pair `(e, f)` of `W = orthS B S` whose orthogonal complement
`W' = orthS B {e, f, S}` is nonzero, the elements `u ∈ H` of determinant one that preserve `B` and
fix `S` act transitively on hyperbolic pairs of `W` (`pair_trans_SO`). The move `e ↦ e'` uses one
Eichler element `eich y (e' - e) 1` with `y = f + βe + γz` (`moveY`, `move_gamma`), `γ` a root of
a quadratic (`move1`, needs `B(e, e') ≠ 0`), or two moves `e ↦ f ↦ e'` (`move_e`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

section Move

attribute [local instance] zarTop

variable [CharZero K] {B : Matrix n n K} (hB : Bᵀ = B)
  {H : Subgroup (Matrix.GeneralLinearGroup n K)}
  (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K)))
  (hso : ∀ X : Matrix n n K, Xᵀ * B + B * X = 0 →
    X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
  {S : Set (n → K)}

include hB hH hso in
/-- An isotropic `y ∈ orthS B S` with `B(y, e) = B(y, e') = 1` moves `e` to `e'` (same norm). -/
theorem moveY {e e' y : n → K} (he : e ∈ orthS B S) (he' : e' ∈ orthS B S)
    (hy : y ∈ orthS B S) (hnorm : bf B e' e' = bf B e e) (hyy : bf B y y = 0)
    (hye : bf B y e = 1) (hye' : bf B y e' = 1) :
    ∃ u, GoodSO H B S u ∧ (u : Matrix n n K) *ᵥ e = e' := by
  have hyw : bf B y (e' - e) = 0 := by rw [bf_sub_right, hye, hye', sub_self]
  exact ⟨_, eich_good hB hH hso hy (Submodule.sub_mem _ he' he) hyy hyw 1,
    eich_move hB hyy hye hnorm hyw⟩

include hB hH hso in
/-- The move `e ↦ e'` through `y = f + βe + γz`, `β = -γ² B(z, z) / 2`. -/
theorem move_gamma {e f e' z : n → K} (he : e ∈ orthS B S) (hf : f ∈ orthS B S)
    (he' : e' ∈ orthS B S) (hz : z ∈ orthS B S) (hee : bf B e e = 0) (hff : bf B f f = 0)
    (hef : bf B e f = 1) (he'e' : bf B e' e' = 0) (hez : bf B e z = 0) (hfz : bf B f z = 0)
    (γ : K) (hγ : bf B f e' - γ ^ 2 * bf B z z * 2⁻¹ * bf B e e' + γ * bf B z e' = 1) :
    ∃ u, GoodSO H B S u ∧ (u : Matrix n n K) *ᵥ e = e' := by
  have hfe : bf B f e = 1 := by rw [bf_swap_sym hB e f, hef]
  have hze : bf B z e = 0 := by rw [bf_swap_sym hB e z, hez]
  have hzf : bf B z f = 0 := by rw [bf_swap_sym hB f z, hfz]
  refine moveY hB hH hso he he' (y := f + (-(γ ^ 2 * bf B z z * 2⁻¹)) • e + γ • z)
    (Submodule.add_mem _ (Submodule.add_mem _ hf (Submodule.smul_mem _ _ he))
      (Submodule.smul_mem _ _ hz)) (by rw [hee, he'e']) ?_ ?_ ?_
  · simp only [bf_add_left, bf_add_right, bf_smul_left, bf_smul_right, hee, hff, hef, hfe, hez,
      hze, hfz, hzf]
    ring
  · simp only [bf_add_left, bf_smul_left, hfe, hee, hze]
    ring
  · simp only [bf_add_left, bf_smul_left]
    linear_combination hγ

include hB hH hso in
/-- The move `e ↦ e'` when `B(e, e') ≠ 0`, given an anisotropic `z ⊥ e, f` in `orthS B S`. -/
theorem move1 [IsAlgClosed K] {e f e' z : n → K} (he : e ∈ orthS B S) (hf : f ∈ orthS B S)
    (he' : e' ∈ orthS B S) (hz : z ∈ orthS B S) (hee : bf B e e = 0) (hff : bf B f f = 0)
    (hef : bf B e f = 1) (he'e' : bf B e' e' = 0) (hez : bf B e z = 0) (hfz : bf B f z = 0)
    (hzz : bf B z z ≠ 0) (hb : bf B e e' ≠ 0) :
    ∃ u, GoodSO H B S u ∧ (u : Matrix n n K) *ᵥ e = e' := by
  have ha : -(bf B z z * 2⁻¹ * bf B e e') ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hzz (inv_ne_zero two_ne_zero)) hb)
  obtain ⟨γ, hγ⟩ := exists_quadratic_eq_zero ha (IsAlgClosed.exists_eq_mul_self
    (discrim (-(bf B z z * 2⁻¹ * bf B e e')) (bf B z e') (bf B f e' - 1)))
  exact move_gamma hB hH hso he hf he' hz hee hff hef he'e' hez hfz γ (by linear_combination hγ)

include hB hH hso in
/-- Moving `e` to any nonzero isotropic `e' ∈ W` when `W' ≠ 0`. -/
theorem move_e [IsAlgClosed K] (hnd : B.Nondegenerate) (hD : DecS B S) {e f e' : n → K}
    (he : e ∈ orthS B S) (hf : f ∈ orthS B S) (he' : e' ∈ orthS B S) (hee : bf B e e = 0)
    (hff : bf B f f = 0) (hef : bf B e f = 1) (he'e' : bf B e' e' = 0) (he'0 : e' ≠ 0)
    (h0 : orthS B (insert e (insert f S)) ≠ ⊥) :
    ∃ u, GoodSO H B S u ∧ (u : Matrix n n K) *ᵥ e = e' := by
  have hfe : bf B f e = 1 := by rw [bf_swap_sym hB e f, hef]
  have hD' := decS_insert hD he hf hee hff hef (by rw [hfe]; exact one_ne_zero)
  have mem3 : ∀ {z : n → K}, z ∈ orthS B (insert e (insert f S)) →
      z ∈ orthS B S ∧ bf B e z = 0 ∧ bf B f z = 0 := fun {z} hz =>
    ⟨orthS_anti (fun y hy => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hy)) hz,
      hz e (Set.mem_insert _ _), hz f (Set.mem_insert_of_mem _ (Set.mem_insert _ _))⟩
  obtain ⟨z, hz, hzz⟩ := exists_aniso hB hnd hD' h0
  obtain ⟨hzS, hez, hfz⟩ := mem3 hz
  by_cases hb : bf B e e' = 0
  · by_cases ha : bf B f e' = 0
    · have hdW : e' ∈ orthS B (insert e (insert f S)) := by
        intro s hs
        rcases hs with rfl | rfl | hs
        · exact hb
        · exact ha
        · exact he' s hs
      obtain ⟨z', hz', hdz⟩ := exists_bf_ne_sym hB hnd hD' hdW he'0
      obtain ⟨hz'S, hez', hfz'⟩ := mem3 hz'
      have hze' : bf B z' e' ≠ 0 := by rw [bf_swap_sym hB e' z']; exact hdz
      refine move_gamma hB hH hso he hf he' hz'S hee hff hef he'e' hez' hfz' (bf B z' e')⁻¹ ?_
      rw [ha, hb, mul_zero, sub_zero, zero_add, inv_mul_cancel₀ hze']
    · obtain ⟨u1, hu1, k1⟩ := move1 hB hH hso he hf hf hzS hee hff hef hff hez hfz hzz
        (by rw [hef]; exact one_ne_zero)
      obtain ⟨u2, hu2, k2⟩ := move1 hB hH hso hf he he' hzS hff hee hfe he'e' hfz hez hzz ha
      exact ⟨u2 * u1, hu2.mul hu1, by rw [mulVec_mul_GL, k1, k2]⟩
  · exact move1 hB hH hso he hf he' hzS hee hff hef he'e' hez hfz hzz hb

include hB hH hso in
/-- Transitivity on hyperbolic pairs of `W = orthS B S` when `W' = orthS B {e, f, S} ≠ 0`. -/
theorem pair_trans_SO [IsAlgClosed K] (hnd : B.Nondegenerate) (hD : DecS B S)
    {e f e' f' : n → K} (he : e ∈ orthS B S) (hf : f ∈ orthS B S) (he' : e' ∈ orthS B S)
    (hf' : f' ∈ orthS B S) (hee : bf B e e = 0) (hff : bf B f f = 0) (hef : bf B e f = 1)
    (he'e' : bf B e' e' = 0) (hf'f' : bf B f' f' = 0) (hef' : bf B e' f' = 1)
    (h0 : orthS B (insert e (insert f S)) ≠ ⊥) :
    ∃ u, GoodSO H B S u ∧ (u : Matrix n n K) *ᵥ e = e' ∧ (u : Matrix n n K) *ᵥ f = f' := by
  have he'0 : e' ≠ 0 := by rintro rfl; rw [bf_zero_left] at hef'; exact zero_ne_one hef'
  obtain ⟨u1, hu1, k1⟩ := move_e hB hH hso hnd hD he hf he' hee hff hef he'e' he'0 h0
  have hf₁ : (u1 : Matrix n n K) *ᵥ f ∈ orthS B S := iso_orthS hu1.1.2.1 hu1.1.2.2 hf
  have h1 : bf B e' ((u1 : Matrix n n K) *ᵥ f) = 1 := by rw [← k1, bf_iso hu1.1.2.1, hef]
  have h2 : bf B ((u1 : Matrix n n K) *ᵥ f) ((u1 : Matrix n n K) *ᵥ f) = 0 := by
    rw [bf_iso hu1.1.2.1, hff]
  have hyw : bf B e' (f' - (u1 : Matrix n n K) *ᵥ f) = 0 := by
    rw [bf_sub_right, h1, hef', sub_self]
  refine ⟨eich hB he'e' hyw 1 * u1,
    (eich_good hB hH hso he' (Submodule.sub_mem _ hf' hf₁) he'e' hyw 1).mul hu1, ?_, ?_⟩
  · rw [mulVec_mul_GL, k1]
    exact eich_fix hB he'e' hyw 1 he'e'
      (by rw [bf_swap_sym hB e' (f' - (u1 : Matrix n n K) *ᵥ f), hyw])
  · rw [mulVec_mul_GL]
    exact eich_move hB he'e' h1 (by rw [hf'f', h2]) hyw

end Move

end RamanujanPetersson.AlgGrpB

end


