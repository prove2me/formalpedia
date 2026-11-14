-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBSpGen
-- name    : RPLib_S4_AlgGrpBSpGen
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:49:04.470462+00:00
-- url     : https://prove2.me/theorems/f4a310a9-0480-41bc-ac36-145b639cc3a4
-- title:
--   Larsen's alternative library: `Lie H ⊇ sp(B)` forces `H ⊇ Sp(B)` for `Sp`, O5b)
-- statement:
--   `fix_induct` (any form `B`, any subgroup `M`): if for every `S` with `DecS B S` and every `g ∈ M`
--   fixing `S` either `g ∈ H` or there are a hyperbolic pair `(e, f)` in `orthS B S` and `u ∈ H ∩ M`
--   fixing `S` with `u e = g e`, `u f = g f`, then `M ⊆ H` (strong induction on `dim orthS B S`,
--   adding `e, f` to `S`; `decS_insert`). It is reused for `SO(B)`.
--   For `B` alternating and nondegenerate (char 0) the step is `pair_trans`, giving
--   `iso_mem_of_sp_le_lieS`: a closed `H` with `sp(B) ⊆ Lie H` contains `Sp(B) = isoSub B`.
--   `isClosed_isoSet`: `isoSet B` is Zariski closed.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBSp

/-!
# S4-AlgGrpB, file SpGen: `Lie H ⊇ sp(B)` forces `H ⊇ Sp(B)` (spike API (A4) for `Sp`, O5b)

`fix_induct` (any form `B`, any subgroup `M`): if for every `S` with `DecS B S` and every `g ∈ M`
fixing `S` either `g ∈ H` or there are a hyperbolic pair `(e, f)` in `orthS B S` and `u ∈ H ∩ M`
fixing `S` with `u e = g e`, `u f = g f`, then `M ⊆ H` (strong induction on `dim orthS B S`,
adding `e, f` to `S`; `decS_insert`). It is reused for `SO(B)`.
For `B` alternating and nondegenerate (char 0) the step is `pair_trans`, giving
`iso_mem_of_sp_le_lieS`: a closed `H` with `sp(B) ⊆ Lie H` contains `Sp(B) = isoSub B`.
`isClosed_isoSet`: `isoSet B` is Zariski closed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial
open scoped Matrix

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

theorem isoSet_eq_zeroS (B : Matrix n n K) :
    isoSet B = zeroS (Set.range fun ij : n × n => isoPoly B ij.1 ij.2) := by
  ext g
  rw [mem_zeroS, Set.forall_mem_range, mem_isoSet]
  constructor
  · intro h ij
    rw [eval_isoPoly, h, sub_self, Matrix.zero_apply]
  · intro h
    ext i j
    have := h (i, j)
    rwa [eval_isoPoly, Matrix.sub_apply, sub_eq_zero] at this

section Closed

attribute [local instance] zarTop

theorem isClosed_isoSet (B : Matrix n n K) : IsClosed (isoSet B) := by
  rw [isoSet_eq_zeroS]
  exact isClosed_zeroS _

end Closed

/-- Adding a hyperbolic pair `(e, f)` of `orthS B S` to `S` keeps the decomposition property. -/
theorem decS_insert {B : Matrix n n K} {S : Set (n → K)} (hD : DecS B S) {e f : n → K}
    (he : e ∈ orthS B S) (hf : f ∈ orthS B S) (hee : bf B e e = 0) (hff : bf B f f = 0)
    (hef : bf B e f = 1) (hfe : bf B f e ≠ 0) : DecS B (insert e (insert f S)) := by
  intro x
  obtain ⟨s, hs, hw⟩ := hD x
  set w := x - s
  set a := (bf B f e)⁻¹ * bf B f w
  set b := bf B e w
  have hsub : S ⊆ insert e (insert f S) :=
    fun y hy => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hy)
  refine ⟨s + a • e + b • f, ?_, ?_⟩
  · refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.span_mono hsub hs) ?_) ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · have hx : x - (s + a • e + b • f) = w - a • e - b • f := by simp only [w]; abel
    rw [hx]
    intro t ht
    rcases ht with rfl | rfl | ht
    · rw [bf_sub_right, bf_sub_right, bf_smul_right, bf_smul_right, hee, hef]
      simp only [b]; ring
    · rw [bf_sub_right, bf_sub_right, bf_smul_right, bf_smul_right, hff]
      simp only [a]; field_simp; ring
    · rw [bf_sub_right, bf_sub_right, bf_smul_right, bf_smul_right, hw t ht, he t ht, hf t ht]
      ring

/-- The fix-`S` induction: reduces `M ⊆ H` to transitivity on hyperbolic pairs. -/
theorem fix_induct {B : Matrix n n K} {H M : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hstep : ∀ S : Set (n → K), DecS B S → ∀ g ∈ M,
      (∀ s ∈ S, (g : Matrix n n K) *ᵥ s = s) →
      g ∈ H ∨ ∃ e f : n → K, e ∈ orthS B S ∧ f ∈ orthS B S ∧ bf B e e = 0 ∧ bf B f f = 0 ∧
        bf B e f = 1 ∧ bf B f e ≠ 0 ∧ ∃ u ∈ H, u ∈ M ∧
          (∀ s ∈ S, (u : Matrix n n K) *ᵥ s = s) ∧
          (u : Matrix n n K) *ᵥ e = (g : Matrix n n K) *ᵥ e ∧
          (u : Matrix n n K) *ᵥ f = (g : Matrix n n K) *ᵥ f) :
    ∀ g ∈ M, g ∈ H := by
  suffices h : ∀ (k : ℕ) (S : Set (n → K)), Module.finrank K (orthS B S) = k → DecS B S →
      ∀ g ∈ M, (∀ s ∈ S, (g : Matrix n n K) *ᵥ s = s) → g ∈ H from
    fun g hg => h _ ∅ rfl (decS_empty B) g hg (fun s hs => absurd hs (Set.notMem_empty s))
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S hk hD g hg hfix
  rcases hstep S hD g hg hfix with h | ⟨e, f, he, hf, hee, hff, hef, hfe, u, huH, huM, hufix, hue, huf⟩
  · exact h
  · have hD' := decS_insert hD he hf hee hff hef hfe
    have hlt : orthS B (insert e (insert f S)) < orthS B S := by
      refine SetLike.lt_iff_le_and_exists.2
        ⟨orthS_anti fun y hy => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hy), e, he,
          fun h => hfe (h f (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))⟩
    have hk' : Module.finrank K (orthS B (insert e (insert f S))) < k :=
      hk ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hfix' : ∀ s ∈ insert e (insert f S),
        ((u⁻¹ * g : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ s = s := by
      intro s hs
      rw [mulVec_mul_GL]
      rcases hs with rfl | rfl | hs
      · rw [← hue, inv_mulVec_GL]
      · rw [← huf, inv_mulVec_GL]
      · rw [hfix s hs]
        calc ((u⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ s
            = ((u⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ ((u : Matrix n n K) *ᵥ s) := by
              rw [hufix s hs]
          _ = s := inv_mulVec_GL u s
    have h1 := ih _ hk' _ rfl hD' (u⁻¹ * g) (M.mul_mem (M.inv_mem huM) hg) hfix'
    have hg' : g = u * (u⁻¹ * g) := by rw [mul_inv_cancel_left]
    rw [hg']
    exact H.mul_mem huH h1

section SpA4

attribute [local instance] zarTop

variable [CharZero K]

/-- `(A4)` for `Sp(B)` (char 0): `B` alternating nondegenerate, `H` Zariski closed with
`sp(B) = {X | Xᵀ B + B X = 0} ⊆ Lie H` ⇒ `Sp(B) ⊆ H`. -/
theorem iso_mem_of_sp_le_lieS {B : Matrix n n K} (hB : Bᵀ = -B) (hnd : B.Nondegenerate)
    {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K)))
    (hsp : ∀ X : Matrix n n K, Xᵀ * B + B * X = 0 → X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    {g : Matrix.GeneralLinearGroup n K} (hg : g ∈ isoSub B) : g ∈ H := by
  refine fix_induct (B := B) (M := isoSub B) (fun S hD g hg hfix => ?_) g hg
  by_cases h0 : orthS B S = ⊥
  · left
    rw [eq_one_of_fix hD h0 hfix]
    exact H.one_mem
  · right
    obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    obtain ⟨z, hz, hez⟩ := exists_bf_ne hB hnd hD he he0
    have hf : (bf B e z)⁻¹ • z ∈ orthS B S := Submodule.smul_mem _ _ hz
    have hef : bf B e ((bf B e z)⁻¹ • z) = 1 := by rw [bf_smul_right, inv_mul_cancel₀ hez]
    obtain ⟨u, hu, k1, k2⟩ := pair_trans hB hH hsp hnd hD he hf (iso_orthS hg hfix he)
      (iso_orthS hg hfix hf) hef (by rw [bf_iso hg, hef])
    exact ⟨e, _, he, hf, bf_self_alt hB e, bf_self_alt hB _, hef,
      by rw [bf_swap_alt hB e, hef]; exact neg_ne_zero.2 one_ne_zero,
      u, hu.1, hu.2.1, hu.2.2, k1, k2⟩

/-- `(A4)` for `Sp(B)`, equality form: a closed `H ≤ Sp(B)` with `sp(B) ⊆ Lie H` is `Sp(B)`. -/
theorem eq_isoSub_of_sp_le_lieS {B : Matrix n n K} (hB : Bᵀ = -B) (hnd : B.Nondegenerate)
    {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K))) (hle : H ≤ isoSub B)
    (hsp : ∀ X : Matrix n n K, Xᵀ * B + B * X = 0 → X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K))) :
    H = isoSub B :=
  le_antisymm hle fun _ hg => iso_mem_of_sp_le_lieS hB hnd hH hsp hg

end SpA4

end RamanujanPetersson.AlgGrpB

end


