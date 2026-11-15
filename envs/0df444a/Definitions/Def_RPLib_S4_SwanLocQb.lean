-- Prove2me | Definitions.Def_RPLib_S4_SwanLocQb
-- name    : RPLib_S4_SwanLocQb
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:22:32.244818+00:00
-- url     : https://prove2.me/theorems/ddda7404-1ee6-4671-91fe-4ea043683cb2
-- title:
--   The quotient formula $v(\sigma\varpi_H - \varpi_H) = \sum_{h \in H} v(\sigma h\varpi - \varpi)$
-- statement:
--   For local data with group $G$, a normal subgroup $H$ and a uniformiser $\varpi_H$ of the $H$-fixed field, the file proves the quotient formula $$v(\sigma\varpi_H - \varpi_H) = \sum_{h \in H} v(\sigma h \varpi - \varpi) \qquad (\sigma \notin H),$$ by comparing the values at $\sigma\varpi$ of the polynomial $\prod_{h}(X - h\varpi)$ and of its image under $\sigma$, and that these valuations are finite.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter IV, Section 1, Proposition 3

import Mathlib
import Definitions.Def_RPLib_S4_SwanLocQa

/-!
# S4-Swan (K2), part 9: the quotient formula `v(σ ϖH - ϖH) = ∑_{h ∈ H} v(σ h ϖ - ϖ)`

Serre, Local Fields IV §1 Prop 3, for `σ ∉ H` (`LocData.v_quot`), from the tools of part 7.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

open Polynomial

namespace LocData

variable {G L : Type*} [Group G] [Field L] [MulSemiringAction G L] (D : LocData G L)
  (H : Subgroup G) [Fintype H]

theorem v_eval_map_fpol (σ : G) :
    D.v (((D.fpol H).map (MulSemiringAction.toRingHom G L σ)).eval D.ϖ) =
      ∑ h : H, D.v ((σ * h) • D.ϖ - D.ϖ) := by
  rw [D.map_fpol H σ, eval_prod, D.v_prod]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [eval_sub, eval_X, eval_C, AddValuation.map_sub_swap]

theorem eval_map_fpol_ne_zero {σ : G} (hσ : σ ∉ H) :
    ((D.fpol H).map (MulSemiringAction.toRingHom G L σ)).eval D.ϖ ≠ 0 := by
  rw [D.map_fpol H σ, eval_prod, Finset.prod_ne_zero_iff]
  intro h _
  rw [eval_sub, eval_X, eval_C, sub_ne_zero]
  intro h'
  have h1 := D.eq_one_of_fix_ϖ h'.symm
  rw [mul_eq_one_iff_eq_inv] at h1
  exact hσ (h1 ▸ H.inv_mem h.2)

variable {D H}

/-- Serre IV §1 Prop 3 in valuation form: `v(σ ϖH - ϖH) = v(f^σ(ϖ))`. -/
theorem QData.v_quot' [H.Normal] {ϖH : L} (hq : D.QData H ϖH) {σ : G} (hσ : σ ∉ H) :
    D.v (σ • ϖH - ϖH) = D.v (((D.fpol H).map (MulSemiringAction.toRingHom G L σ)).eval D.ϖ) := by
  have he : 1 ≤ Fintype.card H := Fintype.card_pos
  have hf := D.fpol_monic H
  have hfT := D.fpol_coeffIn H
  have hϖH0 : 0 ≤ D.v ϖH := by rw [hq.v_eq]; exact_mod_cast Nat.zero_le _
  refine le_antisymm ?_ ?_
  · have h0 : ((D.fpol H).map (MulSemiringAction.toRingHom G L σ)).eval D.ϖ =
        ((D.fpol H).map (MulSemiringAction.toRingHom G L σ) - D.fpol H).eval D.ϖ := by
      rw [eval_sub, D.eval_fpol, sub_zero]
    rw [h0]
    refine D.le_v_eval _ fun k => ?_
    rw [D.v_mul_pow, coeff_sub, coeff_map, MulSemiringAction.toRingHom_apply]
    refine le_trans ?_ (le_add_of_nonneg_right (by exact_mod_cast Nat.zero_le k))
    obtain ⟨hfix, hint⟩ := (D.mem_intSub).1 (hfT k)
    exact D.lb H _ he hq.fix hq.v_eq hq.resH σ hfix hint
  · obtain ⟨B, hB⟩ := WithTop.ne_top_iff_exists.1
      (fun h => D.eval_map_fpol_ne_zero H hσ ((D.v.top_iff).1 h))
    obtain ⟨g, hg, hvg⟩ := D.approx (B.toNat + 1) ϖH hϖH0
    have hgT : CoeffIn (D.intSub H) (g - C ϖH) := fun k => by
      rw [coeff_sub, coeff_C]
      refine (D.intSub H).sub_mem ?_ ?_
      · obtain ⟨h1, h2⟩ := (D.mem_intSub).1 (hg k)
        exact (D.mem_intSub).2 ⟨fun h _ => h1 h trivial, h2⟩
      · split_ifs
        · exact (D.mem_intSub).2 ⟨hq.fix, hϖH0⟩
        · exact (D.intSub H).zero_mem
    obtain ⟨hqT, hρT⟩ := coeffIn_div hf hgT hfT
    have hdiv := modByMonic_add_div (g - C ϖH) (D.fpol H)
    have hρdeg : ((g - C ϖH) %ₘ D.fpol H).natDegree < Fintype.card H := by
      rw [← D.natDegree_fpol H]
      refine natDegree_modByMonic_lt _ hf fun h1 => ?_
      have := D.natDegree_fpol H
      rw [h1, natDegree_one] at this
      omega
    have hρv : ((B.toNat + 1 : ℕ) : WithTop ℤ) ≤ D.v (((g - C ϖH) %ₘ D.fpol H).eval D.ϖ) := by
      have h2 := congrArg (eval D.ϖ) hdiv
      rw [eval_add, eval_mul, D.eval_fpol, zero_mul, add_zero, eval_sub, eval_C] at h2
      rw [h2, AddValuation.map_sub_swap]; exact hvg
    have hterm : ∀ k, ((B.toNat + 1 : ℕ) : WithTop ℤ) ≤
        D.v (((g - C ϖH) %ₘ D.fpol H).coeff k * D.ϖ ^ k) := by
      intro k
      by_cases hk : k < Fintype.card H
      · refine hρv.trans ?_
        rw [eval_eq_sum_range' hρdeg]
        refine D.v_sum_le_of_distinct _ _ (fun i hi j hj hij hi0 => ?_) k (Finset.mem_range.2 hk)
        exact hq.v_term_ne ((D.mem_intSub).1 (hρT i)).1 ((D.mem_intSub).1 (hρT j)).1
          (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij hi0
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, AddValuation.map_zero]
        exact le_top
    have hgσ : g.map (MulSemiringAction.toRingHom G L σ) = g := by
      ext k
      rw [coeff_map, MulSemiringAction.toRingHom_apply]
      exact ((D.mem_intSub).1 (hg k)).1 σ trivial
    have hdivσ := congrArg (fun p => (p.map (MulSemiringAction.toRingHom G L σ)).eval D.ϖ) hdiv
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, hgσ, map_C, eval_add,
      eval_mul, eval_sub, eval_C, MulSemiringAction.toRingHom_apply] at hdivσ
    have hlt : D.v (((D.fpol H).map (MulSemiringAction.toRingHom G L σ)).eval D.ϖ) ≤
        ((B.toNat + 1 : ℕ) : WithTop ℤ) := by
      rw [← hB, ← WithTop.coe_natCast, WithTop.coe_le_coe]
      have := Int.self_le_toNat B
      push_cast; omega
    rw [AddValuation.map_sub_swap,
      show ϖH - σ • ϖH = (ϖH - g.eval D.ϖ) + ((g.eval D.ϖ) - σ • ϖH) by ring, ← hdivσ]
    refine D.v.map_le_add (hlt.trans hvg) (D.v.map_le_add ?_ ?_)
    · refine hlt.trans (D.le_v_eval _ fun k => ?_)
      rw [coeff_map, MulSemiringAction.toRingHom_apply, D.v_mul_pow, D.v_smul, ← D.v_mul_pow]
      exact hterm k
    · rw [AddValuation.map_mul]
      refine le_add_of_nonneg_right (D.le_v_eval _ fun k => ?_)
      rw [coeff_map, MulSemiringAction.toRingHom_apply, D.v_mul_pow, D.v_smul]
      exact add_nonneg ((D.mem_intSub).1 (hqT k)).2 (by exact_mod_cast Nat.zero_le k)

/-- **Quotient formula** (Serre IV §1 Prop 3): `v(σ ϖH - ϖH) = ∑_{h ∈ H} v(σ h ϖ - ϖ)` for `σ ∉ H`. -/
theorem QData.v_quot [H.Normal] {ϖH : L} (hq : D.QData H ϖH) {σ : G} (hσ : σ ∉ H) :
    D.v (σ • ϖH - ϖH) = ∑ h : H, D.v ((σ * h) • D.ϖ - D.ϖ) := by
  rw [hq.v_quot' hσ, D.v_eval_map_fpol H σ]

theorem QData.v_ne_top [H.Normal] {ϖH : L} (hq : D.QData H ϖH) {σ : G} (hσ : σ ∉ H) :
    D.v (σ • ϖH - ϖH) ≠ ⊤ := by
  rw [hq.v_quot' hσ]
  exact fun h => D.eval_map_fpol_ne_zero H hσ ((D.v.top_iff).1 h)

end LocData

end

end Swan
end RamanujanPetersson


