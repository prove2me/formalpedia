-- Prove2me | Definitions.Def_RPLib_S4_SwanLocQa
-- name    : RPLib_S4_SwanLocQa
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:19:22.913358+00:00
-- url     : https://prove2.me/theorems/e03338db-61e8-4518-bf44-c42b1c16dd3c
-- title:
--   Tools for the quotient formula of ramification functions
-- statement:
--   Toward Serre's quotient formula (Local Fields IV, Proposition 3) for local data with group $G$ and a normal subgroup $H$: the file defines the polynomial $$f(X) = \prod_{h \in H} (X - h\varpi)$$ whose coefficients lie in the integral elements fixed by $H$, proves that it is monic of degree $|H|$ and that its image under $\sigma$ is computed coefficientwise, and proves valuation estimates for products, sums of distinct-valued terms, and evaluations of polynomials with integral coefficients. It sets up the quotient data (a uniformiser $\varpi_H$ of the fixed field) used in the formula.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter IV, Section 1, Proposition 3

import Mathlib
import Definitions.Def_RPLib_S4_SwanLoc

/-!
# S4-Swan (K2), part 7: tools for the quotient formula (Serre, Local Fields IV §1 Prop 3)

For `H` normal in `G` and `ϖH ∈ L^H` with `v ϖH = |H|`, where `v(L^H \ 0) ⊆ |H| ℤ` (`QData`):
`v(σ ϖH - ϖH) = ∑_{h ∈ H} v(σ h ϖ - ϖ)` for `σ ∉ H` (`v_quot`). Serre's proof with `f = ∏_{h ∈ H} (X - h ϖ)`;
monogenicity `B = A[ϖ]` is replaced by successive approximation through `res` (`approx`) plus the fact that
`∑_{k < |H|} c_k ϖ^k` with `c_k ∈ L^H` has the valuation of its smallest term (`v_sum_le_of_distinct`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

open Polynomial

namespace LocData

variable {G L : Type*} [Group G] [Field L] [MulSemiringAction G L] (D : LocData G L)

/-- Integral `H`-fixed elements. -/
def intSub (H : Subgroup G) : Subring L where
  carrier := {x | (∀ h ∈ H, h • x = x) ∧ 0 ≤ D.v x}
  mul_mem' := fun ha hb => ⟨fun h hh => by rw [smul_mul', ha.1 h hh, hb.1 h hh],
    by rw [AddValuation.map_mul]; exact add_nonneg ha.2 hb.2⟩
  one_mem' := ⟨fun h _ => smul_one h, (AddValuation.map_one D.v).symm.le⟩
  add_mem' := fun ha hb => ⟨fun h hh => by rw [smul_add, ha.1 h hh, hb.1 h hh],
    D.v.map_le_add ha.2 hb.2⟩
  zero_mem' := ⟨fun h _ => smul_zero h, by rw [AddValuation.map_zero]; exact le_top⟩
  neg_mem' := fun ha => ⟨fun h hh => by rw [smul_neg, ha.1 h hh],
    by rw [AddValuation.map_neg]; exact ha.2⟩

theorem mem_intSub {H : Subgroup G} {x : L} :
    x ∈ D.intSub H ↔ (∀ h ∈ H, h • x = x) ∧ 0 ≤ D.v x := Iff.rfl

/-- All coefficients of `p` lie in `T`. -/
def CoeffIn (T : Subring L) (p : L[X]) : Prop := ∀ k, p.coeff k ∈ T

omit [MulSemiringAction G L] in
theorem coeffIn_mul {T : Subring L} {p q : L[X]} (hp : CoeffIn T p) (hq : CoeffIn T q) :
    CoeffIn T (p * q) := fun k => by
  rw [coeff_mul]; exact T.sum_mem fun x _ => T.mul_mem (hp _) (hq _)

omit [MulSemiringAction G L] in
theorem coeffIn_prod {ι : Type*} {T : Subring L} (s : Finset ι) (f : ι → L[X])
    (hf : ∀ i ∈ s, CoeffIn T (f i)) : CoeffIn T (∏ i ∈ s, f i) :=
  Finset.prod_induction f (CoeffIn T) (fun _ _ => coeffIn_mul)
    (fun k => by rw [coeff_one]; split_ifs; exacts [T.one_mem, T.zero_mem]) hf

omit [MulSemiringAction G L] in
theorem coeffIn_X_sub_C {T : Subring L} {c : L} (hc : c ∈ T) : CoeffIn T (X - C c) := fun k => by
  rw [coeff_sub, coeff_X, coeff_C]
  refine T.sub_mem ?_ ?_ <;> split_ifs
  exacts [T.one_mem, T.zero_mem, hc, T.zero_mem]

omit [MulSemiringAction G L] in
/-- Division by a monic polynomial stays inside a subring. -/
theorem coeffIn_div {T : Subring L} {p f : L[X]} (hf : f.Monic) (hp : CoeffIn T p)
    (hfT : CoeffIn T f) : CoeffIn T (p /ₘ f) ∧ CoeffIn T (p %ₘ f) := by
  have sub : ∀ q : L[X], CoeffIn T q → (↑q.coeffs : Set L) ⊆ T := fun q hq c hc => by
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.1 hc; exact hq n
  have hfS : (f.toSubring T (sub f hfT)).Monic := by rw [monic_toSubring]; exact hf
  have e1 := map_divByMonic (p := p.toSubring T (sub p hp)) T.subtype hfS
  have e2 := map_modByMonic (p := p.toSubring T (sub p hp)) T.subtype hfS
  rw [map_toSubring, map_toSubring] at e1 e2
  exact ⟨fun k => by rw [← e1, coeff_map]; exact SetLike.coe_mem _,
    fun k => by rw [← e2, coeff_map]; exact SetLike.coe_mem _⟩

theorem v_ϖ_ne_zero : D.ϖ ≠ 0 := fun h0 => by
  have h := D.v_ϖ; rw [h0, AddValuation.map_zero] at h; exact WithTop.top_ne_coe h

/-- Successive approximation: `x ≡ g(ϖ) mod 𝔭^N` with `g` having `G`-fixed integral coefficients. -/
theorem approx (N : ℕ) : ∀ x : L, 0 ≤ D.v x → ∃ g : L[X], CoeffIn (D.intSub ⊤) g ∧
    (N : WithTop ℤ) ≤ D.v (x - g.eval D.ϖ) := by
  induction N with
  | zero =>
    intro x hx
    exact ⟨0, fun k => by rw [coeff_zero]; exact (D.intSub ⊤).zero_mem,
      by rw [eval_zero, sub_zero, Nat.cast_zero]; exact hx⟩
  | succ N ih =>
    intro x hx
    obtain ⟨a, ha, hva⟩ := D.res x hx
    set y := (x - a) * D.ϖ⁻¹ with hy
    have hxa : x - a = D.ϖ * y := by
      rw [hy, mul_comm (x - a), ← mul_assoc, mul_inv_cancel₀ D.v_ϖ_ne_zero, one_mul]
    have hy0 : 0 ≤ D.v y := by
      rw [hxa, AddValuation.map_mul, D.v_ϖ] at hva
      have h2 : (1 : WithTop ℤ) + 0 ≤ 1 + D.v y := by rwa [add_zero]
      exact (WithTop.add_le_add_iff_left WithTop.one_ne_top).1 h2
    have ha0 : 0 ≤ D.v a := by
      have h := D.v.map_le_sub hx (zero_le_one.trans hva)
      rwa [sub_sub_cancel] at h
    obtain ⟨g, hg, hvg⟩ := ih y hy0
    refine ⟨C a + X * g, fun k => ?_, ?_⟩
    · rcases k with _ | k
      · rw [coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero]
        exact (D.mem_intSub).2 ⟨fun σ _ => ha σ, ha0⟩
      · rw [coeff_add, coeff_C_succ, coeff_X_mul, zero_add]; exact hg k
    · have he : x - (C a + X * g).eval D.ϖ = D.ϖ * (y - g.eval D.ϖ) := by
        rw [eval_add, eval_C, eval_mul, eval_X, mul_sub, ← hxa]; ring
      rw [he, AddValuation.map_mul, D.v_ϖ, Nat.cast_succ, add_comm (N : WithTop ℤ)]
      exact add_le_add le_rfl hvg

theorem v_prod {ι : Type*} (s : Finset ι) (f : ι → L) :
    D.v (∏ i ∈ s, f i) = ∑ i ∈ s, D.v (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, AddValuation.map_one]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

theorem coe_add_one_le {m : ℤ} {w : WithTop ℤ} (h : (m : WithTop ℤ) < w) :
    ((m + 1 : ℤ) : WithTop ℤ) ≤ w := by
  induction w with
  | top => exact le_top
  | coe a => exact WithTop.coe_le_coe.2 (Int.add_one_le_of_lt (WithTop.coe_lt_coe.1 h))

/-- A sum whose nonzero terms have pairwise distinct valuations has the valuation of its smallest term. -/
theorem v_sum_le_of_distinct {ι : Type*} (s : Finset ι) (t : ι → L)
    (hd : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → t i ≠ 0 → D.v (t i) ≠ D.v (t k)) :
    ∀ k ∈ s, D.v (∑ i ∈ s, t i) ≤ D.v (t k) := by
  classical
  intro k hk
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image s (fun i => D.v (t i)) ⟨k, hk⟩
  refine le_trans ?_ (hmin k hk)
  by_cases htj : t j = 0
  · rw [htj, AddValuation.map_zero]; exact le_top
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (fun h => htj ((D.v.top_iff).1 h))
  rw [← Finset.add_sum_erase s t hj]
  refine le_of_eq (AddValuation.map_add_eq_of_lt_left D.v ?_)
  rw [← hm]
  refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 (lt_add_one m)) (D.v.map_le_sum fun i hi => ?_)
  have hi' := Finset.mem_of_mem_erase hi
  refine coe_add_one_le ?_
  rw [hm]
  exact lt_of_le_of_ne (hmin i hi') (hd j hj i hi' (Finset.ne_of_mem_erase hi).symm htj)

theorem le_v_eval (p : L[X]) {N : WithTop ℤ} (hp : ∀ k, N ≤ D.v (p.coeff k * D.ϖ ^ k)) :
    N ≤ D.v (p.eval D.ϖ) := by
  rw [eval_eq_sum, sum_def]; exact D.v.map_le_sum fun k _ => hp k

theorem v_mul_pow (c : L) (k : ℕ) : D.v (c * D.ϖ ^ k) = D.v c + (k : WithTop ℤ) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, D.v_ϖ, nsmul_one]

variable (H : Subgroup G) [Fintype H]

/-- `f = ∏_{h ∈ H} (X - h ϖ)`. -/
def fpol : L[X] := ∏ h : H, (X - C ((h : G) • D.ϖ))

theorem fpol_monic : (D.fpol H).Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem natDegree_fpol : (D.fpol H).natDegree = Fintype.card H := by
  rw [fpol, natDegree_prod_of_monic _ _ (fun h _ => monic_X_sub_C _)]
  simp

theorem eval_fpol : (D.fpol H).eval D.ϖ = 0 := by
  rw [fpol, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)

theorem map_fpol (σ : G) : (D.fpol H).map (MulSemiringAction.toRingHom G L σ) =
    ∏ h : H, (X - C ((σ * h) • D.ϖ)) := by
  rw [fpol, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [Polynomial.map_sub, map_X, map_C, MulSemiringAction.toRingHom_apply, mul_smul]

theorem fpol_coeff_fix {h₀ : G} (hh₀ : h₀ ∈ H) (k : ℕ) :
    h₀ • (D.fpol H).coeff k = (D.fpol H).coeff k := by
  have e1 := D.map_fpol H h₀
  have e2 : ∏ h : H, (X - C ((h₀ * h) • D.ϖ)) = D.fpol H :=
    Equiv.prod_comp (Equiv.mulLeft (⟨h₀, hh₀⟩ : H)) (fun h : H => X - C ((h : G) • D.ϖ))
  rw [e2] at e1
  have := congrArg (fun p => p.coeff k) e1
  simpa [coeff_map] using this

theorem fpol_coeffIn : CoeffIn (D.intSub H) (D.fpol H) := by
  have hint : CoeffIn (D.intSub ⊥) (D.fpol H) := coeffIn_prod _ _ fun h _ => coeffIn_X_sub_C
    ((D.mem_intSub).2 ⟨mem_bot_fix _, by rw [D.v_smul, D.v_ϖ]; exact zero_le_one⟩)
  exact fun k => (D.mem_intSub).2
    ⟨fun h₀ hh₀ => D.fpol_coeff_fix H hh₀ k, ((D.mem_intSub).1 (hint k)).2⟩

/-- Hypotheses of the quotient formula: `ϖH ∈ L^H`, `v ϖH = |H|`, `v(L^H \ 0) ⊆ |H| ℤ`. -/
structure QData (ϖH : L) : Prop where
  fix : ∀ h ∈ H, h • ϖH = ϖH
  v_eq : D.v ϖH = (Fintype.card H : ℕ)
  val : ∀ x : L, (∀ h ∈ H, h • x = x) → x ≠ 0 →
    ∃ k : ℤ, D.v x = (((Fintype.card H : ℤ) * k : ℤ) : WithTop ℤ)

variable {D H}

theorem QData.resH {ϖH : L} (hq : D.QData H ϖH) : ∀ x : L, (∀ h ∈ H, h • x = x) → 0 ≤ D.v x →
    ∃ a : L, (∀ σ : G, σ • a = a) ∧ ((Fintype.card H : ℕ) : WithTop ℤ) ≤ D.v (x - a) := by
  intro x hxH hx
  obtain ⟨a, ha, hva⟩ := D.res x hx
  refine ⟨a, ha, ?_⟩
  by_cases h0 : x - a = 0
  · rw [h0, AddValuation.map_zero]; exact le_top
  obtain ⟨k, hk⟩ := hq.val (x - a) (fun h hh => by rw [smul_sub, hxH h hh, ha h]) h0
  rw [hk] at hva ⊢
  have h1 : (1 : ℤ) ≤ Fintype.card H * k := WithTop.coe_le_coe.1 (by rw [WithTop.coe_one]; exact hva)
  have hc : (0 : ℤ) ≤ Fintype.card H := Int.natCast_nonneg _
  have hk1 : 1 ≤ k := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith
  rw [← WithTop.coe_natCast, WithTop.coe_le_coe]
  exact le_mul_of_one_le_right hc hk1

theorem QData.v_term_ne {ϖH : L} (hq : D.QData H ϖH) {c d : L} (hc : ∀ h ∈ H, h • c = c)
    (hd : ∀ h ∈ H, h • d = d) {i j : ℕ} (hi : i < Fintype.card H) (hj : j < Fintype.card H)
    (hij : i ≠ j) (hc0 : c * D.ϖ ^ i ≠ 0) : D.v (c * D.ϖ ^ i) ≠ D.v (d * D.ϖ ^ j) := by
  obtain ⟨m, hm⟩ := hq.val c hc (left_ne_zero_of_mul hc0)
  by_cases hd0 : d = 0
  · rw [hd0, zero_mul, AddValuation.map_zero]
    exact fun h => hc0 ((D.v.top_iff).1 h)
  obtain ⟨n, hn⟩ := hq.val d hd hd0
  rw [D.v_mul_pow, D.v_mul_pow, hm, hn, ← WithTop.coe_natCast, ← WithTop.coe_natCast,
    ← WithTop.coe_add, ← WithTop.coe_add, Ne, WithTop.coe_eq_coe]
  intro h
  have he : (0 : ℤ) ≤ Fintype.card H := Int.natCast_nonneg _
  have hi' : (i : ℤ) < Fintype.card H := by exact_mod_cast hi
  have hj' : (j : ℤ) < Fintype.card H := by exact_mod_cast hj
  have hij' : (i : ℤ) ≠ j := by exact_mod_cast hij
  rcases lt_trichotomy m n with hmn | hmn | hmn
  · have : m + 1 ≤ n := hmn
    nlinarith
  · subst hmn; exact hij' (by linarith)
  · have : n + 1 ≤ m := hmn
    nlinarith

end LocData

end

end Swan
end RamanujanPetersson


