-- Prove2me | Definitions.Def_RPLib_S3_SSHasseA
-- name    : RPLib_S3_SSHasseA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:21:14.141213+00:00
-- url     : https://prove2.me/theorems/4f206cdc-afba-44ef-b596-e48461eae6b4
-- title:
--   Weight-two Ramanujan-Petersson library: the trace modulo `p` as a coefficient
-- statement:
--   The trace modulo `p` as a coefficient.
--
--   For a Weierstrass curve `W` over a finite field `F` of odd characteristic, `q = #F`:
--   * `gE W = 4X³ + b₂X² + 2b₄X + b₆` (on `E`, `(2y + a₁x + a₃)² = g_E(x)`);
--   * `trace_eq_neg_sum` : `a_E = -Σ_x χ(g_E(x))` (`χ` the quadratic character);
--   * `trace_cast_eq_coeff` : `(a_E : F) = [X^{q-1}] g_E^{(q-1)/2}`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_SSFib

/-!
# S3-DWS-Supersingular, part B1: the trace modulo `p` as a coefficient

For a Weierstrass curve `W` over a finite field `F` of odd characteristic, `q = #F`:
* `gE W = 4X³ + b₂X² + 2b₄X + b₆` (on `E`, `(2y + a₁x + a₃)² = g_E(x)`);
* `trace_eq_neg_sum` : `a_E = -Σ_x χ(g_E(x))` (`χ` the quadratic character);
* `trace_cast_eq_coeff` : `(a_E : F) = [X^{q-1}] g_E^{(q-1)/2}`.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve RPLib

namespace RamanujanPetersson.S3.DWSS

section HasseA

variable {F : Type*} [Field F]

/-- `g_E(X) = 4X³ + b₂X² + 2b₄X + b₆`. -/
noncomputable def gE (W : WeierstrassCurve F) : F[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

lemma eval_gE (W : WeierstrassCurve F) (x : F) :
    (gE W).eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [gE]

lemma natDegree_gE_le (W : WeierstrassCurve F) : (gE W).natDegree ≤ 3 := by
  unfold gE; compute_degree

lemma sq_form (W : WeierstrassCurve F) (x y : F) :
    (2 * y + W.a₁ * x + W.a₃) ^ 2 - (gE W).eval x =
      4 * ((y ^ 2 + W.a₁ * x * y + W.a₃ * y) - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) := by
  rw [eval_gE]; simp only [b₂, b₄, b₆]; ring

variable [Fintype F] [DecidableEq F]

lemma card_fibre_y (hF : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F) :
    ((Finset.univ.filter (fun y : F => y ^ 2 + W.a₁ * x * y + W.a₃ * y =
        x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)).card : ℤ) = quadraticChar F ((gE W).eval x) + 1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  rw [← quadraticChar_card_sqrts hF, Set.toFinset_ofPred]
  congr 1
  refine Finset.card_nbij' (fun y => 2 * y + W.a₁ * x + W.a₃) (fun w => (w - W.a₁ * x - W.a₃) / 2)
    ?_ ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have := sq_form W x y
    rw [hy.2, sub_self, mul_zero, sub_eq_zero] at this
    exact this
  · intro w hw
    rw [Finset.mem_coe, Finset.mem_filter] at hw ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have := sq_form W x ((w - W.a₁ * x - W.a₃) / 2)
    have e : 2 * ((w - W.a₁ * x - W.a₃) / 2) + W.a₁ * x + W.a₃ = w := by field_simp; ring
    rw [e, hw.2, sub_self] at this
    exact sub_eq_zero.mp ((mul_eq_zero.mp this.symm).resolve_left h4)
  · intro y _; field_simp; ring
  · intro w _; field_simp; ring

lemma card_filter_prod (W : WeierstrassCurve F) :
    (((Finset.univ.filter (fun xy : F × F => xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 =
        xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆)).card : ℕ) : ℤ) =
      ∑ x : F, ((Finset.univ.filter (fun y : F => y ^ 2 + W.a₁ * x * y + W.a₃ * y =
        x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)).card : ℤ) := by
  rw [Finset.card_filter, Nat.cast_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.card_filter, Nat.cast_sum]

/-- `a_E = -Σ_x χ(g_E(x))`. -/
theorem trace_eq_neg_sum (hF : ringChar F ≠ 2) (W : WeierstrassCurve F) [W.IsElliptic] :
    EllFq.trace W = -∑ x : F, quadraticChar F ((gE W).eval x) := by
  rw [EllFq.trace, EllFq.numPoints_eq_card_filter, Nat.card_eq_fintype_card]
  push_cast
  rw [card_filter_prod]
  simp only [card_fibre_y hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  ring

lemma sum_pow_eq (_hq : 2 ≤ Fintype.card F) (k : ℕ) (hk : k < 2 * (Fintype.card F - 1)) :
    ∑ x : F, x ^ k = if k = Fintype.card F - 1 then -1 else 0 := by
  rcases lt_trichotomy k (Fintype.card F - 1) with h | h | h
  · rw [if_neg h.ne]; exact FiniteField.sum_pow_lt_card_sub_one F k h
  · rw [if_pos h, h]
    have e : ∀ x : F, x ^ (Fintype.card F - 1) = 1 - if x = 0 then 1 else 0 := fun x => by
      split_ifs with hx
      · rw [hx, zero_pow (by omega)]; ring
      · rw [FiniteField.pow_card_sub_one_eq_one x hx]; ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, FiniteField.cast_card_eq_zero]
    ring
  · rw [if_neg h.ne']
    have e : ∀ x : F, x ^ k = x ^ (k - (Fintype.card F - 1)) := fun x => by
      by_cases hx : x = 0
      · rw [hx, zero_pow (by omega), zero_pow (by omega)]
      · conv_lhs => rw [show k = (Fintype.card F - 1) + (k - (Fintype.card F - 1)) by omega]
        rw [pow_add, FiniteField.pow_card_sub_one_eq_one x hx, one_mul]
    simp only [e]
    exact FiniteField.sum_pow_lt_card_sub_one F _ (by omega)

/-- **B1.** `(a_E : F) = [X^{q-1}] g_E^{(q-1)/2}` (`q/2 = (q-1)/2` as `q` is odd). -/
theorem trace_cast_eq_coeff (hF : ringChar F ≠ 2) (W : WeierstrassCurve F) [W.IsElliptic] :
    ((EllFq.trace W : ℤ) : F) = (gE W ^ (Fintype.card F / 2)).coeff (Fintype.card F - 1) := by
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  have hdeg : (gE W ^ (Fintype.card F / 2)).natDegree < 2 * (Fintype.card F - 1) := by
    calc (gE W ^ (Fintype.card F / 2)).natDegree ≤ (Fintype.card F / 2) * 3 :=
          natDegree_pow_le_of_le _ (natDegree_gE_le W)
      _ < 2 * (Fintype.card F - 1) := by omega
  rw [trace_eq_neg_sum hF W]
  push_cast
  simp_rw [quadraticChar_eq_pow_of_char_ne_two' hF, ← eval_pow, eval_eq_sum_range' hdeg]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun k hk => by rw [sum_pow_eq hq2 k (Finset.mem_range.mp hk)])]
  simp only [mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
  rw [if_pos (by omega), neg_neg]

end HasseA

end RamanujanPetersson.S3.DWSS


