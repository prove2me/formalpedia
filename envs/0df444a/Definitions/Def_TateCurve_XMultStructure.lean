-- Prove2me | Definitions.Def_TateCurve_XMultStructure
-- name    : TateCurve_XMultStructure
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/aaea6a50-303c-59dc-8b88-6e9c44a4a300
-- title:
--   Tate curve x-only addition defects, admissibility, descent engine
-- statement:
--   Throughout, $K$ is a nontrivially normed field with ultrametric distance (complete where series are involved), $q$ a parameter of the Tate curve, and $a_4(q)$, $a_6(q)$, $\mathrm{pointX}$, $\mathrm{xfun}$ the $q$-series coefficients, the $x$-coordinate $\mathrm{pointX}\,q\,u=\sum_{n\in\mathbb Z}\mathrm{xfun}(q^nu)-2s_1(q)$ with $\mathrm{xfun}(w)=w/(1-w)^2$, as fixed in the earlier modules.
--
--   Two cleared symmetric functions are introduced: $\mathrm{symSumNum}\,q\,x_1\,x_2 = 2x_1x_2(x_1+x_2)+x_1x_2+2a_4(q)(x_1+x_2)+4a_6(q)$ and $\mathrm{symProdNum}\,q\,x_1\,x_2 = (x_1x_2)^2-2a_4(q)x_1x_2-4a_6(q)(x_1+x_2)-a_6(q)+a_4(q)^2$; both are symmetric in $x_1,x_2$, and they are rewritten using the $b$-invariants of `curve q`, computed here to be $b_2=1$, $b_4=2a_4(q)$, $b_6=4a_6(q)$, $b_8=a_6(q)-a_4(q)^2$.
--
--   Admissibility is recorded by `OffLattice q w`, the condition $q^nw\neq 1$ for all $n\in\mathbb Z$, stable under $w\mapsto q^kw$ and $w\mapsto w^{-1}$, and by the structure `AddParams q u v`, whose fields assert $q,u,v\neq 0$ together with `OffLattice` for $u$, $v$, $uv$ and $uv^{-1}$; it is shown stable under swapping $u,v$, inverting either argument, and multiplying either argument by $q$.
--
--   The defects $\mathrm{addDefectSum}\,q\,u\,v$ and $\mathrm{addDefectProd}\,q\,u\,v$ are the differences between $(\mathrm{pointX}(uv)+\mathrm{pointX}(uv^{-1}))(\mathrm{pointX}\,u-\mathrm{pointX}\,v)^2$, respectively $\mathrm{pointX}(uv)\,\mathrm{pointX}(uv^{-1})(\mathrm{pointX}\,u-\mathrm{pointX}\,v)^2$, and the corresponding symmetric numerator; their vanishing is exactly the asserted identity. Both are invariant under $u\mapsto qu$, $v\mapsto qv$, under $u\mapsto u^{-1}$ given `AddParams`, under $v\mapsto v^{-1}$ given $q\neq0$, $v\neq0$ and `OffLattice q v`, and under swapping $u,v$ given $q,u,v\neq 0$ and `OffLattice q (u*v⁻¹)`. The nodal ($q$-free) analogues of the two identities are proved for $\mathrm{xfun}$ under $u,v\neq0$, $u,v,uv,uv^{-1}\neq1$, and `AddParams q u v` is produced from $q\neq0$, $1<\|u\|$, $\|q\|\|u\|<1$, $\|v\|=1$, $v\neq1$.
--
--   A final section sets up a descent for a doubly indexed family $c:\mathbb N\to\mathbb N\to K$: $\mathrm{specTail}\,c\,w\,M=\sum_{k\ge1}c(M+k,k)w^{-k}$, $\mathrm{specAlpha}\,c\,w\,M=\sum c(i,j)w^j$ over $i+j=M$ with $1\le j\le i$, and $\mathrm{specGamma}\,c\,M=\sum_{k=1}^M(-2)c(M,k)$. Assuming a uniform bound $\|c(N,k)\|\le B$ and the identity $\sum_{k=1}^{M}c(M,k)(w^k+w^{-k}-2)=\mathrm{specAlpha}+\mathrm{specTail}+\mathrm{specGamma}$ for all $M$ and all $w$ with $\|w\|>1$, it is concluded that $c(N,k)=0$ whenever $1\le k\le N$; the proof isolates single coefficients by letting $w$ run through powers of an element of norm $>1$ and inducts on $N$ and on the codimension $N-k$.
--
--   **Relation to Mathlib.** Mathlib supplies the normed-field and Weierstrass-curve background (the $b$-invariants of `WeierstrassCurve` are computed here for `curve q`); `OffLattice`, `AddParams`, the two cleared symmetric numerators, the addition defects, and the bounded-coefficient descent are the project's own notions.
--
--   **Where it is used.** The defects and their symmetries reduce the $x$-only addition law on the Tate curve to checks on a fundamental region for the multiplicative parameter, and the descent lemma is the bounded-coefficient counterpart of the $q$-shift argument that forces the relevant correction coefficients to vanish; together they serve the analytic parametrisation of the Tate curve and its $p$-torsion used in the Galois-representation part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TateCurve_XMultStructure.lean

import Mathlib
import Definitions.Def_TateCurve_QShift
import Theorems.Thm_TateCurve_pointX_inv
import Theorems.Thm_TateCurve_pointX_q_mul
import Theorems.Thm_TateCurve_pointX_zpow_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section SymPolynomials

variable (q x₁ x₂ : K)

noncomputable def symSumNum : K :=
  2 * (x₁ * x₂) * (x₁ + x₂) + x₁ * x₂ + 2 * a₄ q * (x₁ + x₂) + 4 * a₆ q

noncomputable def symProdNum : K :=
  (x₁ * x₂) ^ 2 - 2 * a₄ q * (x₁ * x₂) - 4 * a₆ q * (x₁ + x₂) - a₆ q + (a₄ q) ^ 2

variable {q x₁ x₂}

lemma symSumNum_comm : symSumNum q x₂ x₁ = symSumNum q x₁ x₂ := by
  unfold symSumNum; ring

lemma symProdNum_comm : symProdNum q x₂ x₁ = symProdNum q x₁ x₂ := by
  unfold symProdNum; ring

lemma curve_b₂ : (curve q).b₂ = 1 := by
  simp only [WeierstrassCurve.b₂, curve_a₁, curve_a₂]; ring

lemma curve_b₄ : (curve q).b₄ = 2 * a₄ q := by
  simp only [WeierstrassCurve.b₄, curve_a₁, curve_a₃, curve_a₄]; ring

lemma curve_b₆ : (curve q).b₆ = 4 * a₆ q := by
  simp only [WeierstrassCurve.b₆, curve_a₃, curve_a₆]; ring

lemma curve_b₈ : (curve q).b₈ = a₆ q - (a₄ q) ^ 2 := by
  simp only [WeierstrassCurve.b₈, curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆]; ring

lemma symSumNum_eq_b :
    symSumNum q x₁ x₂ =
      2 * (x₁ * x₂) * (x₁ + x₂) + (curve q).b₂ * (x₁ * x₂) + (curve q).b₄ * (x₁ + x₂) +
        (curve q).b₆ := by
  rw [curve_b₂, curve_b₄, curve_b₆]; unfold symSumNum; ring

lemma symProdNum_eq_b :
    symProdNum q x₁ x₂ =
      (x₁ * x₂) ^ 2 - (curve q).b₄ * (x₁ * x₂) - (curve q).b₆ * (x₁ + x₂) - (curve q).b₈ := by
  rw [curve_b₄, curve_b₆, curve_b₈]; unfold symProdNum; ring

end SymPolynomials

section Admissibility

variable {q u v w : K}

abbrev OffLattice (q w : K) : Prop := ∀ n : ℤ, q ^ n * w ≠ 1

lemma OffLattice.zpow_mul (hq0 : q ≠ 0) (k : ℤ) (h : OffLattice q w) :
    OffLattice q (q ^ k * w) := by
  intro n hn
  apply h (n + k)
  rwa [← mul_assoc, ← zpow_add₀ hq0] at hn

lemma OffLattice.q_mul (hq0 : q ≠ 0) (h : OffLattice q w) : OffLattice q (q * w) := by
  have h1 := h.zpow_mul hq0 1
  rwa [zpow_one] at h1

lemma OffLattice.inv (hq0 : q ≠ 0) (h : OffLattice q w) : OffLattice q w⁻¹ := by
  intro n hn
  have hw : w ≠ 0 := by
    intro h0
    rw [h0, inv_zero, mul_zero] at hn
    exact zero_ne_one hn

  have hwq : q ^ n = w := by
    have h1 : q ^ n * w⁻¹ * w = 1 * w := by rw [hn]
    rwa [mul_assoc, inv_mul_cancel₀ hw, mul_one, one_mul] at h1
  apply h (-n)
  rw [← hwq, zpow_neg]
  exact inv_mul_cancel₀ (zpow_ne_zero n hq0)

structure AddParams (q u v : K) : Prop where
  q_ne_zero : q ≠ 0
  u_ne_zero : u ≠ 0
  v_ne_zero : v ≠ 0
  offLattice_u : OffLattice q u
  offLattice_v : OffLattice q v
  offLattice_mul : OffLattice q (u * v)
  offLattice_div : OffLattice q (u * v⁻¹)

namespace AddParams

lemma swap (h : AddParams q u v) : AddParams q v u where
  q_ne_zero := h.q_ne_zero
  u_ne_zero := h.v_ne_zero
  v_ne_zero := h.u_ne_zero
  offLattice_u := h.offLattice_v
  offLattice_v := h.offLattice_u
  offLattice_mul := by rw [mul_comm]; exact h.offLattice_mul
  offLattice_div := by
    have h1 := OffLattice.inv h.q_ne_zero h.offLattice_div
    rwa [mul_inv_rev, inv_inv] at h1

lemma inv_left (h : AddParams q u v) : AddParams q u⁻¹ v where
  q_ne_zero := h.q_ne_zero
  u_ne_zero := inv_ne_zero h.u_ne_zero
  v_ne_zero := h.v_ne_zero
  offLattice_u := OffLattice.inv h.q_ne_zero h.offLattice_u
  offLattice_v := h.offLattice_v
  offLattice_mul := by
    have h1 := OffLattice.inv h.q_ne_zero h.offLattice_div
    rwa [mul_inv_rev, inv_inv, mul_comm] at h1
  offLattice_div := by
    have h1 := OffLattice.inv h.q_ne_zero h.offLattice_mul
    rwa [mul_inv_rev, mul_comm] at h1

lemma inv_right (h : AddParams q u v) : AddParams q u v⁻¹ where
  q_ne_zero := h.q_ne_zero
  u_ne_zero := h.u_ne_zero
  v_ne_zero := inv_ne_zero h.v_ne_zero
  offLattice_u := h.offLattice_u
  offLattice_v := OffLattice.inv h.q_ne_zero h.offLattice_v
  offLattice_mul := h.offLattice_div
  offLattice_div := by
    rw [inv_inv]
    exact h.offLattice_mul

lemma q_mul_left (h : AddParams q u v) : AddParams q (q * u) v where
  q_ne_zero := h.q_ne_zero
  u_ne_zero := mul_ne_zero h.q_ne_zero h.u_ne_zero
  v_ne_zero := h.v_ne_zero
  offLattice_u := OffLattice.q_mul h.q_ne_zero h.offLattice_u
  offLattice_v := h.offLattice_v
  offLattice_mul := by
    rw [mul_assoc]
    exact OffLattice.q_mul h.q_ne_zero h.offLattice_mul
  offLattice_div := by
    rw [mul_assoc]
    exact OffLattice.q_mul h.q_ne_zero h.offLattice_div

lemma q_mul_right (h : AddParams q u v) : AddParams q u (q * v) where
  q_ne_zero := h.q_ne_zero
  u_ne_zero := h.u_ne_zero
  v_ne_zero := mul_ne_zero h.q_ne_zero h.v_ne_zero
  offLattice_u := h.offLattice_u
  offLattice_v := OffLattice.q_mul h.q_ne_zero h.offLattice_v
  offLattice_mul := by
    rw [show u * (q * v) = q * (u * v) by ring]
    exact OffLattice.q_mul h.q_ne_zero h.offLattice_mul
  offLattice_div := by
    have h1 := OffLattice.zpow_mul h.q_ne_zero (-1) h.offLattice_div
    rw [zpow_neg_one] at h1
    rw [show u * (q * v)⁻¹ = q⁻¹ * (u * v⁻¹) by rw [mul_inv_rev]; ring]
    exact h1

end AddParams

end Admissibility

section Defects

variable [CompleteSpace K] {q u v w : K}

lemma pointX_inv_mul (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hdiv : OffLattice q (u * v⁻¹)) :
    pointX q (u⁻¹ * v) = pointX q (u * v⁻¹) := by
  rw [show u⁻¹ * v = (u * v⁻¹)⁻¹ by rw [mul_inv_rev, inv_inv, mul_comm]]
  exact pointX_inv hq0 (mul_ne_zero hu0 (inv_ne_zero hv0)) hdiv

lemma pointX_inv_mul_inv (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hmul : OffLattice q (u * v)) :
    pointX q (u⁻¹ * v⁻¹) = pointX q (u * v) := by
  rw [show u⁻¹ * v⁻¹ = (u * v)⁻¹ by rw [mul_inv_rev, mul_comm]]
  exact pointX_inv hq0 (mul_ne_zero hu0 hv0) hmul

lemma pointX_q_inv_mul (hq0 : q ≠ 0) : pointX q (q⁻¹ * w) = pointX q w := by
  have h := pointX_zpow_mul (u := w) hq0 (-1)
  rwa [zpow_neg_one] at h

variable (q u v)

noncomputable def addDefectSum : K :=
  (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 -
    symSumNum q (pointX q u) (pointX q v)

noncomputable def addDefectProd : K :=
  pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 -
    symProdNum q (pointX q u) (pointX q v)

variable {q u v}

lemma addDefectSum_eq_zero_iff :
    addDefectSum q u v = 0 ↔
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        symSumNum q (pointX q u) (pointX q v) := by
  unfold addDefectSum; exact sub_eq_zero

lemma addDefectProd_eq_zero_iff :
    addDefectProd q u v = 0 ↔
      pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
        symProdNum q (pointX q u) (pointX q v) := by
  unfold addDefectProd; exact sub_eq_zero

theorem addDefectSum_q_mul_left (hq0 : q ≠ 0) :
    addDefectSum q (q * u) v = addDefectSum q u v := by
  unfold addDefectSum
  rw [mul_assoc q u v, mul_assoc q u v⁻¹, pointX_q_mul hq0, pointX_q_mul hq0,
    pointX_q_mul hq0]

theorem addDefectProd_q_mul_left (hq0 : q ≠ 0) :
    addDefectProd q (q * u) v = addDefectProd q u v := by
  unfold addDefectProd
  rw [mul_assoc q u v, mul_assoc q u v⁻¹, pointX_q_mul hq0, pointX_q_mul hq0,
    pointX_q_mul hq0]

theorem addDefectSum_q_mul_right (hq0 : q ≠ 0) :
    addDefectSum q u (q * v) = addDefectSum q u v := by
  unfold addDefectSum
  rw [show u * (q * v) = q * (u * v) by ring,
    show u * (q * v)⁻¹ = q⁻¹ * (u * v⁻¹) by rw [mul_inv_rev]; ring,
    pointX_q_mul hq0, pointX_q_inv_mul hq0, pointX_q_mul hq0]

theorem addDefectProd_q_mul_right (hq0 : q ≠ 0) :
    addDefectProd q u (q * v) = addDefectProd q u v := by
  unfold addDefectProd
  rw [show u * (q * v) = q * (u * v) by ring,
    show u * (q * v)⁻¹ = q⁻¹ * (u * v⁻¹) by rw [mul_inv_rev]; ring,
    pointX_q_mul hq0, pointX_q_inv_mul hq0, pointX_q_mul hq0]

theorem addDefectSum_inv_left (h : AddParams q u v) :
    addDefectSum q u⁻¹ v = addDefectSum q u v := by
  unfold addDefectSum
  rw [pointX_inv_mul h.q_ne_zero h.u_ne_zero h.v_ne_zero h.offLattice_div,
    pointX_inv_mul_inv h.q_ne_zero h.u_ne_zero h.v_ne_zero h.offLattice_mul,
    pointX_inv h.q_ne_zero h.u_ne_zero h.offLattice_u]
  ring

theorem addDefectProd_inv_left (h : AddParams q u v) :
    addDefectProd q u⁻¹ v = addDefectProd q u v := by
  unfold addDefectProd
  rw [pointX_inv_mul h.q_ne_zero h.u_ne_zero h.v_ne_zero h.offLattice_div,
    pointX_inv_mul_inv h.q_ne_zero h.u_ne_zero h.v_ne_zero h.offLattice_mul,
    pointX_inv h.q_ne_zero h.u_ne_zero h.offLattice_u]
  ring

theorem addDefectSum_inv_right (hq0 : q ≠ 0) (hv0 : v ≠ 0) (hv : OffLattice q v) :
    addDefectSum q u v⁻¹ = addDefectSum q u v := by
  unfold addDefectSum
  rw [inv_inv, pointX_inv hq0 hv0 hv]
  ring

theorem addDefectProd_inv_right (hq0 : q ≠ 0) (hv0 : v ≠ 0) (hv : OffLattice q v) :
    addDefectProd q u v⁻¹ = addDefectProd q u v := by
  unfold addDefectProd
  rw [inv_inv, pointX_inv hq0 hv0 hv]
  ring

theorem addDefectSum_swap (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hdiv : OffLattice q (u * v⁻¹)) :
    addDefectSum q v u = addDefectSum q u v := by
  unfold addDefectSum
  rw [mul_comm v u, show v * u⁻¹ = (u * v⁻¹)⁻¹ by rw [mul_inv_rev, inv_inv],
    pointX_inv hq0 (mul_ne_zero hu0 (inv_ne_zero hv0)) hdiv, symSumNum_comm]
  ring

theorem addDefectProd_swap (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hdiv : OffLattice q (u * v⁻¹)) :
    addDefectProd q v u = addDefectProd q u v := by
  unfold addDefectProd
  rw [mul_comm v u, show v * u⁻¹ = (u * v⁻¹)⁻¹ by rw [mul_inv_rev, inv_inv],
    pointX_inv hq0 (mul_ne_zero hu0 (inv_ne_zero hv0)) hdiv, symProdNum_comm]
  ring

end Defects

section Nodal

variable {u v : K}

theorem nodal_symSum (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v ≠ 1) (huv' : u * v⁻¹ ≠ 1) :
    (xfun (u * v) + xfun (u * v⁻¹)) * (xfun u - xfun v) ^ 2 =
      2 * (xfun u * xfun v) * (xfun u + xfun v) + xfun u * xfun v := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have h1v : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  have h1uv : (1 : K) - u * v ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have h1uv' : (1 : K) - u * v⁻¹ ≠ 0 := sub_ne_zero.mpr (Ne.symm huv')
  have hne : u ≠ v := by
    intro h
    exact huv' (by rw [h, mul_inv_cancel₀ hv0])
  have hsub : u - v ≠ 0 := sub_ne_zero.mpr hne
  have hsub' : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  unfold xfun
  field_simp
  ring

theorem nodal_symProd (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v ≠ 1) (huv' : u * v⁻¹ ≠ 1) :
    xfun (u * v) * xfun (u * v⁻¹) * (xfun u - xfun v) ^ 2 = (xfun u * xfun v) ^ 2 := by
  have h1u : (1 : K) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have h1v : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  have h1uv : (1 : K) - u * v ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have h1uv' : (1 : K) - u * v⁻¹ ≠ 0 := sub_ne_zero.mpr (Ne.symm huv')
  have hne : u ≠ v := by
    intro h
    exact huv' (by rw [h, mul_inv_cancel₀ hv0])
  have hsub : u - v ≠ 0 := sub_ne_zero.mpr hne
  have hsub' : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  unfold xfun
  field_simp
  ring

end Nodal

section Region

variable [CompleteSpace K] {q u v : K}

lemma offLattice_of_norm_eq_one (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hv : ‖v‖ = 1) (hv1 : v ≠ 1) :
    OffLattice q v := by
  intro n hn
  have hq0' : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0

  have hnorm : ‖q‖ ^ n = 1 := by
    have h1 := congrArg norm hn
    rwa [norm_mul, norm_zpow, hv, mul_one, norm_one] at h1

  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with hneg | hzero | hpos
    · exfalso
      have h2 : ‖q‖ ^ (-n) ≤ ‖q‖ ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ hq0' (le_of_lt hq) (by omega)
      have h3 : ‖q‖ ^ (-n) * ‖q‖ ^ n = 1 := by
        rw [← zpow_add₀ (ne_of_gt hq0')]
        simp
      rw [hnorm, mul_one] at h3
      rw [zpow_one, h3] at h2
      linarith
    · exact hzero
    · exfalso
      have h2 : ‖q‖ ^ n ≤ ‖q‖ ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ hq0' (le_of_lt hq) (by omega)
      rw [zpow_one, hnorm] at h2
      linarith
  rw [hn0, zpow_zero, one_mul] at hn
  exact hv1 hn

theorem addParams_of_norm_one_spectator (hq0 : q ≠ 0) (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1)
    (hv : ‖v‖ = 1) (hv1 : v ≠ 1) : AddParams q u v := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hu hqu
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv
    exact zero_ne_one hv
  refine ⟨hq0, ne_zero_of_one_lt_norm hu, hv0, qshift_lattice_ne_one hq0 hu hqu,
    offLattice_of_norm_eq_one hq0 hq1 hv hv1, ?_, ?_⟩
  ·
    have h1 : 1 < ‖u * v‖ := by rw [norm_mul, hv, mul_one]; exact hu
    have h2 : ‖q‖ * ‖u * v‖ < 1 := by rw [norm_mul, hv, mul_one]; exact hqu
    exact qshift_lattice_ne_one hq0 h1 h2
  ·
    have h1 : 1 < ‖u * v⁻¹‖ := by rw [norm_mul, norm_inv, hv, inv_one, mul_one]; exact hu
    have h2 : ‖q‖ * ‖u * v⁻¹‖ < 1 := by
      rw [norm_mul, norm_inv, hv, inv_one, mul_one]; exact hqu
    exact qshift_lattice_ne_one hq0 h1 h2

end Region

end TateCurve

set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section UnitSpectator

variable {q u v : K}

lemma norm_inv_eq_one_of_norm_eq_one (hv : ‖v‖ = 1) : ‖v⁻¹‖ = 1 := by
  rw [norm_inv, hv, inv_one]

lemma ne_zero_of_norm_eq_one (hv : ‖v‖ = 1) : v ≠ 0 := by
  intro h
  rw [h, norm_zero] at hv
  exact zero_ne_one hv

lemma norm_mul_eq_of_norm_eq_one (hv : ‖v‖ = 1) (u : K) : ‖u * v‖ = ‖u‖ := by
  rw [norm_mul, hv, mul_one]

lemma norm_mul_inv_eq_of_norm_eq_one (hv : ‖v‖ = 1) (u : K) : ‖u * v⁻¹‖ = ‖u‖ := by
  rw [norm_mul, norm_inv_eq_one_of_norm_eq_one hv, mul_one]

lemma one_lt_norm_mul_of_norm_eq_one (hv : ‖v‖ = 1) (hu : 1 < ‖u‖) : 1 < ‖u * v‖ := by
  rw [norm_mul_eq_of_norm_eq_one hv]; exact hu

lemma one_lt_norm_mul_inv_of_norm_eq_one (hv : ‖v‖ = 1) (hu : 1 < ‖u‖) : 1 < ‖u * v⁻¹‖ := by
  rw [norm_mul_inv_eq_of_norm_eq_one hv]; exact hu

lemma norm_q_mul_norm_mul_lt_one_of_norm_eq_one (hv : ‖v‖ = 1)
    (hqu : ‖q‖ * ‖u‖ < 1) : ‖q‖ * ‖u * v‖ < 1 := by
  rw [norm_mul_eq_of_norm_eq_one hv]; exact hqu

lemma norm_q_mul_norm_mul_inv_lt_one_of_norm_eq_one (hv : ‖v‖ = 1)
    (hqu : ‖q‖ * ‖u‖ < 1) : ‖q‖ * ‖u * v⁻¹‖ < 1 := by
  rw [norm_mul_inv_eq_of_norm_eq_one hv]; exact hqu

lemma norm_zpow_eq_one_of_norm_eq_one (hv : ‖v‖ = 1) (j : ℤ) : ‖v ^ j‖ = 1 := by
  rw [norm_zpow, hv, one_zpow]

lemma norm_finsetSum_mul_zpow_le_of_norm_eq_one (hv : ‖v‖ = 1) {s : Finset ℤ} {a : ℤ → K}
    {B : ℝ} (hB : 0 ≤ B) (ha : ∀ j ∈ s, ‖a j‖ ≤ B) :
    ‖∑ j ∈ s, a j * v ^ j‖ ≤ B := by
  refine norm_sum_le_of_forall_le_of_nonneg hB fun j hj => ?_
  rw [norm_mul, norm_zpow_eq_one_of_norm_eq_one hv, mul_one]
  exact ha j hj

end UnitSpectator

section BoundedDescent

variable (c : ℕ → ℕ → K)

noncomputable def specTail (w : K) (M : ℕ) : K :=
  ∑' k : ℕ, if 1 ≤ k then c (M + k) k * w⁻¹ ^ k else 0

noncomputable def specAlpha (w : K) (M : ℕ) : K :=
  ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal M).filter (fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1), c p.1 p.2 * w ^ p.2

noncomputable def specGamma (M : ℕ) : K :=
  ∑ k ∈ Finset.Icc 1 M, (-2 : K) * c M k

variable {c} {B : ℝ} {w : K}

lemma summable_specTail_term (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B) (hw : 1 < ‖w‖) (M : ℕ) :
    Summable fun k : ℕ => if 1 ≤ k then c (M + k) k * w⁻¹ ^ k else 0 := by
  refine Summable.of_norm ?_
  have hgeom : Summable fun k : ℕ => B * ‖w⁻¹‖ ^ k :=
    (summable_geometric_of_lt_one (norm_nonneg _)
      (norm_inv_lt_one_of_one_lt_norm hw)).mul_left B
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hgeom
  by_cases hk : 1 ≤ k
  · rw [if_pos hk, norm_mul, norm_pow]
    have h1 : ‖c (M + k) k‖ ≤ B := hc _ _
    have h2 : (0 : ℝ) ≤ ‖w⁻¹‖ ^ k := pow_nonneg (norm_nonneg _) k
    nlinarith
  · rw [if_neg hk]
    simp only [norm_zero]
    have h2 : (0 : ℝ) ≤ ‖w⁻¹‖ ^ k := pow_nonneg (norm_nonneg _) k
    nlinarith

lemma norm_specTail_le (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B) (hw : 1 < ‖w‖) (M : ℕ) :
    ‖specTail c w M‖ ≤ B := by
  refine norm_tsum_le_of_forall_le_of_nonneg hB fun k => ?_
  by_cases hk : 1 ≤ k
  · rw [if_pos hk, norm_mul, norm_pow]
    have h1 : ‖c (M + k) k‖ ≤ B := hc _ _
    have h2 : ‖w⁻¹‖ ^ k ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_inv_le_one_of_one_lt_norm hw)
    nlinarith [norm_nonneg (c (M + k) k), pow_nonneg (norm_nonneg w⁻¹) k]
  · rw [if_neg hk, norm_zero]
    exact hB

lemma spec_eq_zero_of_diamond (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B) {M k₀ : ℕ}
    (hk₀1 : 1 ≤ k₀) (hk₀M : k₀ ≤ M)
    (hdiamond : ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k) = specTail c w M)
    (hbig : ∀ k', k₀ < k' → k' ≤ M → c M k' = 0) :
    c M k₀ = 0 := by

  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
  have hx0 : x ≠ 0 := ne_zero_of_one_lt_norm hx
  have hxinv : ‖x⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hx
  set v : ℕ → K := fun t => x ^ (t + 1) with hv
  have hv0 : ∀ t, v t ≠ 0 := fun t => pow_ne_zero _ hx0
  have hvnorm : ∀ t, ‖v t‖ = ‖x‖ ^ (t + 1) := fun t => by rw [hv]; exact norm_pow x (t + 1)
  have hvbig : ∀ t, 1 < ‖v t‖ := by
    intro t
    rw [hvnorm t]
    exact one_lt_pow₀ hx (Nat.succ_ne_zero t)
  have hvinvnorm : ∀ t, ‖(v t)⁻¹‖ = ‖x⁻¹‖ ^ (t + 1) := by
    intro t
    rw [norm_inv, hvnorm t, norm_inv, inv_pow]

  set f : ℕ → K := fun t => specTail c (v t) M * (v t)⁻¹ ^ k₀ with hf

  have hf0 : Tendsto f atTop (nhds 0) := by
    have hbound : ∀ t, ‖f t‖ ≤ B * (‖x⁻¹‖ ^ k₀) ^ (t + 1) := by
      intro t
      rw [hf]
      simp only []
      rw [norm_mul, norm_pow]
      have h1 : ‖specTail c (v t) M‖ ≤ B := norm_specTail_le hB hc (hvbig t) M
      have h2 : ‖(v t)⁻¹‖ ^ k₀ = (‖x⁻¹‖ ^ (t + 1)) ^ k₀ := by rw [hvinvnorm t]
      have h3 : (‖x⁻¹‖ ^ (t + 1)) ^ k₀ = (‖x⁻¹‖ ^ k₀) ^ (t + 1) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have h4 : (0 : ℝ) ≤ ‖(v t)⁻¹‖ ^ k₀ := pow_nonneg (norm_nonneg _) _
      calc ‖specTail c (v t) M‖ * ‖(v t)⁻¹‖ ^ k₀ ≤ B * ‖(v t)⁻¹‖ ^ k₀ :=
            mul_le_mul_of_nonneg_right h1 h4
        _ = B * (‖x⁻¹‖ ^ k₀) ^ (t + 1) := by rw [h2, h3]
    have hratio : ‖x⁻¹‖ ^ k₀ < 1 :=
      pow_lt_one₀ (norm_nonneg _) hxinv (by omega)
    have hgeo : Tendsto (fun t : ℕ => B * (‖x⁻¹‖ ^ k₀) ^ (t + 1)) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => (‖x⁻¹‖ ^ k₀) ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg (norm_nonneg _) _) hratio
      have h2 : Tendsto (fun t : ℕ => (‖x⁻¹‖ ^ k₀) ^ (t + 1)) atTop (nhds 0) :=
        h1.comp (tendsto_add_atTop_nat 1)
      have h3 := h2.const_mul B
      rw [mul_zero] at h3
      exact h3
    exact squeeze_zero_norm hbound hgeo

  have hflim : Tendsto f atTop (nhds (c M k₀)) := by

    have hfeq : ∀ t, f t
        = ∑ k ∈ Finset.Icc 1 M, c M k * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀ := by
      intro t
      rw [hf]
      simp only []
      rw [← hdiamond (v t) (hvbig t), Finset.sum_mul]

    have hterm : ∀ k ∈ Finset.Icc 1 M,
        Tendsto (fun t => c M k * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀)
          atTop (nhds (if k = k₀ then c M k₀ else 0)) := by
      intro k hk
      have hkM : k ≤ M := (Finset.mem_Icc.mp hk).2
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1

      have hpt : ∀ t, c M k * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀
          = c M k * ((x ^ k * (x ^ k₀)⁻¹) ^ (t + 1) + ((x ^ (k + k₀))⁻¹) ^ (t + 1)) := by
        intro t
        rw [hv]
        simp only []
        have hxp : x ^ (t + 1) ≠ 0 := pow_ne_zero _ hx0
        field_simp
        ring
      rcases lt_trichotomy k k₀ with hlt | heq | hgt
      ·
        rw [if_neg (Nat.ne_of_lt hlt)]
        have hw1 : ‖x ^ k * (x ^ k₀)⁻¹‖ < 1 := by
          rw [norm_mul, norm_inv, norm_pow, norm_pow, ← div_eq_mul_inv]
          rw [div_lt_one (pow_pos (lt_trans one_pos hx) k₀)]
          exact pow_lt_pow_right₀ hx hlt
        have hz : ‖(x ^ (k + k₀))⁻¹‖ < 1 := by
          rw [norm_inv, inv_lt_one_iff₀]
          right
          rw [norm_pow]
          exact one_lt_pow₀ hx (by omega)
        have hwlim : Tendsto (fun t : ℕ => (x ^ k * (x ^ k₀)⁻¹) ^ (t + 1)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hw1).comp (tendsto_add_atTop_nat 1)
        have hzlim : Tendsto (fun t : ℕ => ((x ^ (k + k₀))⁻¹) ^ (t + 1)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz).comp (tendsto_add_atTop_nat 1)
        have hlim : Tendsto (fun t => c M k
            * ((x ^ k * (x ^ k₀)⁻¹) ^ (t + 1) + ((x ^ (k + k₀))⁻¹) ^ (t + 1)))
            atTop (nhds (c M k * (0 + 0))) :=
          (hwlim.add hzlim).const_mul _
        rw [add_zero, mul_zero] at hlim
        refine Tendsto.congr (fun t => (hpt t).symm) hlim
      ·
        subst heq
        rw [if_pos rfl]
        have hw1 : x ^ k * (x ^ k)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hx0)
        have hz : ‖(x ^ (k + k))⁻¹‖ < 1 := by
          rw [norm_inv, inv_lt_one_iff₀]
          right
          rw [norm_pow]
          exact one_lt_pow₀ hx (by omega)
        have hzlim : Tendsto (fun t : ℕ => ((x ^ (k + k))⁻¹) ^ (t + 1)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz).comp (tendsto_add_atTop_nat 1)
        have hlim : Tendsto (fun t => c M k
            * ((x ^ k * (x ^ k)⁻¹) ^ (t + 1) + ((x ^ (k + k))⁻¹) ^ (t + 1)))
            atTop (nhds (c M k * (1 + 0))) := by
          have h1 : Tendsto (fun t : ℕ => (x ^ k * (x ^ k)⁻¹) ^ (t + 1)) atTop (nhds 1) := by
            simp only [hw1, one_pow]
            exact tendsto_const_nhds
          exact (h1.add hzlim).const_mul _
        rw [add_zero, mul_one] at hlim
        refine Tendsto.congr (fun t => (hpt t).symm) hlim
      ·
        rw [if_neg (by omega)]
        have hzero : c M k = 0 := hbig k hgt hkM
        have hconst : ∀ t, c M k * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀ = 0 := by
          intro t
          rw [hzero]
          simp
        refine Tendsto.congr (fun t => (hconst t).symm) tendsto_const_nhds

    have hsum : Tendsto (fun t => ∑ k ∈ Finset.Icc 1 M,
        c M k * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀)
        atTop (nhds (∑ k ∈ Finset.Icc 1 M, if k = k₀ then c M k₀ else 0)) :=
      tendsto_finsetSum _ hterm
    have hcollapse : (∑ k ∈ Finset.Icc 1 M, if k = k₀ then c M k₀ else 0) = c M k₀ := by
      rw [Finset.sum_ite_eq' (Finset.Icc 1 M) k₀ (fun _ => c M k₀)]
      rw [if_pos (Finset.mem_Icc.mpr ⟨hk₀1, hk₀M⟩)]
    rw [hcollapse] at hsum
    exact Tendsto.congr (fun t => (hfeq t).symm) hsum

  exact tendsto_nhds_unique hflim hf0

lemma spec_row_eq_zero_of_diamond (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B) {M : ℕ}
    (hdiamond : ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k) = specTail c w M) :
    ∀ k, 1 ≤ k → k ≤ M → c M k = 0 := by

  have hcol : ∀ d j : ℕ, 1 ≤ j → j ≤ M → M ≤ j + d → c M j = 0 := by
    intro d
    induction d with
    | zero =>
        intro j h1 h2 hd
        have hjM : j = M := by omega
        subst hjM
        exact spec_eq_zero_of_diamond hB hc h1 le_rfl hdiamond
          (fun k' hk' hk'' => absurd hk'' (by omega))
    | succ d ihd =>
        intro j h1 h2 hd
        rcases (by omega : M ≤ j + d ∨ j + d < M) with h | h
        · exact ihd j h1 h2 h
        · refine spec_eq_zero_of_diamond hB hc h1 h2 hdiamond fun k' hk' hk'' => ?_
          exact ihd k' (by omega) hk'' (by omega)
  intro k h1 h2
  exact hcol M k h1 h2 (by omega)

theorem spec_eq_zero_of_master (hB : 0 ≤ B) (hc : ∀ N k, ‖c N k‖ ≤ B)
    (hmaster : ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha c w M + specTail c w M + specGamma c M) :
    ∀ N k : ℕ, 1 ≤ k → k ≤ N → c N k = 0 := by

  suffices h : ∀ R N k : ℕ, N ≤ R → 1 ≤ k → k ≤ N → c N k = 0 by
    intro N k h1 h2
    exact h N N k le_rfl h1 h2
  intro R
  induction R with
  | zero =>
      intro N k hNR h1 h2
      omega
  | succ R ihR =>
      intro N k hNR h1 h2
      rcases Nat.lt_or_ge N (R + 1) with hN | hN
      · exact ihR N k (by omega) h1 h2

      have hNeq : N = R + 1 := by omega

      have hdiamond : ∀ w : K, 1 < ‖w‖ →
          ∑ j ∈ Finset.Icc 1 N, c N j * (w ^ j + w⁻¹ ^ j) = specTail c w N := by
        intro w hw
        have h1' := hmaster N w hw

        have hα : specAlpha c w N = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have hmem := Finset.mem_filter.mp hp
          have hanti := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem.1
          have hp1 : 1 ≤ p.2 := hmem.2.1
          have hp2 : p.2 ≤ p.1 := hmem.2.2
          have hlow : c p.1 p.2 = 0 := by
            refine ihR p.1 p.2 (by omega) hp1 hp2
          rw [hlow]
          simp
        rw [hα, zero_add] at h1'

        calc ∑ j ∈ Finset.Icc 1 N, c N j * (w ^ j + w⁻¹ ^ j)
            = ∑ j ∈ Finset.Icc 1 N,
                (c N j * (w ^ j + w⁻¹ ^ j - 2) + (2 : K) * c N j) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
          _ = (∑ j ∈ Finset.Icc 1 N, c N j * (w ^ j + w⁻¹ ^ j - 2))
                + ∑ j ∈ Finset.Icc 1 N, (2 : K) * c N j :=
              Finset.sum_add_distrib
          _ = (specTail c w N + specGamma c N)
                + ∑ j ∈ Finset.Icc 1 N, (2 : K) * c N j := by
              rw [h1']
          _ = specTail c w N
                + (∑ j ∈ Finset.Icc 1 N, (-2 : K) * c N j
                    + ∑ j ∈ Finset.Icc 1 N, (2 : K) * c N j) := by
              rw [specGamma, add_assoc]
          _ = specTail c w N := by
              rw [← Finset.sum_add_distrib]
              have hzero : ∑ j ∈ Finset.Icc 1 N, ((-2 : K) * c N j + (2 : K) * c N j) = 0 := by
                refine Finset.sum_eq_zero fun j _ => ?_
                ring
              rw [hzero, add_zero]
      exact spec_row_eq_zero_of_diamond hB hc hdiamond k h1 h2

end BoundedDescent

end TateCurve


