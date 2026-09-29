-- Prove2me | Definitions.Def_TateCurve_XMultAlignment
-- name    : TateCurve_XMultAlignment
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/ded042cf-6d8d-590f-bc8c-c88a1b55a277
-- title:
--   Symmetric addition hypotheses and the Tate-curve x-ladder
-- statement:
--   Over a complete, nontrivially normed ultrametric field $K$ of characteristic zero, with Tate parameter $q$, the module's main definition is the Prop-valued structure `SymAddHyps q`, a bundle of three universally quantified identities for the $x$-coordinate function $u \mapsto$ `pointX q u` of the Tate curve `curve q` (whose $b$-invariants are $b_2 = 1$, $b_4 = 2a_4(q)$, $b_6 = 4a_6(q)$). The field `sum` asserts, for all $u,v$ satisfying `AddParams q u v` (that is, $q,u,v \ne 0$ and each of $u$, $v$, $uv$, $uv^{-1}$ off the lattice, $q^n w \ne 1$ for all $n \in \mathbb{Z}$), that $(X(uv)+X(uv^{-1}))(X(u)-X(v))^2$ equals `symSumNum q (X u) (X v)` $= 2x_1x_2(x_1+x_2)+x_1x_2+2a_4(q)(x_1+x_2)+4a_6(q)$; the field `prod` asserts the companion identity for the product $X(uv)X(uv^{-1})(X(u)-X(v))^2$ with `symProdNum`; the field `dbl` asserts, for $u \ne 0$ with $u$ and $u^2$ off the lattice, the cleared duplication formula $X(u^2)\,\Psi_2^{\mathrm{Sq}}(X(u)) = \Phi_2(X(u))$.
--
--   Alongside this the module records: primed restatements, for a Weierstrass curve $W$ over a field via its affine model, of the identity for $\mathrm{addX}$ times $(x_1-x_2)^2$ and of the sum of the two $\mathrm{addX}$ values obtained from $y_2$ and $-y_2 - a_1x_2 - a_3$; that $(X(u),Y(u))$ satisfies the affine Weierstrass equation of `curve q` and is nonsingular when $0 \ne \|q\|_+ < 1$ and $u$ is off the lattice; a Bézout argument showing $u^j$ is off the lattice for $0 < j < p$ when $u^p = q^s$ and $p$ is prime; the ladder theorem that, granting `SymAddHyps q` and $m \cdot P \ne 0$ for $2 \le m \le N$, the multiples $j \cdot P$ of $P = (X(u),Y(u))$ are affine with $x$-coordinate $X(u^j)$ for $1 \le j \le N$; and, for odd prime $p$ with $u^p = q^s$, that either $p \cdot P = 0$ or $m \cdot P = 0$ for some $2 \le m \le p-1$.
--
--   **Relation to Mathlib.** `addX`, `slope`, `negY`, `Ψ₂Sq`, `Φ`, the point group and `Point.xOrZero` are Mathlib's; the Tate-curve data (`curve`, `pointX`, `pointY`, `OffLattice`, `AddParams`, `symSumNum`, `symProdNum`) and the hypothesis bundle `SymAddHyps` are the project's own. The two primed lemmas repeat, for `W : WeierstrassCurve F` through `W.toAffine`, statements the project also records for an affine curve.
--
--   **Where it is used.** These identities and the ladder are used to show that the Tate-curve point attached to a parameter $u$ with $u^p \in q^{\mathbb{Z}}$ is a $p$-torsion point, towards an explicit description of the $p$-torsion of a Tate curve and thence the local analysis at $p$ in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TateCurve_XMultAlignment.lean

import Mathlib
import Definitions.Def_TateCurve_XMultStructure
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_WeierstrassCurve_AddFormula
import Definitions.Def_NetPairing_Basic
import Theorems.Thm_TateCurve_equation_pointX_pointY
import Theorems.Thm_TateCurve_pointX_inv
import Theorems.Thm_TateCurve_pointX_zpow_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : WeierstrassCurve F}

lemma addX_mul_sq_of_X_ne' [DecidableEq F] {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) ^ 2 =
      (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) - (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  rw [slope_of_X_ne hx, addX]
  field_simp
  ring

theorem addX_add_addX_negY_mul_sq' [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) +
        W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) *
        (x₁ - x₂) ^ 2 =
      2 * (x₁ * x₂) * (x₁ + x₂) + W.b₂ * (x₁ * x₂) + W.b₄ * (x₁ + x₂) + W.b₆ := by
  have e₁ := addX_mul_sq_of_X_ne' (W := W) y₁ y₂ hx
  have e₂ := addX_mul_sq_of_X_ne' (W := W) y₁ (W.toAffine.negY x₂ y₂) hx
  rw [W.toAffine.equation_iff x₁ y₁] at h₁
  rw [W.toAffine.equation_iff x₂ y₂] at h₂
  rw [add_mul, e₁, e₂, negY, b₂, b₄, b₆]
  linear_combination 2 * h₁ + 2 * h₂

end WeierstrassCurve.Affine

set_option linter.unusedSectionVars false

open WeierstrassCurve.Affine
open Polynomial

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u : K}

structure SymAddHyps (q : K) : Prop where

  sum : ∀ u v : K, AddParams q u v →
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v)

  prod : ∀ u v : K, AddParams q u v →
    pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
      symProdNum q (pointX q u) (pointX q v)

  dbl : ∀ u : K, u ≠ 0 → OffLattice q u → OffLattice q (u ^ 2) →
    pointX q (u ^ 2) * ((curve q).Ψ₂Sq).eval (pointX q u) =
      ((curve q).Φ 2).eval (pointX q u)

section TatePoint

lemma equation_point (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : OffLattice q u) :
    (curve q).toAffine.Equation (pointX q u) (pointY q u) := by
  have h := equation_pointX_pointY hq0 hq hu0 hu
  rw [WeierstrassCurve.Affine.equation_iff]
  show pointY q u ^ 2 + (curve q).a₁ * pointX q u * pointY q u + (curve q).a₃ * pointY q u =
      pointX q u ^ 3 + (curve q).a₂ * pointX q u ^ 2 + (curve q).a₄ * pointX q u + (curve q).a₆
  rw [curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆]
  linear_combination h

lemma nonsingular_point (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : OffLattice q u) :
    (curve q).toAffine.Nonsingular (pointX q u) (pointY q u) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (Δ_ne_zero hq0 hq)).mp (equation_point hq0 hq hu0 hu)

end TatePoint

section PowerBookkeeping

private lemma pow_succ_mul_inv (hu0 : u ≠ 0) (k : ℕ) : u ^ (k + 1) * u⁻¹ = u ^ k := by
  rw [pow_succ, mul_assoc, mul_inv_cancel₀ hu0, mul_one]

private lemma addParams_pow (hq0 : q ≠ 0) (hu0 : u ≠ 0) {N k : ℕ} (hk : k + 3 ≤ N)
    (hoff : ∀ j : ℕ, 1 ≤ j → j ≤ N → OffLattice q (u ^ j)) :
    AddParams q (u ^ (k + 2)) u := by
  have h1 : OffLattice q u := by
    have h := hoff 1 le_rfl (by omega); rwa [pow_one] at h
  have hmul : OffLattice q (u ^ (k + 2) * u) := by
    have h := hoff (k + 2 + 1) (by omega) (by omega)
    rwa [pow_succ] at h
  have hdiv : OffLattice q (u ^ (k + 2) * u⁻¹) := by
    have h := hoff (k + 1) (by omega) (by omega)
    have heq : u ^ (k + 2) * u⁻¹ = u ^ (k + 1) := pow_succ_mul_inv hu0 (k + 1)
    rwa [heq]
  exact ⟨hq0, pow_ne_zero _ hu0, hu0, hoff (k + 2) (by omega) (by omega), h1, hmul, hdiv⟩

lemma offLattice_pow_of_prime {p j : ℕ} {s : ℤ} (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hu : OffLattice q u) (hpow : u ^ p = q ^ s) (hp : p.Prime)
    (hj0 : 0 < j) (hjp : j < p) : OffLattice q (u ^ j) := by
  intro n hn

  have hju : u ^ ((j : ℕ) : ℤ) = q ^ (-n) := by
    rw [zpow_natCast]
    have h1 : q ^ (-n) * (q ^ n * u ^ j) = q ^ (-n) * 1 := by rw [hn]
    rwa [← mul_assoc, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, one_mul, mul_one] at h1
  have hpz : u ^ ((p : ℕ) : ℤ) = q ^ s := by rw [zpow_natCast]; exact hpow

  have hcop : Nat.Coprime p j := (Nat.Prime.coprime_iff_not_dvd hp).mpr
    (fun hdvd => absurd (Nat.le_of_dvd hj0 hdvd) (by omega))
  have hbez : (1 : ℤ) = (p : ℤ) * Nat.gcdA p j + (j : ℤ) * Nat.gcdB p j := by
    have h := Nat.gcd_eq_gcd_ab p j
    rwa [hcop.gcd_eq_one, Nat.cast_one] at h

  have hkey : u = q ^ (s * Nat.gcdA p j + (-n) * Nat.gcdB p j) := by
    have h1 : u = (u ^ ((p : ℕ) : ℤ)) ^ Nat.gcdA p j * (u ^ ((j : ℕ) : ℤ)) ^ Nat.gcdB p j := by
      rw [← zpow_mul, ← zpow_mul, ← zpow_add₀ hu0, ← hbez, zpow_one]
    rw [h1, hpz, hju, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hq0]

  exact hu (-(s * Nat.gcdA p j + (-n) * Nat.gcdB p j))
    (by rw [hkey, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero])

end PowerBookkeeping

section Ladder

theorem xOrZero_nsmul_of_forall_ne_zero
    (hyps : SymAddHyps q) (hq0 : q ≠ 0) (hu0 : u ≠ 0) {N : ℕ}
    (hoff : ∀ j : ℕ, 1 ≤ j → j ≤ N → OffLattice q (u ^ j))
    (hns : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u))
    (htor : ∀ m : ℕ, 2 ≤ m → m ≤ N →
      m • (Point.some (pointX q u) (pointY q u) hns : (curve q).toAffine.Point) ≠ 0) :
    ∀ j : ℕ, 1 ≤ j → j ≤ N →
      j • (Point.some (pointX q u) (pointY q u) hns : (curve q).toAffine.Point) ≠ 0 ∧
      (j • (Point.some (pointX q u) (pointY q u) hns :
        (curve q).toAffine.Point)).xOrZero = pointX q (u ^ j) := by
  set P : (curve q).toAffine.Point := Point.some (pointX q u) (pointY q u) hns with hP
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hjN
    rcases lt_or_ge j 3 with hj3 | hj3
    ·
      interval_cases j
      ·
        refine ⟨by rw [one_nsmul, hP]; exact Point.some_ne_zero hns, ?_⟩
        rw [one_nsmul, hP, Point.xOrZero_some, pow_one]
      ·
        have hoff1 : OffLattice q u := by
          have h := hoff 1 le_rfl (by omega); rwa [pow_one] at h
        have hoff2 : OffLattice q (u ^ 2) := hoff 2 (by omega) hjN
        by_cases hy : pointY q u = (curve q).toAffine.negY (pointX q u) (pointY q u)
        ·
          exact absurd (by rw [two_nsmul, hP]; exact Point.add_self_of_Y_eq hy)
            (htor 2 le_rfl hjN)
        ·
          have hT : ((curve q).toAffine.Ψ₂Sq).eval (pointX q u) ≠ 0 := by
            have hsq := WeierstrassCurve.Affine.sq_sub_negY_eq_eval_Ψ₂Sq
              (W := (curve q).toAffine) hns.left
            rw [← hsq]
            exact pow_ne_zero 2 (sub_ne_zero.mpr hy)
          have hcurve := WeierstrassCurve.Affine.addX_self_mul_Ψ₂Sq
            (W := (curve q).toAffine) hns.left hy
          have hser : pointX q (u ^ 2) * ((curve q).toAffine.Ψ₂Sq).eval (pointX q u) =
              (((curve q).toAffine.Φ 2)).eval (pointX q u) :=
            hyps.dbl u hu0 hoff1 hoff2
          have hx2 : (curve q).toAffine.addX (pointX q u) (pointX q u)
              ((curve q).toAffine.slope (pointX q u) (pointX q u) (pointY q u) (pointY q u)) =
              pointX q (u ^ 2) :=
            mul_right_cancel₀ hT (hcurve.trans hser.symm)
          refine ⟨?_, ?_⟩
          · rw [two_nsmul, hP, Point.add_self_of_Y_ne hy]
            exact Point.some_ne_zero _
          · rw [two_nsmul, hP, Point.add_self_of_Y_ne hy, Point.xOrZero_some]
            exact hx2
    ·
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩

      obtain ⟨hQne, hQx⟩ := ih (k + 2) (by omega) (by omega) (by omega)
      obtain ⟨hRne, hRx⟩ := ih (k + 1) (by omega) (by omega) (by omega)

      obtain ⟨xj, yj, hj, hQeq⟩ : ∃ (xj yj : K)
          (hj : (curve q).toAffine.Nonsingular xj yj), (k + 2) • P = Point.some xj yj hj := by
        cases hQP : (k + 2) • P with
        | zero => exact absurd hQP hQne
        | @some a b hc => exact ⟨a, b, hc, rfl⟩
      have hxj : xj = pointX q (u ^ (k + 2)) := by
        rw [hQeq, Point.xOrZero_some] at hQx
        exact hQx
      by_cases hxx : xj = pointX q u
      ·
        exfalso
        rcases Y_eq_of_X_eq hj.left hns.left hxx with hyy | hyy
        ·
          have hQP : (k + 2) • P = P := by
            rw [hQeq, hP]
            subst hxx; subst hyy
            rw [Subsingleton.elim hj hns]
          have hsucc : (k + 2) • P = (k + 1) • P + P := succ_nsmul P (k + 1)
          have h0 : (k + 1) • P + P = 0 + P := by
            rw [zero_add, ← hsucc, hQP]
          exact hRne (add_right_cancel h0)
        ·
          have hQP : (k + 2) • P = -P := by
            rw [hQeq, hP, Point.neg_some]
            subst hxx; subst hyy
            exact congrArg _ (Subsingleton.elim _ _)
          have hk3 : (k + 3) • P = 0 := by
            have hsucc : (k + 3) • P = (k + 2) • P + P := succ_nsmul P (k + 2)
            rw [hsucc, hQP, neg_add_cancel]
          exact htor (k + 3) (by omega) hjN hk3
      ·

        have hap : AddParams q (u ^ (k + 2)) u := addParams_pow hq0 hu0 hjN hoff
        have hS1 := hyps.sum (u ^ (k + 2)) u hap
        rw [show u ^ (k + 2) * u = u ^ (k + 2 + 1) from (pow_succ u (k + 2)).symm,
          show u ^ (k + 2) * u⁻¹ = u ^ (k + 1) from pow_succ_mul_inv hu0 (k + 1),
          symSumNum_eq_b, ← hxj] at hS1

        have hsum := WeierstrassCurve.Affine.addX_add_addX_negY_mul_sq'
          (W := curve q) hj.left hns.left hxx

        have hAm : (curve q).toAffine.addX xj (pointX q u)
            ((curve q).toAffine.slope xj (pointX q u) yj
              ((curve q).toAffine.negY (pointX q u) (pointY q u))) = pointX q (u ^ (k + 1)) := by
          have h1 := hRx
          have hsucc2 : (k + 2) • P = (k + 1) • P + P := succ_nsmul P (k + 1)
          have hrearr : (k + 1) • P = (k + 2) • P + -P := by
            rw [hsucc2, add_neg_cancel_right]
          rw [hrearr, hQeq, hP, Point.neg_some, Point.add_of_X_ne hxx,
            Point.xOrZero_some] at h1
          exact h1

        have hD2 : (xj - pointX q u) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hxx)
        have hcomb := mul_right_cancel₀ hD2 (hsum.trans hS1.symm)
        rw [hAm] at hcomb
        have hfinal : (curve q).toAffine.addX xj (pointX q u)
            ((curve q).toAffine.slope xj (pointX q u) yj (pointY q u)) =
            pointX q (u ^ (k + 2 + 1)) := add_right_cancel hcomb

        have hsucc : (k + 3) • P = (k + 2) • P + P := succ_nsmul P (k + 2)
        refine ⟨?_, ?_⟩
        · rw [hsucc, hQeq, hP, Point.add_of_X_ne hxx]
          exact Point.some_ne_zero _
        · rw [hsucc, hQeq, hP, Point.add_of_X_ne hxx, Point.xOrZero_some]
          exact hfinal

end Ladder

section Endgame

lemma pointX_pow_pred_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hu : OffLattice q u)
    {p : ℕ} (hp1 : 1 ≤ p) {s : ℤ} (hpow : u ^ p = q ^ s) :
    pointX q (u ^ (p - 1)) = pointX q u := by
  have h1 : u ^ p = u ^ (p - 1) * u := by
    conv_lhs => rw [show p = (p - 1) + 1 by omega]
    rw [pow_succ]
  have h2 : u ^ (p - 1) = q ^ s * u⁻¹ := by
    rw [← hpow, h1, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
  rw [h2, pointX_zpow_mul hq0, pointX_inv hq0 hu0 hu]

theorem nsmul_prime_eq_zero_of_forall_ne_zero
    {p : ℕ} (hyps : SymAddHyps q) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hu : OffLattice q u) {s : ℤ} (hpow : u ^ p = q ^ s) (hp : p.Prime) (hodd : Odd p)
    (hns : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u))
    (htor : ∀ m : ℕ, 2 ≤ m → m ≤ p - 1 →
      m • (Point.some (pointX q u) (pointY q u) hns : (curve q).toAffine.Point) ≠ 0) :
    p • (Point.some (pointX q u) (pointY q u) hns : (curve q).toAffine.Point) = 0 := by
  set P : (curve q).toAffine.Point := Point.some (pointX q u) (pointY q u) hns with hP
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases hodd with ⟨t, ht⟩
    omega

  have hoff : ∀ j : ℕ, 1 ≤ j → j ≤ p - 1 → OffLattice q (u ^ j) := fun j hj1 hj2 =>
    offLattice_pow_of_prime hq0 hu0 hu hpow hp (by omega) (by omega)

  have halign := xOrZero_nsmul_of_forall_ne_zero hyps hq0 hu0 hoff hns htor
  obtain ⟨hne, hx⟩ := halign (p - 1) (by omega) le_rfl

  have hXp : pointX q (u ^ (p - 1)) = pointX q u :=
    pointX_pow_pred_eq hq0 hu0 hu (by omega) hpow

  obtain ⟨x', y', h', hQeq⟩ : ∃ (x' y' : K)
      (h' : (curve q).toAffine.Nonsingular x' y'), (p - 1) • P = Point.some x' y' h' := by
    cases hQP : (p - 1) • P with
    | zero => exact absurd hQP hne
    | @some a b hc => exact ⟨a, b, hc, rfl⟩
  have hx' : x' = pointX q u := by
    rw [hQeq, Point.xOrZero_some] at hx
    rw [hx, hXp]

  rcases Y_eq_of_X_eq h'.left hns.left hx' with hyy | hyy
  · exfalso
    have hQP : (p - 1) • P = P := by
      rw [hQeq, hP]
      subst hx'; subst hyy
      rw [Subsingleton.elim h' hns]
    obtain ⟨hne2, _⟩ := halign (p - 2) (by omega) (by omega)
    have h0 : (p - 2) • P + P = 0 + P := by
      rw [zero_add, ← succ_nsmul, show p - 2 + 1 = p - 1 by omega, hQP]
    exact hne2 (add_right_cancel h0)
  · have hQP : (p - 1) • P = -P := by
      rw [hQeq, hP, Point.neg_some]
      subst hx'; subst hyy
      exact congrArg _ (Subsingleton.elim _ _)
    have hsucc : p • P = (p - 1) • P + P := by
      conv_lhs => rw [show p = (p - 1) + 1 by omega]
      exact succ_nsmul P (p - 1)
    rw [hsucc, hQP, neg_add_cancel]

theorem nsmul_prime_eq_zero_or_exists_nsmul_eq_zero
    {p : ℕ} (hyps : SymAddHyps q) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hu : OffLattice q u) {s : ℤ} (hpow : u ^ p = q ^ s) (hp : p.Prime) (hodd : Odd p)
    (hns : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u)) :
    p • (Point.some (pointX q u) (pointY q u) hns : (curve q).toAffine.Point) = 0 ∨
      ∃ m : ℕ, 2 ≤ m ∧ m ≤ p - 1 ∧
        m • (Point.some (pointX q u) (pointY q u) hns : (curve q).toAffine.Point) = 0 := by
  by_cases h : ∃ m : ℕ, 2 ≤ m ∧ m ≤ p - 1 ∧
      m • (Point.some (pointX q u) (pointY q u) hns : (curve q).toAffine.Point) = 0
  · exact Or.inr h
  · refine Or.inl (nsmul_prime_eq_zero_of_forall_ne_zero hyps hq0 hu0 hu hpow hp hodd hns
      (fun m hm1 hm2 hm0 => h ⟨m, hm1, hm2, hm0⟩))

end Endgame

end TateCurve


