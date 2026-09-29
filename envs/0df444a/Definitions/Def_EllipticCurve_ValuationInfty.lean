-- Prove2me | Definitions.Def_EllipticCurve_ValuationInfty
-- name    : EllipticCurve_ValuationInfty
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/0eb68ae7-0a9b-5c31-8c00-8fe866c501ab
-- title:
--   The valuation at infinity on an affine Weierstrass curve
-- statement:
--   Throughout, $K$ is a field and $W$ an affine Weierstrass curve over $K$, with coordinate ring $K[W] = K[X][Y]/(Y^2 + a_1XY + a_3Y - X^3 - a_2X^2 - a_4X - a_6)$, a free $K[X]$-module of rank two on the basis $\{1, y\}$, and function field $K(W)$ the localisation of $K[W]$ at its non-zero-divisors. The construction proceeds through the algebra norm $N = \mathrm{Algebra.norm}\ K[X]$ of this rank-two extension. First, `valuationInftyDef` sends $0$ to $0$ and a non-zero $f \in K[W]$ to $\exp(\deg N(f)) \in \mathbb{Z}^{m0} = \mathrm{WithZero}(\mathrm{Multiplicative}\ \mathbb{Z})$, where the degree is the natural-number degree of the norm; `valuationInftyInt` packages this as a `Valuation` on $K[W]$, multiplicativity coming from multiplicativity of the norm and additivity of degrees, and the ultrametric inequality from `degree_norm_add_le`, which bounds $\deg N(f+g)$ by the maximum of $\deg N(f)$ and $\deg N(g)$ using the Mathlib formula $\deg N(p\cdot 1 + q\cdot y) = \max(2\deg p,\, 2\deg q + 3)$. Since the norm of a non-zero element is non-zero, the support of this valuation meets the non-zero-divisors trivially, so it extends along the localisation map to `valuationInfty`, a valuation on $K(W)$ with values in $\mathbb{Z}^{m0}$. Note the multiplicative normalisation: the value grows with the order of the pole at the point at infinity, so $\exp$ of a positive integer is a large value.
--
--   Auxiliary lemmas compute the relevant norm degrees: $\deg N(p\cdot 1 + q\cdot y)$ in the cases $q = 0$ and $q \neq 0$, hence $\deg N(p(x)) = 2\deg p$ and $\deg N(y) = 3$; also $y \neq 0$ in $K[W]$ and the relation $y\,(y + a_1x + a_3) = x^3 + a_2x^2 + a_4x + a_6$. Consequently `valuationInfty` takes the value $\exp 2$ at $x$ and $\exp 3$ at $y$. The valuation is surjective onto $\mathbb{Z}^{m0}$, witnessed by the powers of $y/x$, and therefore nontrivial; its valuation subring is a discrete valuation ring.
--
--   **Relation to Mathlib.** Mathlib supplies the affine coordinate ring, its $K[X]$-basis $\{1, y\}$, the degree formula for norms of elements written in that basis, the function field, and the extension of a valuation to a localisation; the valuation at infinity itself is built here from these ingredients.
--
--   **Where it is used.** The valuation at infinity gives the local behaviour of functions on a Weierstrass curve at $\mathcal{O} = [0:1:0]$, with $x$ and $y$ having poles of order $2$ and $3$; it is used in the function-field and divisor-theoretic arguments about elliptic curves in the modules that import it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_EllipticCurve_ValuationInfty.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Norm.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Polynomial.Bivariate WithZero nonZeroDivisors
open Polynomial

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)

namespace CoordinateRing

lemma algebraNorm_ne_zero {f : W.CoordinateRing} (hf : f ≠ 0) : Algebra.norm K[X] f ≠ 0 :=
  (Algebra.norm_ne_zero_iff_of_basis (CoordinateRing.basis W)).mpr hf

open scoped Classical in

noncomputable def valuationInftyDef (f : W.CoordinateRing) : ℤᵐ⁰ :=
  if f = 0 then 0 else WithZero.exp ((Algebra.norm K[X] f).natDegree : ℤ)

lemma degree_norm_add_le (f g : W.CoordinateRing) :
    (Algebra.norm K[X] (f + g)).degree ≤
      max (Algebra.norm K[X] f).degree (Algebra.norm K[X] g).degree := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  obtain ⟨p', q', rfl⟩ := exists_smul_basis_eq g
  have : p • (1 : W.CoordinateRing) + q • mk W Y + (p' • 1 + q' • mk W Y) =
      (p + p') • 1 + (q + q') • mk W Y := by
    rw [add_smul, add_smul]; abel
  rw [this, degree_norm_smul_basis, degree_norm_smul_basis, degree_norm_smul_basis]
  refine max_le ?_ ?_
  · rcases le_max_iff.mp (degree_add_le p p') with h | h
    · exact le_max_of_le_left (le_max_of_le_left (nsmul_le_nsmul_right h 2))
    · exact le_max_of_le_right (le_max_of_le_left (nsmul_le_nsmul_right h 2))
  · rcases le_max_iff.mp (degree_add_le q q') with h | h
    · exact le_max_of_le_left (le_max_of_le_right
        (add_le_add_left (nsmul_le_nsmul_right h 2) 3))
    · exact le_max_of_le_right (le_max_of_le_right
        (add_le_add_left (nsmul_le_nsmul_right h 2) 3))

noncomputable def valuationInftyInt : Valuation W.CoordinateRing ℤᵐ⁰ where
  toFun := valuationInftyDef W
  map_zero' := if_pos rfl
  map_one' := by
    simp [valuationInftyDef]
  map_mul' f g := by
    classical
    by_cases hf : f = 0
    · simp [valuationInftyDef, hf]
    by_cases hg : g = 0
    · simp [valuationInftyDef, hg]
    simp only [valuationInftyDef, if_neg hf, if_neg hg, if_neg (mul_ne_zero hf hg), map_mul,
      natDegree_mul (algebraNorm_ne_zero W hf) (algebraNorm_ne_zero W hg), Nat.cast_add, WithZero.exp_add]
  map_add_le_max' f g := by
    classical
    by_cases hfg : f + g = 0
    · simp [valuationInftyDef, hfg]
    by_cases hf : f = 0
    · simp [valuationInftyDef, hf]
    by_cases hg : g = 0
    · simp [valuationInftyDef, hg]
    simp only [valuationInftyDef, if_neg hf, if_neg hg, if_neg hfg, le_max_iff,
      WithZero.exp_le_exp, Nat.cast_le]
    have h := degree_norm_add_le W f g
    rw [degree_eq_natDegree (algebraNorm_ne_zero W hfg), degree_eq_natDegree (algebraNorm_ne_zero W hf),
      degree_eq_natDegree (algebraNorm_ne_zero W hg)] at h
    rcases le_max_iff.mp h with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)

lemma valuationInftyInt_apply (f : W.CoordinateRing) :
    valuationInftyInt W f = valuationInftyDef W f := rfl

lemma nonZeroDivisors_le_supp_primeCompl :
    W.CoordinateRing⁰ ≤ (valuationInftyInt W).supp.primeCompl := fun _ hs => by
  simp [valuationInftyInt_apply, valuationInftyDef, nonZeroDivisors.ne_zero hs]

end CoordinateRing

noncomputable def valuationInfty : Valuation W.FunctionField ℤᵐ⁰ :=
  (CoordinateRing.valuationInftyInt W).extendToLocalization
    (CoordinateRing.nonZeroDivisors_le_supp_primeCompl W) W.FunctionField

lemma valuationInfty_algebraMap (f : W.CoordinateRing) :
    valuationInfty W (algebraMap W.CoordinateRing W.FunctionField f) =
      CoordinateRing.valuationInftyDef W f :=
  Valuation.extendToLocalization_apply_map_apply ..

lemma valuationInfty_algebraMap_of_ne_zero {f : W.CoordinateRing} (hf : f ≠ 0) :
    valuationInfty W (algebraMap W.CoordinateRing W.FunctionField f) =
      WithZero.exp ((Algebra.norm K[X] f).natDegree : ℤ) := by
  rw [valuationInfty_algebraMap, CoordinateRing.valuationInftyDef, if_neg hf]

namespace CoordinateRing

lemma natDegree_norm_smul_basis_of_eq_zero (p : K[X]) :
    (Algebra.norm K[X] (p • (1 : W.CoordinateRing) + (0 : K[X]) • mk W Y)).natDegree =
      2 * p.natDegree := by
  by_cases hp : p = 0
  · subst hp
    have : (0 : K[X]) • (1 : W.CoordinateRing) + (0 : K[X]) • mk W Y = 0 := by simp
    rw [this, (Algebra.norm_eq_zero_iff_of_basis (CoordinateRing.basis W)).mpr rfl,
      natDegree_zero]
  · have h := degree_norm_smul_basis (W' := W) p 0
    rw [degree_zero, degree_eq_natDegree hp, two_nsmul, two_nsmul, WithBot.bot_add,
      WithBot.bot_add, max_bot_right] at h
    apply natDegree_eq_of_degree_eq_some
    rw [h, two_mul]
    rfl

lemma natDegree_norm_smul_basis_of_ne_zero (p q : K[X]) (hq : q ≠ 0) :
    (Algebra.norm K[X] (p • (1 : W.CoordinateRing) + q • mk W Y)).natDegree =
      max (2 * p.natDegree) (2 * q.natDegree + 3) := by
  have h := degree_norm_smul_basis (W' := W) p q
  apply natDegree_eq_of_degree_eq_some
  rw [h, degree_eq_natDegree hq]
  by_cases hp : p = 0
  · subst hp
    rw [degree_zero, two_nsmul, WithBot.bot_add, max_bot_left, natDegree_zero, mul_zero,
      Nat.zero_max, two_nsmul, two_mul]
    rfl
  · rw [degree_eq_natDegree hp, two_nsmul, two_nsmul, two_mul, two_mul]
    rfl

lemma natDegree_norm_mk_C (p : K[X]) :
    (Algebra.norm K[X] (mk W (C p))).natDegree = 2 * p.natDegree := by
  rw [← natDegree_norm_smul_basis_of_eq_zero W p, CoordinateRing.smul, zero_smul, add_zero,
    mul_one]

lemma natDegree_norm_mk_Y : (Algebra.norm K[X] (mk W Y)).natDegree = 3 := by
  have := natDegree_norm_smul_basis_of_ne_zero W 0 1 one_ne_zero
  rw [zero_smul, one_smul, zero_add] at this
  rw [this]
  norm_num

lemma mk_Y_ne_zero : mk W Y ≠ 0 := by
  simpa [YClass] using YClass_ne_zero (W' := W) 0

lemma mk_Y_mul_mk_Y_add :
    mk W Y * (mk W Y + mk W (C (C W.a₁ * X + C W.a₃))) =
      mk W (C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) := by
  have h : mk W (Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y) =
      mk W (C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) :=
    AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [WeierstrassCurve.Affine.polynomial]; ring1⟩
  rw [map_add, map_mul, map_pow] at h
  rw [← h]
  ring

end CoordinateRing

lemma valuationInfty_X :
    valuationInfty W (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X))) =
      WithZero.exp 2 := by
  rw [valuationInfty_algebraMap_of_ne_zero W (CoordinateRing.XClass_ne_zero (W' := W) 0 ∘ ?_),
    CoordinateRing.natDegree_norm_mk_C, natDegree_X]
  · rfl
  · intro h; simpa [CoordinateRing.XClass] using h

lemma valuationInfty_Y :
    valuationInfty W (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) =
      WithZero.exp 3 := by
  rw [valuationInfty_algebraMap_of_ne_zero W (CoordinateRing.mk_Y_ne_zero W),
    CoordinateRing.natDegree_norm_mk_Y]
  rfl

lemma valuationInfty_surjective : Function.Surjective (valuationInfty W) := by
  intro γ
  rcases eq_or_ne γ 0 with rfl | hγ
  · exact ⟨0, map_zero _⟩
  · refine ⟨(algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) /
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X))) ^ WithZero.log γ, ?_⟩
    rw [map_zpow₀, map_div₀, valuationInfty_Y, valuationInfty_X, ← WithZero.exp_sub,
      ← WithZero.exp_zsmul, smul_eq_mul]
    norm_num
    exact WithZero.exp_log hγ

instance valuationInfty_isNontrivial : (valuationInfty W).IsNontrivial :=
  ⟨algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X)), by
    rw [valuationInfty_X]; exact ⟨WithZero.exp_ne_zero, by decide⟩⟩

instance : IsDiscreteValuationRing (valuationInfty W).valuationSubring := inferInstance

end WeierstrassCurve.Affine


