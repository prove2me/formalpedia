-- Prove2me | Definitions.Def_WeierstrassCurve_KohelQuotient
-- name    : WeierstrassCurve_KohelQuotient
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/9d72160f-00fd-5d27-b384-7c916429a55e
-- title:
--   Kohel's Vélu quotient of a Weierstrass curve by a kernel polynomial
-- statement:
--   Over a commutative ring $R$, the module first attaches to a polynomial $h \in R[X]$ the coefficient-level Vieta data: [`Polynomial.rootESymm h k`](../def/WeierstrassCurve_KohelQuotient.html#L12) is $(-1)^k$ times the coefficient of $X^{n-k}$ in $h$, where $n = \deg h$, when $k \le n$, and $0$ when $k > n$; for monic $h$ this is the $k$-th elementary symmetric function $s_k$ of the roots of $h$, defined without reference to any roots. From these, `rootPowerSumOne`, `rootPowerSumTwo` and `rootPowerSumThree` are the Newton expressions $p_1 = s_1$, $p_2 = s_1^2 - 2s_2$, $p_3 = s_1^3 - 3 s_1 s_2 + 3 s_3$ in the $s_k =$ `rootESymm h k`. The accompanying lemmas record $s_0 =$ the leading coefficient, vanishing of $s_k$ for $k > \deg h$, the value for $h = 1$, and compatibility with a ring homomorphism $f : R \to S$, either when $f$ does not kill the leading coefficient or, for the three power sums, when $h$ is monic.
--
--   For a Weierstrass curve $W$ over $R$ with the usual $b_2, b_4, b_6$, the Kohel totals are
--   $$t = W.\mathtt{kohelT}\,h = 6p_2 + b_2 p_1 + n\,b_4, \qquad w = W.\mathtt{kohelW}\,h = 10 p_3 + 2 b_2 p_2 + 3 b_4 p_1 + n\,b_6,$$
--   with $n = \deg h$ taken as a natural-number cast into $R$, and `W.kohelQuotient h` is the Vélu quotient at these totals, i.e. the Weierstrass curve with the same $a_1, a_2, a_3$ and with $a_4 - 5t$, $a_6 - b_2 t - 7 w$ in place of $a_4, a_6$. Thus the construction is a purely coefficient-theoretic operation on Weierstrass presentations, available for every commutative ring and every polynomial, with no hypothesis relating $h$ to a subgroup. The remaining results give the coefficients of the quotient, the invariance of $b_2$, the fact that $h = 1$ gives $t = w = 0$ and returns $W$ itself, the commutation of $t$, $w$ and the quotient with base change along $f$ for monic $h$, and, for a homomorphism of fields $f : K \to L$ and monic $h$ with both quotients elliptic, the equality of $j$-invariants $j((W \otimes_f L).\mathtt{kohelQuotient}(f_* h)) = f(j(W.\mathtt{kohelQuotient}\,h))$.
--
--   **Relation to Mathlib.** Mathlib supplies `WeierstrassCurve`, the quantities $b_2, b_4, b_6$, base change `map`, `IsElliptic` and the $j$-invariant with its base-change lemma; the Vélu and Kohel quotient constructions, and the coefficient-level symmetric functions `rootESymm` and the associated power sums, are the project's own.
--
--   **Where it is used.** The construction produces, from a kernel polynomial, an explicit Weierstrass model of the quotient curve which is defined over an arbitrary commutative ring and commutes with base change and reduction; it is this integral, presentation-level form of Vélu's formulas that is used where isogenous curves and their reductions must be compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_KohelQuotient.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluQuotientOfSums

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

def rootESymm (h : R[X]) (k : ℕ) : R :=
  if k ≤ h.natDegree then (-1) ^ k * h.coeff (h.natDegree - k) else 0

def rootPowerSumOne (h : R[X]) : R := h.rootESymm 1

def rootPowerSumTwo (h : R[X]) : R := h.rootESymm 1 ^ 2 - 2 * h.rootESymm 2

def rootPowerSumThree (h : R[X]) : R :=
  h.rootESymm 1 ^ 3 - 3 * h.rootESymm 1 * h.rootESymm 2 + 3 * h.rootESymm 3

@[simp] theorem rootESymm_zero_right (h : R[X]) : h.rootESymm 0 = h.leadingCoeff := by
  simp only [rootESymm, zero_le, if_true, pow_zero, one_mul, Nat.sub_zero]
  rfl

theorem rootESymm_of_lt {h : R[X]} {k : ℕ} (hk : h.natDegree < k) : h.rootESymm k = 0 := by
  simp [rootESymm, not_le.mpr hk]

theorem rootESymm_of_le {h : R[X]} {k : ℕ} (hk : k ≤ h.natDegree) :
    h.rootESymm k = (-1) ^ k * h.coeff (h.natDegree - k) := by
  simp [rootESymm, hk]

@[simp] theorem rootESymm_one (k : ℕ) : (1 : R[X]).rootESymm k = if k = 0 then 1 else 0 := by
  rcases k with _ | k
  · simp
  · simp [rootESymm]

section map

variable {S : Type*} [CommRing S] (f : R →+* S)

theorem rootESymm_map {h : R[X]} (hh : f h.leadingCoeff ≠ 0) (k : ℕ) :
    (h.map f).rootESymm k = f (h.rootESymm k) := by
  simp only [rootESymm, natDegree_map_of_leadingCoeff_ne_zero f hh, coeff_map]
  split_ifs <;> simp

theorem rootESymm_map_of_monic {h : R[X]} (hh : h.Monic) (k : ℕ) :
    (h.map f).rootESymm k = f (h.rootESymm k) := by
  nontriviality S
  exact rootESymm_map f (by rw [hh.leadingCoeff, map_one]; exact one_ne_zero) k

theorem rootPowerSumOne_map_of_monic {h : R[X]} (hh : h.Monic) :
    (h.map f).rootPowerSumOne = f h.rootPowerSumOne := by
  simp [rootPowerSumOne, rootESymm_map_of_monic f hh]

theorem rootPowerSumTwo_map_of_monic {h : R[X]} (hh : h.Monic) :
    (h.map f).rootPowerSumTwo = f h.rootPowerSumTwo := by
  simp [rootPowerSumTwo, rootESymm_map_of_monic f hh, map_ofNat]

theorem rootPowerSumThree_map_of_monic {h : R[X]} (hh : h.Monic) :
    (h.map f).rootPowerSumThree = f h.rootPowerSumThree := by
  simp [rootPowerSumThree, rootESymm_map_of_monic f hh, map_ofNat]

end map

end Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def kohelT (h : R[X]) : R :=
  6 * h.rootPowerSumTwo + W.b₂ * h.rootPowerSumOne + h.natDegree * W.b₄

def kohelW (h : R[X]) : R :=
  10 * h.rootPowerSumThree + 2 * W.b₂ * h.rootPowerSumTwo + 3 * W.b₄ * h.rootPowerSumOne
    + h.natDegree * W.b₆

def kohelQuotient (h : R[X]) : WeierstrassCurve R :=
  W.veluQuotientOfSums (W.kohelT h) (W.kohelW h)

@[simp] theorem kohelQuotient_a₁ (h : R[X]) : (W.kohelQuotient h).a₁ = W.a₁ := rfl
@[simp] theorem kohelQuotient_a₂ (h : R[X]) : (W.kohelQuotient h).a₂ = W.a₂ := rfl
@[simp] theorem kohelQuotient_a₃ (h : R[X]) : (W.kohelQuotient h).a₃ = W.a₃ := rfl
theorem kohelQuotient_a₄ (h : R[X]) : (W.kohelQuotient h).a₄ = W.a₄ - 5 * W.kohelT h := rfl
theorem kohelQuotient_a₆ (h : R[X]) :
    (W.kohelQuotient h).a₆ = W.a₆ - W.b₂ * W.kohelT h - 7 * W.kohelW h := rfl

theorem kohelQuotient_b₂ (h : R[X]) : (W.kohelQuotient h).b₂ = W.b₂ := by
  simp [b₂]

@[simp] theorem kohelT_one : W.kohelT 1 = 0 := by
  simp [kohelT, rootPowerSumOne, rootPowerSumTwo]

@[simp] theorem kohelW_one : W.kohelW 1 = 0 := by
  simp [kohelW, rootPowerSumOne, rootPowerSumTwo, rootPowerSumThree]

@[simp] theorem kohelQuotient_one : W.kohelQuotient 1 = W := by
  ext <;> simp [kohelQuotient, veluQuotientOfSums]

section map

variable {S : Type*} [CommRing S] (f : R →+* S)

theorem map_kohelT {h : R[X]} (hh : h.Monic) : f (W.kohelT h) = (W.map f).kohelT (h.map f) := by
  nontriviality S
  simp [kohelT, rootPowerSumOne_map_of_monic f hh, rootPowerSumTwo_map_of_monic f hh,
    hh.natDegree_map, map_ofNat]

theorem map_kohelW {h : R[X]} (hh : h.Monic) : f (W.kohelW h) = (W.map f).kohelW (h.map f) := by
  nontriviality S
  simp [kohelW, rootPowerSumOne_map_of_monic f hh, rootPowerSumTwo_map_of_monic f hh,
    rootPowerSumThree_map_of_monic f hh, hh.natDegree_map, map_ofNat]

theorem map_kohelQuotient {h : R[X]} (hh : h.Monic) :
    (W.kohelQuotient h).map f = (W.map f).kohelQuotient (h.map f) := by
  ext
  · rfl
  · rfl
  · rfl
  · simp [kohelQuotient, veluQuotientOfSums, map_kohelT W f hh, map_ofNat]
  · simp [kohelQuotient, veluQuotientOfSums, map_kohelT W f hh, map_kohelW W f hh, map_ofNat]

theorem kohelQuotient_map_j {K L : Type*} [Field K] [Field L] (f : K →+* L) (V : WeierstrassCurve K)
    {h : K[X]} (hh : h.Monic) [(V.kohelQuotient h).IsElliptic]
    [((V.map f).kohelQuotient (h.map f)).IsElliptic] :
    ((V.map f).kohelQuotient (h.map f)).j = f (V.kohelQuotient h).j := by
  have := (V.kohelQuotient h).map_j f
  simp only [map_kohelQuotient V f hh] at this
  convert this using 2

end map

end WeierstrassCurve


