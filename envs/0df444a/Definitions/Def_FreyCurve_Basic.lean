-- Prove2me | Definitions.Def_FreyCurve_Basic
-- name    : FreyCurve_Basic
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/89bf9e5b-5499-59d7-9317-3137073d4947
-- title:
--   Invariants of the Frey curve: discriminant, b2​, b4​, c4​
-- statement:
--   Fix a Frey package $P$, i.e. nonzero integers $a,b,c$ and a prime $p \ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$, and let [`FreyPackage.freyCurve`](../def/FLTPrelim_FreyPackage.html#L90) be the associated Weierstrass curve over $\mathbb{Q}$ given by $a_1 = 1$, $a_2 = (b^p - 1 - a^p)/4$, $a_3 = 0$, $a_4 = -a^p b^p/16$, $a_6 = 0$. This module records the standard invariants of that presentation, all computed in $\mathbb{Q}$ with $a,b,c$ coerced from $\mathbb{Z}$.
--
--   [`FreyCurve.Δ`](../def/FreyCurve_Basic.html#L9) gives the discriminant of the model, $\Delta = (abc)^{2p}/2^8$; the identity uses the Fermat relation $a^p+b^p=c^p$. The accompanying instance asserts `WeierstrassCurve.IsElliptic` for `freyCurve P`, i.e. that this discriminant is a unit of $\mathbb{Q}$, which here follows from $abc \ne 0$; consequently the curve has a discriminant-as-unit $\Delta'$ and a $j$-invariant in Mathlib's sense. [`FreyCurve.b₂`](../def/FreyCurve_Basic.html#L26) and [`FreyCurve.b₄`](../def/FreyCurve_Basic.html#L29) give $b_2 = b^p - a^p$ and $b_4 = -(ab)^p/8$. [`FreyCurve.c₄`](../def/FreyCurve_Basic.html#L32) gives $c_4 = a^{2p} + a^p b^p + b^{2p}$, written as $(a^p)^2 + a^p b^p + (b^p)^2$, and [`FreyCurve.c₄'`](../def/FreyCurve_Basic.html#L36) rewrites the same quantity, again via the Fermat relation, as $c_4 = c^{2p} - (ab)^p$.
--
--   **Relation to Mathlib.** The quantities $b_2$, $b_4$, $c_4$, $\Delta$ and the class `WeierstrassCurve.IsElliptic` (whose field `isUnit` asks that $\Delta$ be a unit) are Mathlib's; this module only evaluates them on the project's `freyCurve` and supplies the `IsElliptic` instance for it.
--
--   **Where it is used.** These identities are the computational input to the local analysis of the Frey curve attached to a hypothetical Fermat solution: semistability, the valuation of the $j$-invariant at primes of bad reduction, and the description of the $2$-torsion.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (large part (≈74%): `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port)). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyCurve_Basic.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace FreyCurve
open FreyPackage

lemma Δ (P : FreyPackage) : P.freyCurve.Δ = (P.a * P.b * P.c) ^ (2 * P.p) / 2 ^ 8 := by
  trans (P.a ^ P.p) ^ 2 * (P.b ^ P.p) ^ 2 * (P.c ^ P.p) ^ 2 / 2 ^ 8
  · field_simp
    norm_cast
    simp [← P.hFLT, WeierstrassCurve.Δ, freyCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  · simp [← mul_pow, ← pow_mul, mul_comm 2]

instance (P : FreyPackage) : WeierstrassCurve.IsElliptic (freyCurve P) where
  isUnit := by
    rw [FreyCurve.Δ, isUnit_iff_ne_zero]
    apply div_ne_zero
    · norm_cast
      exact pow_ne_zero _ <| mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0
    · norm_num

lemma b₂ (P : FreyPackage) : P.freyCurve.b₂ = P.b ^ P.p - P.a ^ P.p := by
  simp [freyCurve, WeierstrassCurve.b₂]; ring

lemma b₄ (P : FreyPackage) : P.freyCurve.b₄ = -(P.a * P.b) ^ P.p / 8 := by
  simp [freyCurve, WeierstrassCurve.b₄]; ring

lemma c₄ (P : FreyPackage) :
    P.freyCurve.c₄ = (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2 := by
  simp [FreyCurve.b₂, FreyCurve.b₄, WeierstrassCurve.c₄]; ring

lemma c₄' (P : FreyPackage) :
    P.freyCurve.c₄ = P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p := by
  rw [FreyCurve.c₄]
  have h : (P.a : ℚ) ^ P.p + (P.b : ℚ) ^ P.p = (P.c : ℚ) ^ P.p := by exact_mod_cast P.hFLT
  rw [pow_mul', ← h, mul_pow]; ring

end FreyCurve


