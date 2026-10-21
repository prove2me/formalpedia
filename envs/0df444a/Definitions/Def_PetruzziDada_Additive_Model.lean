-- Prove2me | Definitions.Def_PetruzziDada_Additive_Model
-- name    : PetruzziDada_Additive_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:31.427988+00:00
-- url     : https://prove2.me/theorems/8c26cb8a-3d4a-41e7-87c2-2d208a22f894
-- title:
--   Additive-demand price-setting newsvendor: expected profit, Λ, Θ, Ψ, L, p⁰, p(z), R and the hazard rate (§1, §1.1, pp. 184–185)
-- statement:
--   The single-period price-setting newsvendor with additive demand of Petruzzi and Dada (§1 and §1.1). A firm stocks $q$ units at unit cost $c$ and sells them at a single price $p$. Demand is
--   $$D(p,\varepsilon) = y(p) + \varepsilon, \qquad y(p) = a - bp,$$
--   where the random noise $\varepsilon$ takes values in $[A,B]$ and has probability density $f$, distribution function $F$ and mean $\mu$. Leftovers are disposed of at unit cost $h$ ($h<0$ is a salvage value) and each unit of unmet demand is charged a penalty $s$. A **model** consists of real numbers $a,b,c,h,s,A,B$ and a function $f:\mathbb R\to\mathbb R$ subject to the paper's standing assumptions (p. 184):
--   $$a>0,\quad b>0,\quad A>-a,\quad h\ge -c,\quad A<B,$$
--   $f(u)\ge 0$ for all $u$, $f(u)=0$ for $u\notin[A,B]$, $f$ integrable on $[A,B]$ and $\int_A^B f(u)\,du = 1$. No sign is imposed on $c$ or $s$.
--
--   Writing $q = y(p) + z$, the decision becomes a **stocking factor** $z$ and a price $p$. The file defines, for a model:
--
--   - $F(z) = \int_A^z f(u)\,du$ and $\mu = \int_A^B u f(u)\,du$;
--   - expected leftovers $\Lambda(z) = \int_A^z (z-u) f(u)\,du$ and expected shortages $\Theta(z) = \int_z^B (u-z) f(u)\,du$;
--   - the **expected profit** (p. 184)
--   $$E[\Pi(z,p)] = \int_A^z \big(p[y(p)+u] - h[z-u]\big) f(u)\,du + \int_z^B \big(p[y(p)+z] - s[u-z]\big) f(u)\,du - c[y(p)+z];$$
--   - the riskless profit $\Psi(p) = (p-c)[y(p)+\mu]$ (eq. (2)) and the loss function $L(z,p) = (c+h)\Lambda(z) + (p+s-c)\Theta(z)$ (eq. (3));
--   - the riskless price $p^0 = (a+bc+\mu)/2b$ (eq. (7)) and the price rule $p(z) = p^0 - \Theta(z)/2b$ (Lemma 1);
--   - the reduced objective $z \mapsto E[\Pi(z,p(z))]$ and its derivative $R(z) \equiv dE[\Pi(z,p(z))]/dz$ (Appendix, p. 192);
--   - the hazard rate $r(z) = f(z)/[1-F(z)]$;
--   - the **hazard condition** of Theorem 1(b): for every $z$ with $A \le z < B$, the hazard rate has a derivative $r'(z)$ at $z$ relative to $[A,B]$ (one-sided at $A$), and $2r(z)^2 + r'(z) > 0$.
--
--   **Formalization Note** The distribution of $\varepsilon$ is given by its density $f$, as on p. 184; integrals are interval integrals. The expected profit is the integral of p. 184, not the decomposition $\Psi - L$, which is eq. (1) and a separate theorem. The integrals in $F$, $\Lambda$, $\Theta$ are taken for every real $z$; because $f$ vanishes off $[A,B]$ they are the true expectations for $z$ outside $[A,B]$ too. $R$ is Mathlib's `deriv`, which is the genuine derivative wherever the reduced objective is differentiable (it is differentiable everywhere, which is part of a milestone). Where $F(z) = 1$ the quotient $f(z)/[1-F(z)]$ is $0$ by Lean's convention; the hazard condition is therefore required only on $[A,B)$, and the paper's "for $A \le z \le B$" is read there, since $r(B)$ is undefined. The derivative of $r$ is required to exist: it is not Mathlib's `derivWithin`, which would return $0$ where $r$ is not differentiable.
-- source:
--   Petruzzi & Dada, Pricing and the Newsvendor Problem: A Review with Extensions, Oper. Res. 47(2) 1999, pp. 184–185, §1 and §1.1, eqs. (2), (3), (7), Lemma 1, Theorem 1(b); p. 192, Appendix (R)

import Mathlib

open MeasureTheory

namespace PetruzziDada.Additive

/-! Additive-demand price-setting newsvendor of Petruzzi & Dada (1999), §1 and §1.1, pp. 184–185.

Demand is `D(p, ε) = y(p) + ε` with `y(p) = a - b p`, and the noise `ε` takes values in `[A, B]`
with probability density `f` (given here as a real function that is nonnegative, vanishes off
`[A, B]`, is integrable on `[A, B]` and integrates to one there). `c` is the unit stocking cost,
`h` the unit disposal cost of leftovers (`h < 0` is a salvage value), `s` the unit shortage
penalty. The fields `a_pos … h_ge` are the paper's standing assumptions of p. 184. -/

/-- The data of the additive-demand model (§1, §1.1, p. 184) with its standing assumptions:
`a > 0`, `b > 0`, `A > -a`, `h ≥ -c`, the bounded range `A < B` of `ε`, and `f` a probability
density of `ε` supported on `[A, B]`. No sign is imposed on `c` or `s`. -/
structure Model where
  a : ℝ
  b : ℝ
  c : ℝ
  h : ℝ
  s : ℝ
  A : ℝ
  B : ℝ
  f : ℝ → ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  A_gt : -a < A
  h_ge : -c ≤ h
  A_lt_B : A < B
  f_nonneg : ∀ u, 0 ≤ f u
  f_eq_zero : ∀ u, u ∉ Set.Icc A B → f u = 0
  f_integrable : IntervalIntegrable f volume A B
  f_total : ∫ u in A..B, f u = 1

namespace Model

variable (M : Model)

/-- Riskless demand `y(p) = a - b p` (p. 184). -/
def y (p : ℝ) : ℝ := M.a - M.b * p

/-- Cumulative distribution function of `ε`, `F(z) = ∫_A^z f(u) du`. -/
noncomputable def F (z : ℝ) : ℝ := ∫ u in M.A..z, M.f u

/-- Mean of `ε`, `μ = ∫_A^B u f(u) du`. -/
noncomputable def μ : ℝ := ∫ u in M.A..M.B, u * M.f u

/-- Expected leftovers `Λ(z) = ∫_A^z (z - u) f(u) du` (p. 184). -/
noncomputable def Λ (z : ℝ) : ℝ := ∫ u in M.A..z, (z - u) * M.f u

/-- Expected shortages `Θ(z) = ∫_z^B (u - z) f(u) du` (p. 184). -/
noncomputable def Θ (z : ℝ) : ℝ := ∫ u in z..M.B, (u - z) * M.f u

/-- Expected profit `E[Π(z, p)]` at stocking factor `z` (stock `q = y(p) + z`) and price `p`,
the integral of p. 184:
`∫_A^z (p[y(p) + u] - h[z - u]) f(u) du + ∫_z^B (p[y(p) + z] - s[u - z]) f(u) du - c[y(p) + z]`. -/
noncomputable def expProfit (z p : ℝ) : ℝ :=
  (∫ u in M.A..z, (p * (M.y p + u) - M.h * (z - u)) * M.f u)
    + (∫ u in z..M.B, (p * (M.y p + z) - M.s * (u - z)) * M.f u)
    - M.c * (M.y p + z)

/-- Riskless profit `Ψ(p) = (p - c)[y(p) + μ]`, eq. (2), p. 184. -/
noncomputable def Ψ (p : ℝ) : ℝ := (p - M.c) * (M.y p + M.μ)

/-- Loss function `L(z, p) = (c + h)Λ(z) + (p + s - c)Θ(z)`, eq. (3), p. 184. -/
noncomputable def L (z p : ℝ) : ℝ := (M.c + M.h) * M.Λ z + (p + M.s - M.c) * M.Θ z

/-- Optimal riskless price `p⁰ = (a + b c + μ) / 2b`, eq. (7), p. 185. -/
noncomputable def p0 : ℝ := (M.a + M.b * M.c + M.μ) / (2 * M.b)

/-- The price rule of Lemma 1, `p(z) = p⁰ - Θ(z) / 2b` (p. 185). -/
noncomputable def price (z : ℝ) : ℝ := M.p0 - M.Θ z / (2 * M.b)

/-- The reduced objective `E[Π(z, p(z))]` (p. 185). -/
noncomputable def reducedProfit (z : ℝ) : ℝ := M.expProfit z (M.price z)

/-- `R(z) ≡ dE[Π(z, p(z))]/dz` (Appendix, proof of Theorem 1, p. 192): the derivative of the
reduced objective. -/
noncomputable def R (z : ℝ) : ℝ := deriv M.reducedProfit z

/-- Hazard rate `r(z) = f(z) / [1 - F(z)]` (Theorem 1(b), p. 185). Where `F(z) = 1` the Lean
quotient is `0`. -/
noncomputable def hazard (z : ℝ) : ℝ := M.f z / (1 - M.F z)

/-- The condition of Theorem 1(b), `2 r(z)² + dr(z)/dz > 0`, read on `A ≤ z < B`: at each such `z`
the hazard rate has a derivative `r'` within `[A, B]` (one-sided at `A`), and `2 r(z)² + r' > 0`.
The point `z = B`, where `F(B) = 1` and `r(B)` is undefined, is excluded. -/
def HazardCondition : Prop :=
  ∀ z ∈ Set.Ico M.A M.B, ∃ r' : ℝ,
    HasDerivWithinAt M.hazard r' (Set.Icc M.A M.B) z ∧ 0 < 2 * M.hazard z ^ 2 + r'

end Model

end PetruzziDada.Additive


