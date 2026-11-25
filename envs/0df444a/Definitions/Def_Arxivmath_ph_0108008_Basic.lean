-- Prove2me | Definitions.Def_Arxivmath_ph_0108008_Basic
-- name    : Arxivmath_ph_0108008_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T19:34:04.104123+00:00
-- url     : https://prove2.me/theorems/5fa35b34-964e-5089-a2c9-f05da0585a49
-- title:
--   Cox-Thompson kernel and integral equation (1.1), coefficient equations (1.2), the Cox-Thompson uniqueness claim, order-0 Green's function g0, Riccati-Bessel u2 and the function p(r)
-- statement:
--   Objects of A. G. Ramm, *A counterexample to the uniqueness result of Cox and Thompson* (arXiv:math-ph/0108008v1). Primes denote $d/dr$.
--
--   1. **Riccati–Bessel functions.** The paper uses the regular and irregular Riccati–Bessel functions $u_m$, $v_m$ of real order $m>-1/2$ (as in Chadan–Sabatier). They enter only as a pair of families $u,v:\mathbb R\to(\mathbb R\to\mathbb R)$, order $\mapsto$ function. The order-$0$ functions are the explicit ones of Section 2: $u_0(r)=\sin r$, $v_0(r)=-\cos r$.
--   2. **$u_2$ (Section 2).** $u_2(r)=(3r^{-2}-1)\sin r-3r^{-1}\cos r$. At $r=0$ it takes the value $0$, which is its limit there.
--   3. **Green's function $g_0$ (Section 2).** $g_0(s,t)=u_0(\min(s,t))\,v_0(\max(s,t))=-\sin(\min(s,t))\cos(\max(s,t))$.
--   4. **$p$ (Section 2).** $p(r)=v_0(r)u_2'(r)-v_0'(r)u_2(r)$.
--   5. **Cox–Thompson kernel (Section 1).** For a finite set $S\subset\mathbb R$ and coefficients $\gamma$, $g(s,t)=\sum_{m\in S}\gamma_m\,u_m(\min(s,t))\,v_m(\max(s,t))$. This is $\sum_{m\in S}\gamma_m u_m(t)v_m(s)$ for $s>t$, extended symmetrically.
--   6. **Coefficient equations (1.2).** For finite $S,T\subset\mathbb R$: $\sum_{m\in S}\gamma_m[m(m+1)-l(l+1)]^{-1}=1$ for every $l\in T$.
--   7. **Solution of (1.1).** For a kernel $g$ and a real number $r$ (the condition $r>0$ is imposed where the notion is used), $h$ is a solution if:
--      - $h$ is continuous on $[0,r]$ and $h(0)=0$;
--      - for every $s\in[0,r]$, $t\mapsto g(s,t)h(t)t^{-2}$ is Lebesgue integrable on $(0,r]$;
--      - $h(s)=-\int_0^r g(s,t)h(t)t^{-2}\,dt$ for every $s\in[0,r]$.
--   8. **The Cox–Thompson claim (Section 1), for given families $u,v$.** Take any finite disjoint sets $S,T$ of reals in $(-1/2,\infty)$, any $\gamma$ satisfying (1.2) and any $r>0$. Then every solution $h$ of (1.1) for the kernel of $S,\gamma$ vanishes on $[0,r]$. The sets may have any sizes, and $T$ may be empty (then (1.2) is vacuous).
--
--   **Formalization Note** Mathlib has no Bessel functions of real order. So $u_m$, $v_m$ are parameters, not defined objects, and every statement that uses them assumes only $u_0=\sin$ and $v_0=-\cos$. The true Riccati–Bessel functions satisfy these, so the statements apply to them. The regularity built into "solution" is not stated in the paper. It makes the integral a genuine Lebesgue integral, and it can only make a counterexample harder to give.
-- source:
--   A. G. Ramm, A counterexample to the uniqueness result of Cox and Thompson, arXiv:math-ph/0108008v1 (2001), Section 1, Eqs. (1.1)-(1.2), PDF p. 1; Section 2, definitions of u0, v0, u2, g0 and p(r), PDF p. 2

import Mathlib

/-!
A. G. Ramm, *A counterexample to the uniqueness result of Cox and Thompson*,
arXiv:math-ph/0108008v1: the Cox–Thompson kernel and the integral equation (1.1), the coefficient
equations (1.2), the uniqueness claim of Cox and Thompson as restated in Section 1, the order-0
Riccati–Bessel Green's function `g₀`, the regular Riccati–Bessel function `u₂` of order 2, and the
function `p(r) = v₀(r) u₂'(r) - v₀'(r) u₂(r)` of Section 2 (PDF pp. 1-2).

The Riccati–Bessel functions `u_m`, `v_m` of arbitrary real order `m > -1/2` are not in Mathlib.
They enter only as parameters `u v : ℝ → ℝ → ℝ` (order ↦ function). The order-0 functions are the
ones the paper gives explicitly, `u₀(r) = sin r` and `v₀(r) = -cos r`, and `u₂` is the explicit
formula `u₂(r) = (3 r⁻² - 1) sin r - 3 r⁻¹ cos r` of Section 2 (with Lean's `0⁻¹ = 0` it takes the
value `0 = lim_{r→0} u₂(r)` at `r = 0`).
-/

open MeasureTheory Real

noncomputable section

namespace Arxivmath_ph_0108008

/-- Section 2, PDF p. 2: the regular Riccati–Bessel function of order 2,
`u₂(r) = (3 r⁻² - 1) sin r - 3 r⁻¹ cos r`. -/
def riccatiU2 (r : ℝ) : ℝ := (3 / r ^ 2 - 1) * sin r - 3 / r * cos r

/-- Section 2, PDF p. 2: the Green's function `g₀(s,t) = u₀(min(s,t)) v₀(max(s,t))` of `d² + 1`
built from `u₀ = sin` and `v₀ = -cos`, i.e. `g₀(s,t) = u₀(t) v₀(s)` for `t < s` and
`u₀(s) v₀(t)` for `t > s`. -/
def greenG0 (s t : ℝ) : ℝ := sin (min s t) * (-cos (max s t))

/-- Section 2, PDF p. 2: `p(r) = v₀(r) u₂'(r) - v₀'(r) u₂(r)` with `v₀(r) = -cos r`. -/
def wronskP (r : ℝ) : ℝ :=
  (-cos r) * deriv riccatiU2 r - deriv (fun x => -cos x) r * riccatiU2 r

/-- Section 1, PDF p. 1: the Cox–Thompson kernel
`g(s,t) = ∑_{m ∈ S} γ_m u_m(t) v_m(s)` for `s > t`, extended symmetrically, i.e.
`g(s,t) = ∑_{m ∈ S} γ_m u_m(min(s,t)) v_m(max(s,t))`, for Riccati–Bessel families
`u v : ℝ → ℝ → ℝ` (order ↦ function). -/
def ctKernel (u v : ℝ → ℝ → ℝ) (S : Finset ℝ) (γ : ℝ → ℝ) (s t : ℝ) : ℝ :=
  ∑ m ∈ S, γ m * u m (min s t) * v m (max s t)

/-- Eq. (1.2), PDF p. 1: `∑_{m ∈ S} γ_m [m(m+1) - l(l+1)]⁻¹ = 1` for every `l ∈ T`. -/
def CTCoeffEq (S T : Finset ℝ) (γ : ℝ → ℝ) : Prop :=
  ∀ l ∈ T, ∑ m ∈ S, γ m / (m * (m + 1) - l * (l + 1)) = 1

/-- Eq. (1.1), PDF p. 1: `h` is a solution on `[0, r]` of `h(s) = -∫₀ʳ g(s,t) h(t) t⁻² dt` with
`h(0) = 0`. The solution is required to be continuous on `[0, r]`, and the integrand to be
integrable on `(0, r]` for every `s ∈ [0, r]`, so that the integral is a genuine Lebesgue
integral. -/
def IsCTSolution (g : ℝ → ℝ → ℝ) (r : ℝ) (h : ℝ → ℝ) : Prop :=
  ContinuousOn h (Set.Icc 0 r) ∧ h 0 = 0 ∧
    ∀ s ∈ Set.Icc 0 r,
      IntegrableOn (fun t => g s t * h t * (t ^ 2)⁻¹) (Set.Ioc 0 r) ∧
        h s = -∫ t in (0 : ℝ)..r, g s t * h t * (t ^ 2)⁻¹

/-- Section 1, PDF p. 1: the uniqueness claim of Cox and Thompson as restated by the paper, for the
Riccati–Bessel families `u`, `v`: for all finite disjoint sets `S`, `T` of reals in `(-1/2, ∞)`, all
coefficients `γ` satisfying (1.2), and all `r > 0`, the only solution of (1.1) is `h = 0` on
`[0, r]`. -/
def CoxThompsonClaim (u v : ℝ → ℝ → ℝ) : Prop :=
  ∀ S T : Finset ℝ, (∀ m ∈ S, -(1 / 2 : ℝ) < m) → (∀ l ∈ T, -(1 / 2 : ℝ) < l) → Disjoint S T →
    ∀ γ : ℝ → ℝ, CTCoeffEq S T γ → ∀ r : ℝ, 0 < r → ∀ h : ℝ → ℝ,
      IsCTSolution (ctKernel u v S γ) r h → ∀ s ∈ Set.Icc 0 r, h s = 0

end Arxivmath_ph_0108008


