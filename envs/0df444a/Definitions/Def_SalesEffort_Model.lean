-- Prove2me | Definitions.Def_SalesEffort_Model
-- name    : SalesEffort_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:14:55.197857+00:00
-- url     : https://prove2.me/theorems/19ec0fd9-72c8-41fa-9154-c196af820bf5
-- title:
--   §3, pp.9–11 — the sales-effort model (Definition 1, Assumption 1), maximizing rates, $\Delta_t(n)$, solutions of the HJB system (2), $\lambda^*(t,n)$ and $L_t(n)$
-- statement:
--   This module fixes the model of Du, Hu and Wu's sales-effort problem with an all-or-nothing contract, and the objects of its HJB analysis.
--
--   **Model** (Definition 1, p.9; Assumption 1, p.10). A seller must make $N$ sales. If she does, she earns a lump sum $b\ge0$ plus a commission $p\ge0$ on every further sale; otherwise she earns nothing. She controls the intensity $\lambda\in[\underline\lambda,\bar\lambda]$ of a Poisson sales process at cost rate $c(\lambda)\ge0$. The cost satisfies Assumption 1:
--
--   1. $\underline\lambda>0$ is the cost-free rate, $c(\underline\lambda)=0$;
--   2. $c$ is invertible and convex on $[\underline\lambda,\bar\lambda]$, read here as: $c$ is continuous, injective and $\alpha$-strongly convex on $[\underline\lambda,\bar\lambda]$ for some $\alpha>0$;
--   3. $\lambda^*\in[\underline\lambda,\bar\lambda]$ maximizes $\lambda p-c(\lambda)$.
--
--   **Maximizing rate.** For a marginal value $\Delta\in\mathbb R$, a rate $\ell$ is optimal if $\ell\in\arg\max_{\lambda\in[\underline\lambda,\bar\lambda]}\{\lambda\Delta-c(\lambda)\}$.
--
--   **The HJB system** (Proposition 1, p.11). With $t\ge0$ the time to go and $n$ the number of sales still needed, $J$ solves (2) if
--   $$\frac{\partial J_t(n)}{\partial t}=\max_{\lambda\in[\underline\lambda,\bar\lambda]}\big\{\lambda[J_t(n-1)-J_t(n)]-c(\lambda)\big\}\quad(n\ge1,\ t\ge0),$$
--   with $J_0(n)=0$ for $n\ge1$ and $J_t(0)=b+[\lambda^*p-c(\lambda^*)]t$.
--
--   **Derived objects.** The marginal value $\Delta_t(n):=J_t(n-1)-J_t(n)$, with $\Delta_t(0)=p$ (Online Appendix p.2). A rate function $\lambda^*(t,n)$ is a maximizing rate at $\Delta_t(n)$ for every $t\ge0$ and $n\ge0$ (so $\lambda^*(t,0)=\lambda^*$). The cumulative rate is $L_t(n)=\int_0^t\lambda^*(s,n)\,ds$ (Online Appendix p.2).
--
--   These objects carry every statement of the mission: Proposition 1, Inequality (OA.1), Lemma A1 and Theorem 1.
--
--   **Formalization Note** The model is the structure `Model` with fields `lo`, `hi`, `b`, `p`, `c`, `lstar` ($\underline\lambda,\bar\lambda,b,p,c,\lambda^*$). Assumption 1(ii) is read as strong convexity because the paper calls the maximizer unique under "the regularity conditions specified in Assumption 1" (p.11) and its proof uses $\alpha=\min c''>0$ (Online Appendix p.5); no derivative of $c$ is assumed, and with convexity alone the arg max need not be unique. $\lambda^*$ is a maximizer over the feasible set $[\underline\lambda,\bar\lambda]$. The solution predicate `IsHJBSolution` asks for the derivative of $t\mapsto J_t(n)$ within $[0,\infty)$ at every $t\ge0$ (one-sided at $0$) and for the maximum to be attained; values at $t<0$ are unconstrained. The rate function `IsRateFn` is a hypothesis on a function `lam`, not a choice. Optimal rates use the published `argmaxOn`.
-- source:
--   Du, Hu & Wu, Sales Effort Management under All-or-Nothing Constraint, SSRN 3506499 (University of Toronto TSpace submitted manuscript), https://ssrn.com/abstract=3506499, Definition 1 p.9; Assumption 1 p.10; Proposition 1 and the paragraph after it, p.11; Online Appendix p.2 (J∗_t(−1) = J∗(0) + p, L_t(n)), p.4 (λ∗(t,0) = λ∗)

import Mathlib
import Definitions.Def_MonotoneCompStatics_Monotonicity_argmaxOn

open Set

namespace SalesEffort

/-- **The sales-effort model** of Du, Hu & Wu, *Sales Effort Management under All-or-Nothing
Constraint*, SSRN 3506499 (TSpace submitted manuscript), Definition 1, p.9, and Assumption 1
(Cost Function), p.10.

* `lo`, `hi`: the feasible sales rates `[λ̲, λ̄]` (p.10); `lo = λ̲ > 0` is the cost-free rate.
* `b`, `p`: the lump-sum bonus and the per-sale commission beyond the target of the
  all-or-nothing payout `R(x) = b + p(x − N)` if `x ≥ N`, `0` otherwise, with `b, p ≥ 0`
  (Definition 1, p.9).
* `c`: the cost rate `c(λ) ≥ 0` of inducing the sales intensity `λ` (p.10).
* `lstar`: `λ∗ = arg max {λp − c(λ)}`, the profit-maximizing rate (Assumption 1(iii)).

Assumption 1: (i) `c(λ̲) = 0`; (ii) `c` is invertible and convex on `[λ̲, λ̄]`;
(iii) `λ∗ ∈ [λ̲, λ̄]`.

**Formalization Note.**
1. Assumption 1(ii) "convex" is read as the regularity the paper uses ("provided that the cost
   function c(λ) satisfies the regularity conditions specified in Assumption 1", p.11, and
   "α = min_{λ∈[λ̲,λ̄]} c″(λ) > 0", Online Appendix p.5): `c` is continuous on `[λ̲, λ̄]` and
   `α`-strongly convex there for some `α > 0`. Every `C²` cost with `c″ ≥ α > 0` qualifies; no
   derivative of `c` is assumed. With convexity alone the arg max need not be unique
   (`c(λ) = λ − 1` on `[1, 3]`, `p = 1`).
2. "Invertible" is kept as injectivity on `[λ̲, λ̄]` (it follows from the other fields).
3. `c` is a function on `ℝ`; only its values on `[λ̲, λ̄]` enter any statement.
4. `λ∗` is a field carrying its defining property: a maximizer of `λ ↦ λp − c(λ)` over the
   feasible set `[λ̲, λ̄]` (Assumption 1(iii) puts it there). It is unique by strong convexity.
5. `λ̲ = λ̄` is allowed. -/
structure Model where
  /-- the cost-free (lowest feasible) sales rate `λ̲` -/
  lo : ℝ
  /-- the highest feasible sales rate `λ̄` -/
  hi : ℝ
  /-- the lump-sum bonus `b` paid when the target is reached -/
  b : ℝ
  /-- the commission `p` per sale beyond the target -/
  p : ℝ
  /-- the cost rate `c(λ)` -/
  c : ℝ → ℝ
  /-- the profit-maximizing rate `λ∗` -/
  lstar : ℝ
  lo_pos : 0 < lo
  lo_le_hi : lo ≤ hi
  b_nonneg : 0 ≤ b
  p_nonneg : 0 ≤ p
  c_lo : c lo = 0
  c_nonneg : ∀ x ∈ Icc lo hi, 0 ≤ c x
  c_injOn : InjOn c (Icc lo hi)
  c_continuousOn : ContinuousOn c (Icc lo hi)
  c_strongConvex : ∃ α : ℝ, 0 < α ∧ StrongConvexOn (Icc lo hi) α c
  lstar_max : lstar ∈ MonotoneCompStatics.Monotonicity.argmaxOn (fun l => l * p - c l) (Icc lo hi)

/-- `ℓ` is a profit-maximizing sales rate at the marginal value `Δ`:
`ℓ ∈ arg max_{λ∈[λ̲,λ̄]} {λΔ − c(λ)}` (Du, Hu & Wu, SSRN 3506499, p.11 below (2), and Online
Appendix p.3: "λ∗(t,n) = arg max_{λ∈[λ̲,λ̄]} {λ∆t(n) − c(λ)}"). -/
def IsOptRate (M : Model) (Δ ℓ : ℝ) : Prop :=
  ℓ ∈ MonotoneCompStatics.Monotonicity.argmaxOn (fun l => l * Δ - M.c l) (Icc M.lo M.hi)

/-- The marginal value `∆_t(n) := J_t(n−1) − J_t(n)` (Du, Hu & Wu, SSRN 3506499, p.11), with the
paper's convention `∆_t(0) = p` (Online Appendix p.2: "we let J∗_t(−1) = J∗(0) + p"). Here `t` is
the time to go and `n` the number of sales still needed. -/
def marginal (M : Model) (J : ℝ → ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then M.p else J t (n - 1) - J t n

/-- `J` solves the HJB system (2) of Proposition 1 (Du, Hu & Wu, SSRN 3506499, p.11) on
`t ∈ [0, ∞)`:
`∂J_t(n)/∂t = max_{λ∈[λ̲,λ̄]} {λ[J_t(n − 1) − J_t(n)] − c(λ)}` for all `n ≥ 1`, with boundary
conditions `J_0(n) = 0` for `n ≥ 1` and `J_t(0) = b + [λ∗p − c(λ∗)]t`.

**Formalization Note.** `J t n` is the value at time to go `t` with `n` sales still needed. The
derivative is required at every `t ≥ 0`, within `[0, ∞)` (one-sided at `t = 0`), and its value
is the maximum of the right-hand side, which is attained (`IsGreatest` of the image of
`[λ̲, λ̄]`). Values of `J` at `t < 0` are unconstrained. -/
def IsHJBSolution (M : Model) (J : ℝ → ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n → J 0 n = 0) ∧
  (∀ t : ℝ, 0 ≤ t → J t 0 = M.b + (M.lstar * M.p - M.c M.lstar) * t) ∧
  ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t → ∃ v : ℝ,
    HasDerivWithinAt (fun s => J s n) v (Ici 0) t ∧
    IsGreatest ((fun l => l * (J t (n - 1) - J t n) - M.c l) '' Icc M.lo M.hi) v

/-- `L` is the profit-maximizing sales rate `λ∗(t,n)` of the solution `J`: at every `t ≥ 0` and
every `n ≥ 0`, `L t n` maximizes `λ∆_t(n) − c(λ)` over `[λ̲, λ̄]` (Du, Hu & Wu, SSRN 3506499,
p.11 below (2)). At `n = 0` this forces `L t 0 = λ∗`, the paper's convention `λ∗(t,0) = λ∗`
(Online Appendix p.4). The maximizer is unique under Assumption 1, so `L` is determined on
`t ≥ 0`. -/
def IsRateFn (M : Model) (J : ℝ → ℕ → ℝ) (L : ℝ → ℕ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ, IsOptRate M (marginal M J t n) (L t n)

/-- The cumulative rate `L_t(n) = ∫₀ᵗ λ∗(s,n) ds` (Du, Hu & Wu, SSRN 3506499, Online Appendix
p.2), as an interval integral of the rate function `L`. -/
noncomputable def cumRate (L : ℝ → ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  ∫ s in (0 : ℝ)..t, L s n

end SalesEffort


