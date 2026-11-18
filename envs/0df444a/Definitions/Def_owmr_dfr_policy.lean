-- Prove2me | Definitions.Def_owmr_dfr_policy
-- name    : owmr_dfr_policy
-- status  : Definition
-- author  : @Ming Hu
-- created : 2026-11-17T09:56:40.735934+00:00
-- url     : https://prove2.me/theorems/de38ace1-c36f-4322-bde5-a0fedcd9b13b
-- title:
--   DFR policy $\pi_{\rm DFR}(\theta)$ (Definition D.1) and DFR demand conditional on positive demand
-- statement:
--   Fix a network $N$ under the standing assumptions of Section 3 and a weight $\theta$. This file defines the constants, the demand condition and the policy of Appendix D.
--
--   **Constants.** $\lambda=2-\sqrt2$ (`dfrLambda`) and $\gamma_\lambda=1+\lambda/2+\sqrt{1+\lambda^2/4}\approx2.335$ (`dfrGamma`).
--
--   **DFR demand.** Write $\bar G_i(x)=\mathbb P(D_i>x)$ for the survival function of retailer $i$'s one-period demand (`survival`). Retailer $i$ has an absolutely continuous DFR distribution conditional on positive demand (`DFRPositive`) when
--
--   1. $\mathbb P(D_i\in A,\ D_i>0)=0$ for every Lebesgue-null set $A\subseteq\mathbb R$, and
--   2. the conditional survival function $x\mapsto\bar G_i(x)/\bar G_i(0)=\mathbb P(D_i>x\mid D_i>0)$ is log-convex on $[0,\infty)$: for $x,y\ge0$ and $0\le\eta\le1$,
--   $$\frac{\bar G_i(\eta x+(1-\eta)y)}{\bar G_i(0)}\le\Bigl(\frac{\bar G_i(x)}{\bar G_i(0)}\Bigr)^{\eta}\Bigl(\frac{\bar G_i(y)}{\bar G_i(0)}\Bigr)^{1-\eta}.$$
--
--   **Planning quantities (rule (i)).** For a canonical optimum $(\hat s,\hat S)$ of retailer $i$ with width $\hat w=\hat S-\hat s$, let $U$ be the renewal measure of $D_i$ and $M(\hat w)=U[0,\hat w)$, as in (9). Then $z_{\hat w}=K_i/M(\hat w)$ (`dfrZ`), $m_{\hat w}=B_{\hat w}$ is the mirror cost of $(\hat s,\hat S)$ (`dfrMirror`), $t_0=U\{0\}/M(\hat w)$ (`dfrT0`), and $t=\min\{1,\sqrt{z_{\hat w}/m_{\hat w}}\}$, with $t=1$ if $m_{\hat w}=0$ (`dfrT`).
--
--   **Choices (`IsDFRChoice N θ c`).** The FIFO choices $c=(s_i,S_i,a_i,s_0,S_0)$ follow Definition D.1 when:
--
--   1. each retailer with $K_i=0$ uses base stock ($s_i=S_i$) at a minimizer $S_i$ of $F_i$, with mirror center $a_i=S_i$;
--   2. each retailer with $K_i>0$ has a canonical optimum $(\hat s,\hat S)$ at planning setup cost $K_i/\theta$ such that: if $t=1$, it uses $(s_i,S_i)=(\hat s,\hat S)$ with a mirror center $a_i$ minimizing its mirror cost; if $t<1$ and $t\le t_0$, it uses base stock at a minimizer of $F_i$, with $a_i=S_i$; if $t_0<t<1$, its width $w=S_i-s_i$ satisfies $U[0,w)=t\,M(\hat w)$, its target $S_i$ minimizes the long-run average holding and backlog cost among width-$w$ policies, and $a_i$ minimizes the mirror cost of $(s_i,S_i)$;
--   3. the supplier uses $s_0\le S_0$ with long-run average cost $J_0(K_0+K_{\max})$ (rule (iii) of Definition 1).
--
--   The policy $\pi_{\rm DFR}(\theta)$ is the deterministic FIFO policy of Definition 1 with the initialization of Appendix B (`fifoPolicy N x c`), run with such choices. The predicate admits every tie-breaking rule, including the smallest minimizers fixed in Definition D.1.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix D, Definition D.1 (DFR Policy), p. E.23, and the demand assumption of Theorem D.1 (DFR Demand), p. E.24; renewal quantities $U$ and $M$ in (9) and mirror cost $B_w$ in (14).

import Definitions.Def_owmr_fifo_policy
import Definitions.Def_owmr_renewal

/-!
# The DFR policy `π_DFR(θ)` (Definition D.1) and the DFR demand assumption (Theorem D.1)

Source: M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse
Multi-Retailer Systems", Appendix D (Smaller Constants for DFR Demand): Definition D.1 (DFR
Policy), Theorem D.1 (DFR Demand), and the quantities `M(w) = U[0,w)` and `U` of (9).

The policy `π_DFR(θ)` runs the FIFO mechanism of Definition 1 (rules (ii) and (iii), including
the initialization of Appendix B) with retailer policies and mirror centers selected by the rules
below; it is therefore `fifoPolicy N x c` for a choice `c` satisfying `IsDFRChoice N θ c`.
As in `IsFIFOChoice`, the predicate allows every tie-breaking rule.
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace OWMR

variable {n : ℕ}

/-- `λ = 2 - √2` (Theorem D.1). -/
def dfrLambda : ℝ := 2 - Real.sqrt 2

/-- `γ_λ = 1 + λ/2 + √(1 + λ²/4)` (Theorem D.1), approximately `2.335`. -/
def dfrGamma : ℝ := 1 + dfrLambda / 2 + Real.sqrt (1 + dfrLambda ^ 2 / 4)

/-- The survival function `x ↦ ℙ(D_i > x)` of retailer `i`'s one-period demand. -/
def Network.survival (N : Network n) (i : Fin n) (x : ℝ) : ℝ :=
  (N.marginal i {z : ℝ≥0 | x < (z : ℝ)}).toReal

/-- Retailer `i`'s demand has an absolutely continuous DFR distribution conditional on positive
demand (Theorem D.1):
* absolute continuity: `ℙ(D_i ∈ A, D_i > 0) = 0` for every Lebesgue-null set `A ⊆ ℝ`;
* DFR: the conditional survival function `F̄(x) = ℙ(D_i > x | D_i > 0) = ℙ(D_i > x)/ℙ(D_i > 0)`
  is log-convex on `[0, ∞)`: `F̄(ηx + (1-η)y) ≤ F̄(x)^η F̄(y)^(1-η)` for `x, y ≥ 0`,
  `0 ≤ η ≤ 1`. -/
def Network.DFRPositive (N : Network n) (i : Fin n) : Prop :=
  (∀ A : Set ℝ, volume A = 0 → N.marginal i {z : ℝ≥0 | (z : ℝ) ∈ A ∧ 0 < (z : ℝ)} = 0) ∧
  ∀ x y η : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ η → η ≤ 1 →
    N.survival i (η * x + (1 - η) * y) / N.survival i 0
      ≤ (N.survival i x / N.survival i 0) ^ η * (N.survival i y / N.survival i 0) ^ (1 - η)

/-- Definition D.1 (i): `z_ŵ = K/M(ŵ)` for retailer `i` and a canonical optimum `(ŝ, Ŝ)` of
width `ŵ = Ŝ - ŝ`, with `M(ŵ) = U[0, ŵ)`. -/
def Network.dfrZ (N : Network n) (i : Fin n) (sh Sh : ℝ) : ℝ :=
  N.K i / (renewalM (N.marginal i) (Sh - sh)).toReal

/-- Definition D.1 (i): `m_ŵ = B_ŵ`, the mirror cost of the width-`ŵ` policy `(ŝ, Ŝ)`. -/
def Network.dfrMirror (N : Network n) (i : Fin n) (sh Sh : ℝ) : ℝ :=
  (mirrorCost (N.marginal i) N.h N.p sh Sh).toReal

/-- Definition D.1 (i): `t₀ = U{0}/M(ŵ)`. -/
def Network.dfrT0 (N : Network n) (i : Fin n) (sh Sh : ℝ) : ℝ :=
  (renewalMeasure (N.marginal i) {0}).toReal / (renewalM (N.marginal i) (Sh - sh)).toReal

/-- Definition D.1 (i): `t = min{1, √(z_ŵ/m_ŵ)}`, with `t = 1` if `m_ŵ = 0`. -/
def Network.dfrT (N : Network n) (i : Fin n) (sh Sh : ℝ) : ℝ :=
  if N.dfrMirror i sh Sh = 0 then 1
  else min 1 (Real.sqrt (N.dfrZ i sh Sh / N.dfrMirror i sh Sh))

/-- The requirements of Definition D.1 on the choices `c` of `π_DFR(θ)`.
* (ii) A retailer with `K_i = 0` uses base stock (`s_i = S_i`) at a minimizer of `F_i`; by (iii)
  its mirror center is its target.
* (i)-(iii) A retailer with `K_i > 0` takes a canonical optimum `(ŝ, Ŝ)` at planning setup cost
  `K_i/θ` and computes `t` and `t₀`. If `t = 1` it uses `(ŝ, Ŝ)`. If `t < 1` and `t ≤ t₀` it uses
  base stock at a minimizer of `F_i`, with mirror center equal to its target. If `t < 1` and
  `t₀ < t` it uses a width-`w_t` policy with `U[0, w_t) = t M(ŵ)` whose target minimizes the
  long-run average holding and backlog cost among width-`w_t` policies. In the `(s,S)` cases
  the mirror center minimizes the mirror cost of the selected policy.
* (iv), via rule (iii) of Definition 1: the supplier `(s₀, S₀)` policy attains the supplier
  value `J₀(K₀ + K_max)`. -/
def IsDFRChoice (N : Network n) (θ : ℝ) (c : FIFOChoice n) : Prop :=
  (∀ i, N.K i = 0 → c.s i = c.S i ∧ (∀ y, N.F i (c.S i) ≤ N.F i y) ∧ c.a i = c.S i) ∧
  (∀ i, 0 < N.K i → ∃ sh Sh : ℝ,
    IsCanonicalOptimum (N.marginal i) (N.F i) (N.K i / θ) sh Sh ∧
    (N.dfrT i sh Sh = 1 → c.s i = sh ∧ c.S i = Sh ∧
      mirrorAvg (N.marginal i) N.h N.p sh Sh (c.a i) = mirrorCost (N.marginal i) N.h N.p sh Sh) ∧
    (N.dfrT i sh Sh < 1 → N.dfrT i sh Sh ≤ N.dfrT0 i sh Sh →
      c.s i = c.S i ∧ (∀ y, N.F i (c.S i) ≤ N.F i y) ∧ c.a i = c.S i) ∧
    (N.dfrT i sh Sh < 1 → N.dfrT0 i sh Sh < N.dfrT i sh Sh →
      renewalM (N.marginal i) (c.S i - c.s i)
          = ENNReal.ofReal (N.dfrT i sh Sh) * renewalM (N.marginal i) (Sh - sh) ∧
      (∀ S' : ℝ, ssAvgCost (N.marginal i) (N.F i) 0 (c.s i) (c.S i)
        ≤ ssAvgCost (N.marginal i) (N.F i) 0 (S' - (c.S i - c.s i)) S') ∧
      mirrorAvg (N.marginal i) N.h N.p (c.s i) (c.S i) (c.a i)
        = mirrorCost (N.marginal i) N.h N.p (c.s i) (c.S i))) ∧
  c.s0 ≤ c.S0 ∧
  ssAvgCost N.aggregate N.fL0 (N.K0 + N.Kmax) c.s0 c.S0 = N.J0 (N.K0 + N.Kmax)

end OWMR


