-- Prove2me | Definitions.Def_FeinbergLiang_ACOE_Inventory
-- name    : FeinbergLiang_ACOE_Inventory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:01:40.906955+00:00
-- url     : https://prove2.me/theorems/4c59e1ef-3a1b-4893-af02-64572bf58bd1
-- title:
--   Periodic-review inventory control with setup costs and backorders: model, K-convexity, (s, S) policies, α*, G_α, H and the renewal bound U
-- statement:
--   This file defines the periodic-review inventory control problem of Feinberg and Liang (2022, §4), case $\mathbb X=\mathbb R$, $\mathbb A=\mathbb R^+=[0,\infty)$, and the auxiliary objects used in its analysis.
--
--   **Data.** The problem is given by the following parameters.
--   1. A fixed ordering cost $K\ge0$.
--   2. A per-unit ordering cost $\bar c>0$.
--   3. A convex holding/backordering cost $h:\mathbb R\to\mathbb R$ with $h(x)\to\infty$ as $|x|\to\infty$, which (as the paper assumes without loss of generality) is nonnegative with $h(0)=0$.
--   4. i.i.d. nonnegative demands $D_1,D_2,\dots$ with common law $\mu$, such that $\mathbb E[h(x-D)]<\infty$ for all $x$ and $P(D>0)>0$.
--
--   **Dynamics and cost.** The inventory evolves as $x_{t+1}=x_t+a_t-D_{t+1}$, and the one-step cost (4.1) is
--   $$c(x,a)=K\,I_{\{a>0\}}+\bar c\,a+\mathbb E[h(x+a-D)].$$
--
--   **Auxiliary objects.**
--   1. A function $f:\mathbb R\to\mathbb R$ is *$K$-convex* (Definition 4.1) if $f((1-\lambda)x+\lambda y)\le(1-\lambda)f(x)+\lambda f(y)+\lambda K$ for all $x\le y$ and $\lambda\in(0,1)$. It is *inf-compact* if all its level sets $\{f\le\lambda\}$ are compact.
--   2. The *$(s,S)$ policy* (Definition 4.2) orders up to $S$ when $x<s$ and orders nothing otherwise. Its variant orders up to $S$ when $x\le s$.
--   3. For $S$ minimizing $f$, the threshold is $s=\inf\{x\le S: f(x)\le K+f(S)\}$ (4.6).
--   4. The critical discount factor (4.7) is
--   $$\alpha^*=1+\lim_{x\to-\infty}\frac{h(x)}{\bar c\,x},$$
--   which may equal $-\infty$.
--   5. $G_\alpha(x)=\bar cx+\mathbb E[h(x-D)]+\alpha\mathbb E[v_\alpha(x-D)]$ (4.3) and, for a function $\tilde u$, $H(x)=\bar cx+\mathbb E[h(x-D)]+\mathbb E[\tilde u(x-D)]$ (4.9).
--   6. The optimality equation (4.10) for a stationary policy $\phi$ at $x$:
--   $$\underline w+\tilde u(x)=K I_{\{\phi(x)>0\}}+H(x+\phi(x))-\bar cx=\min\Big\{\min_{a\ge0}[K+H(x+a)],\,H(x)\Big\}-\bar cx.$$
--   7. The renewal process $N(t)=\sup\{n\ge0: S_n\le t\}$ of the partial sums $S_n=D_1+\dots+D_n$, together with $E_y(x)=\mathbb E[h(x-S_{N(y)+1})]$ and $E(x)=h(x)+E_{x-x^*_L}(x)$.
--   8. The bound (4.13):
--   $$U(x)=\begin{cases}K+\bar c(x^*_U-x), & x<x^*_L,\\ K+\bar c(x^*_U-x^*_L)+(E(x)+\bar c\,\mathbb E[D])(1+\mathbb E[N(x-x^*_L)]), & x\ge x^*_L.\end{cases}$$
--
--   These are the objects in terms of which the paper proves that the average-cost optimality equation holds for the inventory problem and that an optimal $(s,S)$ policy can be read off from it.
--
--   **Formalization Note.** The model is an instance `inventoryMDP D : MDP ℝ ℝ≥0` of the general MDP, with lower cost bound $0$. The cost is real and nonnegative, so it is stored exactly. $\alpha^*$ is an extended real, defined via a `liminf` at $-\infty$; this equals the limit, which exists. $G_\alpha$ and $H$ are extended-real valued, because their last expectations can a priori be $+\infty$; the theorems that use them conclude that they are finite. `lowerThreshold` is `sInf` on ℝ, and the theorems that use it prove that the set is bounded below. In (4.10), "min" is read as attained: the middle expression is at most $K+H(x+a)-\bar cx$ for every $a\ge0$ and at most $H(x)-\bar cx$. $N(t)$ takes values in $\mathbb N\cup\{\infty\}$. On the null event $N(y)=\infty$ the index in $E_y$ is read as $1$, which does not affect the expectation. Bertsekas's derivative-free $K$-convexity (platform definition `BertsekasKConvex`) is an equivalent notion for real functions; this file uses the paper's Definition 4.1 literally.
-- source:
--   Feinberg and Liang, On the optimality equation for average cost Markov decision processes and its validity for inventory control, Annals of Operations Research 317, 2022, pp. 576-578, Section 4 (parameters 1-5, Eqs. (4.1), (4.3), (4.5)-(4.7), (4.9), (4.10), (4.13), Definitions 4.1, 4.2, renewal process p. 578)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace FeinbergLiang.ACOE

/-- The data of the periodic-review inventory control problem with backorders and setup costs,
case (i) `X = ℝ`, `A = ℝ⁺` (Feinberg–Liang 2022, §4, p. 576): fixed ordering cost `K ≥ 0`,
per-unit ordering cost `c̄ > 0`, convex holding/backordering cost `h` with `h(x) → ∞` as
`|x| → ∞`, and i.i.d. nonnegative demands with law `μ` such that `E[h(x - D)] < ∞` for all `x`
and `P(D > 0) > 0`. The last two fields are the paper's standing assumption "without loss of
generality, `h` is nonnegative and `h(0) = 0`". -/
structure InventoryData where
  /-- fixed ordering cost `K` -/
  K : ℝ
  /-- per-unit ordering cost `c̄` -/
  cbar : ℝ
  /-- holding/backordering cost per period -/
  h : ℝ → ℝ
  /-- the law of the one-period demand `D` -/
  μ : Measure ℝ
  K_nonneg : 0 ≤ K
  cbar_pos : 0 < cbar
  h_convex : ConvexOn ℝ Set.univ h
  h_tendsto : Tendsto h (cocompact ℝ) atTop
  [isProb : IsProbabilityMeasure μ]
  demand_nonneg : μ (Set.Iio 0) = 0
  h_integrable : ∀ x, Integrable (fun d => h (x - d)) μ
  demand_pos : 0 < μ (Set.Ioi 0)
  h_nonneg : ∀ x, 0 ≤ h x
  h_zero : h 0 = 0

attribute [instance] InventoryData.isProb

/-- The transition probability of the inventory model: `x_{t+1} = x_t + a_t - D_{t+1}`, i.e.
`q(· | x, a)` is the law of `x + a - D`. -/
noncomputable def invKernel (D : InventoryData) : Kernel (ℝ × ℝ≥0) ℝ :=
  Kernel.map (Kernel.deterministic id measurable_id ×ₖ Kernel.const (ℝ × ℝ≥0) D.μ)
    (fun z : (ℝ × ℝ≥0) × ℝ => z.1.1 + (z.1.2 : ℝ) - z.2)

instance (D : InventoryData) : IsMarkovKernel (invKernel D) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The inventory MDP with one-step cost (4.1)
`c(x, a) = K·I{a > 0} + c̄ a + E[h(x + a - D)]`, which is real and nonnegative, so `lower = 0`. -/
noncomputable def inventoryMDP (D : InventoryData) : MDP ℝ ℝ≥0 where
  lower := 0
  cost x a := ENNReal.ofReal
    (D.K * (if 0 < a then 1 else 0) + D.cbar * (a : ℝ) + ∫ d, D.h (x + a - d) ∂D.μ)
  q := invKernel D

/-- `α* = 1 + lim_{x → -∞} h(x) / (c̄ x)` (4.7), valued in `EReal` (it can be `-∞`); the limit
exists, so it equals the `liminf` taken here. -/
noncomputable def alphaStar (D : InventoryData) : EReal :=
  1 + liminf (fun x : ℝ => ((D.h x / (D.cbar * x) : ℝ) : EReal)) atBot

/-- `K`-convexity (Definition 4.1): for each `x ≤ y` and `λ ∈ (0, 1)`,
`f((1-λ)x + λy) ≤ (1-λ) f(x) + λ f(y) + λ K`. -/
def KConvex (K : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x ≤ y → ∀ l : ℝ, 0 < l → l < 1 →
    f ((1 - l) * x + l * y) ≤ (1 - l) * f x + l * f y + l * K

/-- Inf-compactness of a real function on `ℝ`: every level set `{x : f(x) ≤ λ}` is compact. -/
def InfCompact (f : ℝ → ℝ) : Prop :=
  ∀ l : ℝ, IsCompact {x | f x ≤ l}

/-- The `(s, S)` policy (Definition 4.2): order up to `S` if `x < s`, otherwise do not order. -/
noncomputable def sSPolicy (s S : ℝ) (x : ℝ) : ℝ≥0 :=
  if x < s then Real.toNNReal (S - x) else 0

/-- The variant of the `(s, S)` policy that also orders at `x = s` (Theorem 4.3). -/
noncomputable def sSPolicyLe (s S : ℝ) (x : ℝ) : ℝ≥0 :=
  if x ≤ s then Real.toNNReal (S - x) else 0

lemma measurable_sSPolicy (s S : ℝ) : Measurable (sSPolicy s S) :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_real_toNNReal.comp (measurable_const.sub measurable_id)) measurable_const

lemma measurable_sSPolicyLe (s S : ℝ) : Measurable (sSPolicyLe s S) :=
  Measurable.ite (measurableSet_le measurable_id measurable_const)
    (measurable_real_toNNReal.comp (measurable_const.sub measurable_id)) measurable_const

/-- The threshold `s = inf {x ≤ S : f(x) ≤ K + f(S)}` of (4.6). (`sInf` on `ℝ` is `0` on an
unbounded-below or empty set; the theorems that use it prove the set bounded below.) -/
noncomputable def lowerThreshold (f : ℝ → EReal) (K S : ℝ) : ℝ :=
  sInf {x : ℝ | x ≤ S ∧ f x ≤ (K : EReal) + f S}

/-- `G_α(x) = c̄ x + E[h(x - D)] + α E[v_α(x - D)]` (4.3), in `EReal`. -/
noncomputable def Galpha (D : InventoryData) (α : ℝ) (x : ℝ) : EReal :=
  ((D.cbar * x + ∫ d, D.h (x - d) ∂D.μ : ℝ) : EReal) +
    ((ENNReal.ofReal α * ∫⁻ d, vOpt (inventoryMDP D) α (x - d) ∂D.μ : ℝ≥0∞) : EReal)

/-- `H(x) = c̄ x + E[h(x - D)] + E[ũ(x - D)]` (4.9), for a given function `ũ`, in `EReal`. -/
noncomputable def Hfun (D : InventoryData) (u : ℝ → ℝ≥0∞) (x : ℝ) : EReal :=
  ((D.cbar * x + ∫ d, D.h (x - d) ∂D.μ : ℝ) : EReal) + ((∫⁻ d, u (x - d) ∂D.μ : ℝ≥0∞) : EReal)

/-- The inventory form of the optimality equation (4.10) at `x`, for `w = w̲`, a function `ũ`
and a stationary policy `ϕ`:
`w + ũ(x) = K I{ϕ(x) > 0} + H(x + ϕ(x)) - c̄x = min{min_{a ≥ 0}[K + H(x + a)], H(x)} - c̄x`,
with "min" read as: the middle term is `≤ K + H(x + a) - c̄x` for every `a ≥ 0` and
`≤ H(x) - c̄x`. -/
def InvACOE (D : InventoryData) (u : ℝ → ℝ≥0∞) (ϕ : ℝ → ℝ≥0) (x : ℝ) : Prop :=
  ((wLower (inventoryMDP D) : EReal) + (u x : EReal) =
      ((D.K * (if 0 < ϕ x then 1 else 0) : ℝ) : EReal) + Hfun D u (x + ϕ x) -
        ((D.cbar * x : ℝ) : EReal)) ∧
  (∀ a : ℝ≥0, (wLower (inventoryMDP D) : EReal) + (u x : EReal) ≤
      (D.K : EReal) + Hfun D u (x + a) - ((D.cbar * x : ℝ) : EReal)) ∧
  (wLower (inventoryMDP D) : EReal) + (u x : EReal) ≤ Hfun D u x - ((D.cbar * x : ℝ) : EReal)

/-! ### The renewal process of cumulative demands (p. 578) -/

/-- `S_n = D_1 + ⋯ + D_n` along a demand path `ω = (D_1, D_2, …)` (indexed from `0`). -/
def demandSum (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, ω j

/-- `N(t) = sup {n = 0, 1, … : S_n ≤ t}`, in `ℕ∞` (it is `+∞` on a null set). -/
noncomputable def renewalCount (t : ℝ) (ω : ℕ → ℝ) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : demandSum n ω ≤ t), (n : ℕ∞)

/-- The law of the i.i.d. demand sequence. -/
noncomputable def demandPath (D : InventoryData) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => D.μ)

/-- `E[N(t)]`. -/
noncomputable def meanRenewal (D : InventoryData) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (renewalCount t ω : ℝ≥0∞) ∂(demandPath D)

/-- `E[D]`. -/
noncomputable def meanDemand (D : InventoryData) : ℝ≥0∞ :=
  ∫⁻ d, ENNReal.ofReal d ∂D.μ

/-- `E_y(x) = E[h(x - S_{N(y)+1})]` (p. 578). On the null event `N(y) = ∞` the index is read
as `0 + 1`; this does not affect the expectation. -/
noncomputable def Ey (D : InventoryData) (y x : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (D.h (x - demandSum ((renewalCount y ω).toNat + 1) ω)) ∂(demandPath D)

/-- `E(x) = h(x) + E_{x - x*_L}(x)` (p. 578). -/
noncomputable def Efun (D : InventoryData) (xL x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (D.h x) + Ey D (x - xL) x

/-- The function `U` of (4.13), for an interval `[x*_L, x*_U]`:
`U(x) = K + c̄(x*_U - x)` if `x < x*_L`, and
`U(x) = K + c̄(x*_U - x*_L) + (E(x) + c̄ E[D])(1 + E[N(x - x*_L)])` if `x ≥ x*_L`. -/
noncomputable def Ubound (D : InventoryData) (xL xU x : ℝ) : ℝ≥0∞ :=
  if x < xL then ENNReal.ofReal (D.K + D.cbar * (xU - x))
  else ENNReal.ofReal (D.K + D.cbar * (xU - xL)) +
    (Efun D xL x + ENNReal.ofReal D.cbar * meanDemand D) * (1 + meanRenewal D (x - xL))

end FeinbergLiang.ACOE


