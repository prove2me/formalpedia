-- Prove2me | Definitions.Def_KurtzProtter91_Integrals_Skorohod
-- name    : KurtzProtter91_Integrals_Skorohod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:41:55.732392+00:00
-- url     : https://prove2.me/theorems/bf86a616-3b58-4942-9b96-a68854fecc58
-- title:
--   Pp. 1036–1039 — cadlag paths, the time changes Λ, Skorohod convergence on D_E[0, ∞), J_δ (2.1), step paths and left-point Riemann sums (1.7)
-- statement:
--   This file fixes the deterministic objects of Kurtz and Protter (1991). Time is $[0,\infty)$ and $E$ is a metric space.
--
--   1. **Cadlag paths.** A path $x:[0,\infty)\to E$ is *cadlag* if it is right-continuous at every $t\ge 0$ and has a left limit $x(t-)$ at every $t>0$ (p. 1036). The paper's $D_E[0,\infty)$ is the set of cadlag paths. We set $x(0-)=x(0)$, and for vector-valued paths the jump is $\Delta x(t)=x(t)-x(t-)$, so $\Delta x(0)=0$.
--   2. **Time changes.** $\Lambda$ is the collection of continuous, strictly increasing functions mapping $[0,\infty)$ onto $[0,\infty)$ (p. 1037).
--   3. **Skorohod convergence** (pp. 1037–1038). Cadlag paths $x_n$ converge to a cadlag path $x$ in the Skorohod topology if there are $\lambda_n\in\Lambda$ such that
--   $$x_n\circ\lambda_n(t)\to x(t)\quad\text{and}\quad \lambda_n(t)\to t\qquad\text{uniformly for } t \text{ in bounded intervals.}$$
--   For a product space $E_1\times E_2$ this is convergence of the *pair* $(x_n,y_n)\to(x,y)$ with **one** time change $\lambda_n$ for both components, which is strictly stronger than convergence of each component (Example 1.1, p. 1037).
--   4. **The jump functional $J_\delta$** (2.1), p. 1039. For $\delta\in(0,\infty]$ let $h_\delta(r)=(1-\delta/r)^+$ ($h_\infty=0$) and, for a cadlag $x$ with values in $\mathbb R^m$,
--   $$J_\delta(x)(t)=\sum_{s\le t}h_\delta\big(|x(s)-x(s-)|\big)\,\big(x(s)-x(s-)\big),$$
--   where $|v|=\sum_i|v_i|$. At $r=0$ the standalone coefficient $h_\delta$ is set to zero, since the displayed quotient is undefined there. Only jumps with $|\Delta x(s)|>\delta$ contribute, and a cadlag path has finitely many of them in $[0,t]$.
--   5. **Step paths** (p. 1038). A real path is *piecewise constant* if it is cadlag, has finitely many discontinuities in every bounded interval, and is constant on every interval $[s,t]$ with no discontinuity in $(s,t]$.
--   6. **Left-point Riemann sums and the pathwise integral** (1.7), p. 1036. For a partition $0=t_0<t_1<\dots<t_N=t$ of $[0,t]$, a $k\times m$-matrix-valued $x$ and an $\mathbb R^m$-valued $y$, the left-point sum is $\sum_i x(t_i)\big(y(t_{i+1})-y(t_i)\big)$ (matrix–vector product). We say $z(t)=\int_0^t x(s-)\,dy(s)$ if, for every $t$ and every sequence of partitions of $[0,t]$ whose mesh $\max_i(t_{i+1}-t_i)$ tends to zero, the left-point sums converge to $z(t)$. The real-valued case is $k=m=1$.
--
--   These objects are shared by every statement of the mission: Lemma 2.1, the continuity of $J_\delta$, Lemma 6.2, the step approximation of §6, (1.12)–(1.13), (2.2), and, through the stochastic integral, Theorem 2.2.
--
--   **Formalization Note** Paths are functions `ℝ≥0 → E`; "cadlag" is a predicate, and every statement assumes it where the paper does. The left limit is Mathlib's `Function.leftLim`, which returns $x(0)$ at $t=0$ and is junk only where no left limit exists, i.e. never for a cadlag path. $J_\delta$ is a `finsum` over the jump times with $|\Delta x(s)|>\delta$; it is an honest finite sum for cadlag $x$ (for a non-cadlag $x$ it is junk, and no statement uses it there). The norm $|v|=\sum_i|v_i|$ in (2.1) is the paper's convention for vectors (p. 1049); (2.1) itself does not fix it. Uniform convergence on bounded intervals means uniform convergence on $[0,T]$ for every $T$. Product spaces carry the max metric; Skorohod convergence does not depend on the choice of product metric. The pathwise integral quantifies over all partitions, not only dyadic ones, as (1.7) does.
-- source:
--   Kurtz and Protter, Weak Limit Theorems for Stochastic Integrals and Stochastic Differential Equations, Ann. Probab. 19 (1991), p. 1036 (cadlag processes, (1.7)), pp. 1037–1038 (Λ and the Skorohod topology), p. 1038 (piecewise constant y_n, before (1.12)), p. 1039 ((2.1)), p. 1049 (|x| = Σ|x_i|)

import Mathlib

open Filter Topology
open scoped NNReal ENNReal

namespace KurtzProtter91.Integrals

/-- A **cadlag path** `x : [0, ∞) → E` (Kurtz–Protter 1991, p. 1036): right-continuous at every
`t ≥ 0`, with a left limit `x(t −)` at every `t > 0`. -/
def IsCadlag {E : Type*} [TopologicalSpace E] (x : ℝ≥0 → E) : Prop :=
  (∀ t : ℝ≥0, ContinuousWithinAt x (Set.Ici t) t) ∧
    ∀ t : ℝ≥0, 0 < t → ∃ a : E, Tendsto x (𝓝[<] t) (𝓝 a)

/-- The left limit `x(t −)`. This is Mathlib's `Function.leftLim`: the limit of `x` along
`𝓝[<] t`. At `t = 0` (which has no points to its left) it is `x 0`, i.e. the convention
`x(0 −) = x(0)`. For a cadlag path this is the genuine left limit at every `t > 0`. -/
noncomputable abbrev leftLim {E : Type*} [TopologicalSpace E] (x : ℝ≥0 → E) (t : ℝ≥0) : E :=
  Function.leftLim x t

/-- The jump `Δx(t) = x(t) − x(t −)` of a path in an additive group (so `Δx(0) = 0`). -/
noncomputable def jump {E : Type*} [TopologicalSpace E] [Sub E] (x : ℝ≥0 → E) (t : ℝ≥0) : E :=
  x t - leftLim x t

/-- The jump times `{s ≤ T : y(s) ≠ y(s −)}` of a real path in `[0, T]`. -/
noncomputable def jumpTimes (y : ℝ≥0 → ℝ) (T : ℝ≥0) : Set ℝ≥0 :=
  {s | s ≤ T ∧ jump y s ≠ 0}

/-- A **piecewise constant** (step) path (p. 1038): cadlag, with finitely many discontinuities in
every bounded interval, and constant on every interval `[s, t]` containing no discontinuity in
`(s, t]`. -/
def IsStepPath (y : ℝ≥0 → ℝ) : Prop :=
  IsCadlag y ∧ (∀ T : ℝ≥0, (jumpTimes y T).Finite) ∧
    ∀ s t : ℝ≥0, s ≤ t → (∀ u : ℝ≥0, s < u → u ≤ t → jump y u = 0) → y t = y s

/-- `Λ` (p. 1037): continuous, strictly increasing maps of `[0, ∞)` onto `[0, ∞)`. -/
def IsTimeChange (l : ℝ≥0 → ℝ≥0) : Prop :=
  Continuous l ∧ StrictMono l ∧ Function.Surjective l

/-- `x_n(t) → x(t)` uniformly for `t` in bounded intervals: uniformly on `[0, T]` for every `T`. -/
def TendstoUniformlyOnBounded {E : Type*} [MetricSpace E] (xs : ℕ → ℝ≥0 → E) (x : ℝ≥0 → E) :
    Prop :=
  ∀ T : ℝ≥0, TendstoUniformlyOn xs x atTop (Set.Icc 0 T)

/-- **Skorohod (J1) convergence** on `D_E[0, ∞)` (pp. 1037–1038): the cadlag paths `x_n` converge
to the cadlag path `x` if there are `λ_n ∈ Λ` with `x_n ∘ λ_n(t) → x(t)` and `λ_n(t) → t`
uniformly for `t` in bounded intervals. For a product space `E₁ × E₂` this is convergence of the
pair with one time change for both components. -/
def SkorohodTendsto {E : Type*} [MetricSpace E] (xs : ℕ → ℝ≥0 → E) (x : ℝ≥0 → E) : Prop :=
  (∀ n, IsCadlag (xs n)) ∧ IsCadlag x ∧
    ∃ l : ℕ → ℝ≥0 → ℝ≥0, (∀ n, IsTimeChange (l n)) ∧
      TendstoUniformlyOnBounded (fun n => xs n ∘ l n) x ∧ TendstoUniformlyOnBounded l id

/-- The norm `|v| = ∑ᵢ |vᵢ|` on `ℝ^m` (the paper's convention for vectors, p. 1049). -/
def l1norm {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  ∑ i, |v i|

/-- `h_δ(r) = (1 − δ/r)^+` of (2.1), for `δ ∈ (0, ∞]`; `h_∞ = 0`.
At `r = 0`, where the quotient in the displayed formula is undefined, the coefficient is zero. -/
noncomputable def hDelta (δ : ℝ≥0∞) (r : ℝ) : ℝ :=
  if δ = ⊤ ∨ r = 0 then 0 else max (1 - δ.toReal / r) 0

/-- The functional `J_δ` of (2.1), p. 1039:
`J_δ(x)(t) = ∑_{s ≤ t} h_δ(|x(s) − x(s −)|)(x(s) − x(s −))`. Only jumps with `|Δx(s)| > δ` have
`h_δ ≠ 0`, so the sum is written over those `s ≤ t`; for a cadlag `x` there are finitely many of
them, and the `finsum` is an honest finite sum. -/
noncomputable def Jdelta {m : ℕ} (δ : ℝ≥0∞) (x : ℝ≥0 → Fin m → ℝ) (t : ℝ≥0) : Fin m → ℝ :=
  ∑ᶠ (s : ℝ≥0) (_ : s ≤ t ∧ δ < ENNReal.ofReal (l1norm (jump x s))),
    hDelta δ (l1norm (jump x s)) • jump x s

/-- A partition `0 = t_0 < t_1 < ⋯ < t_N = t` of `[0, t]`. -/
structure Partition (t : ℝ≥0) where
  N : ℕ
  pt : Fin (N + 1) → ℝ≥0
  strictMono : StrictMono pt
  pt_zero : pt 0 = 0
  pt_last : pt (Fin.last N) = t

/-- The mesh `max_i (t_{i+1} − t_i)` of a partition. -/
def Partition.mesh {t : ℝ≥0} (p : Partition t) : ℝ≥0 :=
  Finset.univ.sup fun i : Fin p.N => p.pt i.succ - p.pt i.castSucc

/-- The left-point Riemann sum of (1.7), `∑_i X(t_i)(Y(t_{i+1}) − Y(t_i))`, for a
`k × m`-matrix-valued integrand and an `ℝ^m`-valued integrator (matrix–vector product). -/
def riemannSum {k m : ℕ} {t : ℝ≥0} (p : Partition t) (x : ℝ≥0 → Fin k → Fin m → ℝ)
    (y : ℝ≥0 → Fin m → ℝ) : Fin k → ℝ :=
  fun a => ∑ i : Fin p.N, ∑ j, x (p.pt i.castSucc) a j * (y (p.pt i.succ) j - y (p.pt i.castSucc) j)

/-- Pathwise version of (1.7): `z(t) = ∫_0^t x(s −) dy(s)` is the limit of the left-point Riemann
sums along every sequence of partitions of `[0, t]` whose mesh tends to zero, for every `t`. -/
def HasLeftIntegral {k m : ℕ} (x : ℝ≥0 → Fin k → Fin m → ℝ) (y : ℝ≥0 → Fin m → ℝ)
    (z : ℝ≥0 → Fin k → ℝ) : Prop :=
  ∀ (t : ℝ≥0) (ps : ℕ → Partition t), Tendsto (fun n => (ps n).mesh) atTop (𝓝 0) →
    Tendsto (fun n => riemannSum (ps n) x y) atTop (𝓝 (z t))

/-- The real-valued case of `HasLeftIntegral` (`k = m = 1`): `z(t) = ∫_0^t x(s −) dy(s)`. -/
def HasLeftIntegralR (x y z : ℝ≥0 → ℝ) : Prop :=
  HasLeftIntegral (k := 1) (m := 1) (fun t _ _ => x t) (fun t _ => y t) (fun t _ => z t)

end KurtzProtter91.Integrals


