-- Prove2me | Definitions.Def_ChenWhitt93_JumpDiffusion_Reflection
-- name    : ChenWhitt93_JumpDiffusion_Reflection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:46:45.313987+00:00
-- url     : https://prove2.me/theorems/e5998399-b0aa-4623-aa17-abbb1ca40524
-- title:
--   Section 2, (2.1)–(2.3) — the oblique reflection map associated with $Q$ on $[0,\infty)$
-- statement:
--   Let $J\ge 1$ and let $P$ be a $J\times J$ matrix. $P$ is **transient substochastic** if all its entries are nonnegative, every row sum is at most $1$, and $P^k\to 0$ as $k\to\infty$. This is the assumption the paper places on the routing matrix, in (4.8), and on $Q^{\mathsf t}$, on p. 337.
--
--   Given a $J\times J$ matrix $Q$ and a path $x:[0,\infty)\to\mathbb R^J$, a pair of paths $(y,z)$ is the **reflection** $(\psi(x),\phi(x))$ of $x$ associated with $Q$ when
--
--   1. (2.1) for every $t\ge 0$,
--   $$
--   z(t)=x(t)+(I-Q)\,y(t)\ \ge 0;
--   $$
--   2. (2.2) each $y_j$ is nondecreasing and right-continuous on $[0,\infty)$ with $y_j(0)\ge 0$;
--   3. (2.3) $y_j$ increases only when $z_j=0$:
--   $$
--   \int_{[0,\infty)} z_j(t)\,dy_j(t)=0,\qquad 1\le j\le J,
--   $$
--   where $dy_j$ is the Lebesgue–Stieltjes measure of $y_j$ (extended by $0$ to negative times). An initial jump $y_j(0)>0$ is charged to the time $0$.
--
--   In Section 4 the reflection map with $Q=P^{\mathsf t}$ turns the limiting free process $\hat X$ into the limiting queue length $\hat Z=\phi(\hat X)$ and the scaled limiting idle time $\operatorname{diag}(\mu)\hat Y=\psi(\hat X)$.
--
--   **Formalization Note** The page's (2.2) requires $y_j(0)=0$. Then (2.1) forces $x(0)\ge 0$, and the map is undefined for paths starting outside the orthant. The limit $\hat X$ of Theorem 4.1 can start outside it: when $\hat D(0)>0$ (Remark (4.2)), $[I-P^{\mathsf t}]\operatorname{diag}(\mu)\hat D(0)$ has negative downstream coordinates. The definition therefore allows $y_j(0)\ge 0$, with the atom at $0$ subject to (2.3). This is the extension given by (2.4) ($y=(Qy-x)^{\uparrow}\vee 0$ with the running supremum starting at time $0$), and when $x(0)\ge 0$ it forces $y(0)=0$, so it agrees with the page. Conditions (2.2)–(2.3) are encoded by asking for a `StieltjesFunction` equal to $y_j$ on $[0,\infty)$ and to $0$ on $(-\infty,0)$ whose measure gives zero mass to $\{t\ge 0: z_j(t)>0\}$. This definition duplicates, on $[0,\infty)$, the reflection map of mission 1 of this series, which is drafted concurrently.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 337, Eqs. (2.1)–(2.4) and the standing assumption on Q; p. 348, (4.8) ("the matrix P is substochastic with Pᵏ → 0 as k → ∞")

import Mathlib

namespace ChenWhitt93.JumpDiffusion

open Filter Topology MeasureTheory Matrix

/-!
Chen and Whitt (1993), Section 2, p. 337: the oblique reflection map associated with `Q`,
on paths over `[0, ∞)`, and the standing assumptions on the routing matrix (Section 4, (4.8)).
-/

/-- `P` is a substochastic matrix with `Pᵏ → 0` (p. 337 for `Qᵗ`; (4.8) for `P`): nonnegative
entries, row sums at most `1`, and powers tending to `0`. -/
def IsTransientSubstochastic {J : ℕ} (P : Matrix (Fin J) (Fin J) ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ (∀ i, ∑ j, P i j ≤ 1) ∧ Tendsto (fun k : ℕ => P ^ k) atTop (𝓝 0)

/-- Eqs. (2.1)–(2.3) on `[0, ∞)`: `(y, z)` is the pair `(ψ(x), φ(x))` of the reflection map
associated with `Q`.
* (2.1) `z(t) = x(t) + (I − Q) y(t) ≥ 0` for `t ≥ 0`;
* (2.2)–(2.3) for each `j` the function equal to `yⱼ` on `[0, ∞)` and to `0` on `(−∞, 0)` is a
  Stieltjes function (nondecreasing, right-continuous; so `yⱼ(0) ≥ 0`) whose Lebesgue–Stieltjes
  measure gives zero mass to `{t ≥ 0 : zⱼ(t) > 0}`, i.e. `∫_{[0,∞)} zⱼ dyⱼ = 0`.
The page's (2.2) also requires `yⱼ(0) = 0`; here an initial jump `yⱼ(0) > 0` is allowed (it is
charged by (2.3), so it can occur only where `zⱼ(0) = 0`). This is the extension of the map given by
(2.4) to paths with `x(0) ∉ ℝ₊ⁿ`; when `x(0) ≥ 0` it forces `y(0) = 0` and agrees with the page. -/
def IsReflection {J : ℕ} (Q : Matrix (Fin J) (Fin J) ℝ) (x y z : ℝ → Fin J → ℝ) : Prop :=
  (∀ t, 0 ≤ t → z t = x t + (1 - Q) *ᵥ y t ∧ 0 ≤ z t) ∧
  ∀ j, ∃ F : StieltjesFunction ℝ, (∀ t, F t = if t < 0 then 0 else y t j) ∧
    F.measure {t | 0 ≤ t ∧ 0 < z t j} = 0

end ChenWhitt93.JumpDiffusion


