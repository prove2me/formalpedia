-- Prove2me | Definitions.Def_TopkisRation_TimeMono_Model
-- name    : TopkisRation_TimeMono_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:39.730715+00:00
-- url     : https://prove2.me/theorems/c1888bad-35d5-4cf4-9b5a-3f7a3b3266fc
-- title:
--   §1, pp. 162–166 — the n-class rationing model, Assumptions (A)–(C), the recursion (1), the critical levels z̄_t^j and the rationing level policy (7)
-- statement:
--   This file sets up the single-procurement inventory model of Topkis (1968, §1) with $n$ classes of demand, class $n$ being the most important.
--
--   **Data.** A period is divided into $k$ intervals, indexed **backwards**: interval $t \in \{1,\dots,k\}$ has $t-1$ intervals after it, interval $k$ is the first and $t = 0$ is the end of the period. For each interval $t$ there are a backlogging fraction $a_t \ge 0$ (unsatisfied demand $u_t$ at the end of interval $t$ becomes the backlog $b_{t-1} = a_t u_t$ of the next interval; $a_t = 1$ is complete backlogging, $a_t = 0$ is none), a penalty vector $p_t = (p_t^1,\dots,p_t^n)$ charged as $p_t\cdot u_t$, a holding cost $h_t(\cdot)$ for stock on hand at the end of the interval, and the law $\mu_t$ of the demand vector $d_t = (d_t^1,\dots,d_t^n)$. At the end of interval 1 a salvage cost $v_1(z) + v_2(z - a_1\mathbf 1\cdot u_1)$ is incurred, and $c(w)$ is the cost of the single order placed at the start of interval $k$.
--
--   **Standing assumptions** (§1, p. 162), for $1 \le t \le k$:
--   1. $a_t \ge 0$;
--   2. (A) $h_t$ is continuous and convex on $[0,\infty)$;
--   3. (B) $v_1$ is convex and continuous on $[0,\infty)$, $v_2$ is convex and continuous on $\mathbb R$, and $\lim_{w\to-\infty} D^+v_2(w) > -\infty$;
--   4. (C) $0 \le p_t^1 \le p_t^2 \le \dots \le p_t^n$;
--   5. $\mu_t$ is a probability law on $[0,\infty)^n$ under which every class demand has a finite mean.
--
--   Here $D^+f(x) = \liminf_{\varepsilon\downarrow 0} \frac{f(x+\varepsilon)-f(x)}{\varepsilon}$ is the right derivative, an extended real number.
--
--   **The recursion (1)** (p. 163). With total demand $B = b + d_t$ at the start of interval $t$ and stock $z$,
--   $$
--   f_t(z,B) = \inf_{\substack{0 \le u \le B\\ w = z - \mathbf 1\cdot(B-u) \ge 0}} \bigl[p_t\cdot u + h_t(w) + g_{t-1}(w, a_t u)\bigr],
--   \qquad g_t(z,b) = \mathbb E\, f_t(z, b + d_t),
--   $$
--   with $g_0(z,b) = v_1(z) + v_2(z - \mathbf 1\cdot b)$. Demands of different intervals are independent, which is built into the recursion.
--
--   **Critical levels** (p. 166). With $\delta_j$ the $j$-th unit vector, $\bar z_t^j$ is $+\infty$ if $\varphi_t^j(w) = p_t^j w + h_t(w) + g_{t-1}(w, a_t w\delta_j)$ is strictly decreasing on $[0,\infty)$, and is the smallest minimizer of $\varphi_t^j$ on $[0,\infty)$ otherwise. The **rationing level policy** (7) sets $u^j = (B^{(j)} - z + \bar z_t^j)^+ \wedge B^j$ with $B^{(j)} = \sum_{i\ge j} B^i$: class $j$ demand is served from stock as long as the stock stays at or above $\bar z_t^j$.
--
--   These are the objects of the paper's Theorem 2: the critical levels of consecutive intervals.
--
--   **Formalization Note.** Classes are `Fin n` (paper class $j$ is index $j-1$); intervals are natural numbers counted backwards. $f_t$ is defined by the recursion (1) itself (the paper derives (1) from the policy-space infimum, "clearly we have"), using `sInf` and the Bochner integral; all statements restrict to $z \ge 0$, $B \ge 0$, where the paper's Lemma 2 shows the infimum is finite and attained. $D^+$ is an `EReal` liminf, so it can be $-\infty$. A critical level is a `WithTop ℝ` value characterized by the predicate `IsCriticalLevel`, with $\top$ for $+\infty$. Assumption (D) concerns only the ordering decision and is not part of `Standing`. "$\lim_{w\to-\infty}D^+v_2(w) > -\infty$" is encoded as "$D^+v_2$ is bounded below", which is equivalent for convex $v_2$ since $D^+v_2$ is nondecreasing. This file duplicates the model block of the other missions of this series, to be merged later.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), pp. 162–166, §1, Assumptions (A)–(C), (1), definition of z̄_t^j, (7)

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.TimeMono

open MeasureTheory Filter Topology

/-- Data of the single-procurement model of §1 (pp. 162–163). -/
structure Model (n : ℕ) where
  k : ℕ                          -- number of intervals in the period
  a : ℕ → ℝ                      -- a_t: b_{t-1} = a_t u_t
  p : ℕ → Fin n → ℝ              -- penalty p_t^j
  h : ℕ → ℝ → ℝ                  -- holding cost h_t
  v₁ : ℝ → ℝ                     -- salvage cost v₁(z)
  v₂ : ℝ → ℝ                     -- salvage cost v₂(z − a₁ Σ u₁ⁱ)
  c : ℝ → ℝ                      -- ordering cost c(w), w ≥ 0, at the start of interval k
  μ : ℕ → Measure (Fin n → ℝ)    -- law of the demand vector d_t

variable {n : ℕ}

/-- The standing assumptions of §1: (A), (B), (C), a_t ≥ 0, and the demand distributions
(probability laws on [0, ∞)ⁿ with finite means). -/
structure Model.Standing (M : Model n) : Prop where
  a_nonneg : ∀ t ∈ Finset.Icc 1 M.k, 0 ≤ M.a t
  h_convex : ∀ t ∈ Finset.Icc 1 M.k, ConvexOn ℝ (Set.Ici 0) (M.h t)          -- (A)
  h_cont : ∀ t ∈ Finset.Icc 1 M.k, ContinuousOn (M.h t) (Set.Ici 0)          -- (A)
  v₁_convex : ConvexOn ℝ (Set.Ici 0) M.v₁                                     -- (B)
  v₁_cont : ContinuousOn M.v₁ (Set.Ici 0)                                     -- (B)
  v₂_convex : ConvexOn ℝ Set.univ M.v₂                                        -- (B)
  v₂_cont : Continuous M.v₂                                                   -- (B)
  v₂_slope : ∃ L : ℝ, ∀ w, (L : EReal) ≤ TopkisRation.Levels.rightDeriv M.v₂ w                    -- (B)
  p_nonneg : ∀ t ∈ Finset.Icc 1 M.k, ∀ j, 0 ≤ M.p t j                         -- (C)
  p_mono : ∀ t ∈ Finset.Icc 1 M.k, Monotone (M.p t)                           -- (C)
  μ_prob : ∀ t ∈ Finset.Icc 1 M.k, IsProbabilityMeasure (M.μ t)
  μ_nonneg : ∀ t ∈ Finset.Icc 1 M.k, ∀ᵐ x ∂(M.μ t), 0 ≤ x
  μ_mean : ∀ t ∈ Finset.Icc 1 M.k, ∀ j, Integrable (fun x : Fin n → ℝ => x j) (M.μ t)

/-- The bracket of (1): p_t·u + h_t(w) + G(w, a_t u) with w = z − 1·(B − u). -/
def Model.obj (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ) (z : ℝ) (B u : Fin n → ℝ) : ℝ :=
  M.p t ⬝ᵥ u + M.h t (z - ∑ j, (B j - u j)) + G (z - ∑ j, (B j - u j)) (M.a t • u)

/-- The right-hand side of (1) with g_{t−1} replaced by `G`. -/
noncomputable def Model.stage (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ)
    (z : ℝ) (B : Fin n → ℝ) : ℝ :=
  sInf (M.obj t G z B '' TopkisRation.Levels.feasible z B)

/-- g_0(z, b) = v₁(z) + v₂(z − 1·b) and g_t(z, b) = E f_t(z, b + d_t). -/
noncomputable def Model.g (M : Model n) : ℕ → ℝ → (Fin n → ℝ) → ℝ
  | 0 => fun z b => M.v₁ z + M.v₂ (z - ∑ j, b j)
  | t + 1 => fun z b => ∫ x, M.stage (t + 1) (M.g t) z (b + x) ∂(M.μ (t + 1))

/-- f_t(z, B), for 1 ≤ t (at t = 0 it is junk and never used). -/
noncomputable def Model.f (M : Model n) (t : ℕ) (z : ℝ) (B : Fin n → ℝ) : ℝ :=
  M.stage t (M.g (t - 1)) z B

/-- The function whose smallest minimum is z̄_t^j: p_t^j w + h_t(w) + g_{t−1}(w, a_t w δ_j). -/
noncomputable def Model.levelObj (M : Model n) (t : ℕ) (j : Fin n) (w : ℝ) : ℝ :=
  M.p t j * w + M.h t w + M.g (t - 1) w (M.a t • w • Pi.single j 1)

end TopkisRation.TimeMono


