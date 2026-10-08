-- Prove2me | Definitions.Def_TopkisRation_Backlog_Model
-- name    : TopkisRation_Backlog_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:08.707594+00:00
-- url     : https://prove2.me/theorems/fc3ed56a-3901-49ec-bc15-cbc5a36cc2f7
-- title:
--   §1, pp. 162–167 — the n-class rationing model, Assumptions (A)–(C), the recursion (1), the critical levels z̄_t^j and the rationing level policy (7)
-- statement:
--   This module sets up the single-procurement inventory model of Topkis (1968, §1), in which one stock of a single product serves $n$ classes of demand, class $n$ being the most important.
--
--   **Data.** A period is divided into $k$ intervals, indexed backwards: interval $t$ is followed by $t-1$ further intervals, interval $k$ is the first and $t = 0$ marks the end of the period. For each interval $t$ there are
--
--   1. a constant $a_t \ge 0$: a fraction $a_t$ of the demand left unsatisfied at the end of interval $t$ is backlogged into interval $t-1$, so $b_{t-1} = a_t u_t$ ($a_t = 1$ is complete backlogging, $a_t = 0$ no backlogging);
--   2. penalties $p_t = (p_t^1,\dots,p_t^n)$ per unit of unsatisfied demand of each class, and a holding cost $h_t(\cdot)$ on the stock left at the end of the interval;
--   3. the law $\mu_t$ of the demand vector $d_t = (d_t^1,\dots,d_t^n)$ arriving in interval $t$; demands in different intervals are independent.
--
--   At the end of interval 1 a salvage cost $v_1(z) + v_2(z - a_1\,\mathbf 1\cdot u_1)$ is incurred, and $c(w)$ is the cost of the single order $w \ge 0$ placed at the start of interval $k$.
--
--   **Standing assumptions.** For every interval $t \in \{1,\dots,k\}$: $a_t \ge 0$; (A) $h_t$ is convex and continuous on $[0,\infty)$; (C) $0 \le p_t^1 \le p_t^2 \le \dots \le p_t^n$; $\mu_t$ is a probability law on $[0,\infty)^n$ with finite means. (B) $v_1$ is convex and continuous on $[0,\infty)$, $v_2$ is convex and continuous on $\mathbb R$, and $\lim_{w\to-\infty} D^+v_2(w) > -\infty$.
--
--   **The recursion (1).** With $g_0(z,b) = v_1(z) + v_2(z - \mathbf 1\cdot b)$ and, for $t \ge 1$,
--   $$
--   f_t(z,B) = \inf_{\substack{0 \le u \le B\\ w = z - \mathbf 1\cdot(B-u) \ge 0}} \big[\,p_t\cdot u + h_t(w) + g_{t-1}(w, a_t u)\,\big],\qquad g_t(z,b) = \mathbb E\, f_t(z, b + d_t),
--   $$
--   $f_t(z,B)$ is the minimal expected cost of the last $t$ intervals from stock $z$ and outstanding demand vector $B$.
--
--   **Critical rationing levels and the rationing level policy.** For a class $j$, $\bar z_t^j = +\infty$ if $w \mapsto p_t^j w + h_t(w) + g_{t-1}(w, a_t w\,\delta_j)$ is strictly decreasing on $[0,\infty)$, and otherwise $\bar z_t^j$ is the smallest minimizer of that function on $[0,\infty)$; here $\delta_j$ is the $j$-th unit vector. The rationing level policy (7) leaves $u^j = (B^{(j)} - z + \bar z_t^j)^+ \wedge B^j$ of class $j$ unsatisfied, where $B^{(j)} = \sum_{i \ge j} B^i$ (and $u^j = B^j$ if $\bar z_t^j = +\infty$).
--
--   These objects are the vocabulary of every result of the paper: the critical levels $\bar z_t^j$ are the quantities whose structure Theorems 1–3 describe.
--
--   **Formalization Note** Classes are `Fin n`, class $j$ of the paper being index $j-1$; intervals are natural numbers counted backwards. $f_t$ is defined by the recursion (1), the dynamic program the paper writes down, not as an infimum over policies; $\inf$ is `sInf` over reals and $\mathbb E$ the Bochner integral, and every statement using them restricts to $z \ge 0$, $B \ge 0$. $D^+$ is the right derivative valued in extended reals (a liminf of difference quotients), and the limit in (B) is read as "$D^+v_2$ is bounded below", which is equivalent for convex $v_2$. $\bar z_t^j$ takes values in $\mathbb R \cup \{+\infty\}$ and is described by the predicate `IsCriticalLevel` rather than computed. $f_0$ is junk and never used. The ordering assumption (D) and the cost $c$ play no role here.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), pp. 162–167, §1, Assumptions (A)–(C), (1), definition of z̄_t^j (p. 166), (7)

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.Backlog

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

end TopkisRation.Backlog


