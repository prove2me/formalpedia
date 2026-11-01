-- Prove2me | Definitions.Def_PConeEB_IsConsistentEBF
-- name    : PConeEB_IsConsistentEBF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:52.810056+00:00
-- url     : https://prove2.me/theorems/08ca5adc-0ef3-4a41-b446-799c39d36feb
-- title:
--   Consistent error bound function
-- statement:
--   Let $C_1,\dots,C_m\subseteq\mathcal E$ be closed convex sets with $C:=\bigcap_{i=1}^mC_i\ne\emptyset$. A function $\Phi:\mathbb R_+\times\mathbb R_+\to\mathbb R_+$ is a **consistent error bound function** for $C_1,\dots,C_m$ if:
--
--   1. $\operatorname{dist}(x,C)\le\Phi\bigl(\max_{1\le i\le m}\operatorname{dist}(x,C_i),\|x\|\bigr)$ for all $x\in\mathcal E$;
--   2. for any fixed $b\ge0$, the function $\Phi(\cdot,b)$ is nondecreasing on $\mathbb R_+$, right-continuous at $0$, and $\Phi(0,b)=0$;
--   3. for any fixed $a\ge0$, the function $\Phi(a,\cdot)$ is nondecreasing on $\mathbb R_+$.
--
--   This framework includes Hölderian error bounds as a special case, and it allows a tightness statement against all error bounds and not only against Hölderian ones.
--
--   **Formalization Note** $\Phi$ is a function on $\mathbb R\times\mathbb R$ with nonnegativity and monotonicity on nonnegative arguments. The maximum is the real supremum over a nonempty finite index type. Closedness, convexity and nonemptiness are properties of the sets at the point of use.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Definition 3.2, pp.13–14

import Mathlib

namespace PConeEB

/-- Definition 3.2 (consistent error bound functions). `Φ : ℝ₊ × ℝ₊ → ℝ₊` is a consistent error
bound function for `C₁, …, C_m` if (i) `dist(x, C) ≤ Φ(max_i dist(x, C_i), ‖x‖)` for all `x`, with
`C = ⋂ i, C_i`; (ii) for each `b ≥ 0`, `Φ(·, b)` is nondecreasing on `ℝ₊`, right-continuous at `0`
and `Φ(0, b) = 0`; (iii) for each `a ≥ 0`, `Φ(a, ·)` is nondecreasing on `ℝ₊`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Definition 3.2, pp.13–14.

**Formalization Note.** `Φ` is a function `ℝ → ℝ → ℝ`, with its conditions on nonnegative arguments
only. The real `⨆` runs over a nonempty finite index type, so it is the maximum. Right-continuity
at `0` is the limit along `𝓝[>] 0` together with `Φ 0 b = 0`. The paper's closed convex `C_i` with
nonempty intersection are properties of the sets at the point of use. -/
structure IsConsistentEBF {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι] (C : ι → Set E) (Φ : ℝ → ℝ → ℝ) : Prop where
  nonneg : ∀ a b, 0 ≤ a → 0 ≤ b → 0 ≤ Φ a b
  error_bound : ∀ x : E,
    Metric.infDist x (⋂ i, C i) ≤ Φ (⨆ i, Metric.infDist x (C i)) ‖x‖
  mono_left : ∀ b, 0 ≤ b → MonotoneOn (fun a => Φ a b) (Set.Ici 0)
  tendsto_zero : ∀ b, 0 ≤ b →
    Filter.Tendsto (fun a => Φ a b) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  zero_left : ∀ b, 0 ≤ b → Φ 0 b = 0
  mono_right : ∀ a, 0 ≤ a → MonotoneOn (Φ a) (Set.Ici 0)

end PConeEB


