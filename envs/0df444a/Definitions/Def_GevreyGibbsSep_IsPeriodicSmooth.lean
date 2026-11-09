-- Prove2me | Definitions.Def_GevreyGibbsSep_IsPeriodicSmooth
-- name    : GevreyGibbsSep_IsPeriodicSmooth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:45.748848+00:00
-- url     : https://prove2.me/theorems/57d82c39-2234-4fc8-951a-646de299a50b
-- title:
--   $2\pi$-periodic $C^\infty$ functions on $\mathbb R^d$
-- statement:
--   A function $V:\mathbb R^d\to\mathbb R$ is **periodic and smooth** if it is $C^\infty$ and $V(x+2\pi e_i)=V(x)$ for every $x\in\mathbb R^d$ and every coordinate direction $e_i$. These are the functions $f\in C^\infty(\mathbb R^d)$, $2\pi$-periodic, to which Definition 1 applies.
--
--   **Formalization Note** $C^\infty$ is `ContDiff ℝ (⊤ : ℕ∞)`, infinitely differentiable, not real-analytic.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition 1, p.5

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- `V : ℝ^d → ℝ` is a `2π`-periodic `C^∞` function (arXiv:2608.24527 (sha256 d4fd40eb…),
Definition 1, p.5: "a 2π-periodic smooth function f ∈ C^∞(ℝ^d)").

**Formalization Note** `C^∞` is `ContDiff ℝ (⊤ : ℕ∞)` (not the analytic `ω`). -/
def IsPeriodicSmooth {d : ℕ} (V : (Fin d → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧
    ∀ (x : Fin d → ℝ) (i : Fin d), V (x + Pi.single i (2 * Real.pi)) = V x

end GevreyGibbsSep


