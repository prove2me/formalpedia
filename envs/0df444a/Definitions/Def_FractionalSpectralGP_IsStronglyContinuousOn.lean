-- Prove2me | Definitions.Def_FractionalSpectralGP_IsStronglyContinuousOn
-- name    : FractionalSpectralGP_IsStronglyContinuousOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:54.883535+00:00
-- url     : https://prove2.me/theorems/05bbaa93-a5c6-4710-a5a7-fcf0344ed4c0
-- title:
--   Continuity in the strong topology of $S_{-1}$ on $[a,b]$
-- statement:
--   A function $Y:[a,b]\to S_{-1}$ is **continuous in the strong topology of $S_{-1}$** if, for every $t\in[a,b]$ and every bounded set $B\subset S_1$,
--
--   $$
--   \sup_{g\in B}\big|\langle Y(s)-Y(t),g\rangle\big|\longrightarrow0\qquad(s\to t,\ s\in[a,b]).
--   $$
--
--   This is the hypothesis on the integrand in Theorem 7.1.
--
--   **Formalization Note** The strong topology is the strong dual topology of $S_{-1}=S_1'$ (uniform convergence on bounded subsets of $S_1$); for this DFS space it coincides with the inductive limit topology.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Theorem 7.1, p.24

import Mathlib
import Definitions.Def_FractionalSpectralGP_IsBoundedS1
import Definitions.Def_FractionalSpectralGP_dualPair

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- `Y : [a, b] → S_{−1}` is continuous in the strong topology of `S_{−1}`
(Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, Theorem 7.1, p.24): at every `t ∈ [a, b]`, `⟨Y(s) − Y(t), g⟩ → 0` as `s → t`
in `[a, b]`, uniformly for `g` in each bounded subset of `S₁`.

**Formalization Note.** The strong topology of `S_{−1}` is the strong dual topology of `S_{−1} = S₁'`
(uniform convergence on bounded subsets of `S₁`); for this DFS space it coincides with the
inductive limit topology of p.11. -/
def IsStronglyContinuousOn (Y : ℝ → (ℕ →₀ ℕ) → ℂ) (a b : ℝ) : Prop :=
  ∀ t ∈ Set.Icc a b, ∀ B : Set ((ℕ →₀ ℕ) → ℂ), IsBoundedS1 B → ∀ ε > 0, ∃ δ > 0,
    ∀ s ∈ Set.Icc a b, |s - t| < δ → ∀ g ∈ B, ‖dualPair (Y s - Y t) g‖ ≤ ε

end FractionalSpectralGP


