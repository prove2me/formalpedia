-- Prove2me | Definitions.Def_StochApproxDyn_Lyapunov_LyapunovFunction
-- name    : StochApproxDyn_Lyapunov_LyapunovFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:49:06.12999+00:00
-- url     : https://prove2.me/theorems/d4000718-dbb3-4167-9f14-2f978a28a0a1
-- title:
--   Lyapounov function for a compact invariant set $\Lambda$
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $(M,d)$ and let $\Lambda\subset M$ be a compact invariant set ($\Phi_t(\Lambda)=\Lambda$ for all $t\ge0$). A continuous function $V:M\to\mathbb R$ is a **Lyapounov function for $\Lambda$** if
--
--   1. for $x\in\Lambda$, the function $t\in\mathbb R_+\mapsto V(\Phi_t(x))$ is constant, i.e.
--   $$V(\Phi_t(x))=V(x)\qquad(t\ge0,\ x\in\Lambda);$$
--   2. for $x\in M\setminus\Lambda$, the function $t\in\mathbb R_+\mapsto V(\Phi_t(x))$ is **strictly** decreasing.
--
--   (When $\Lambda$ is the set of equilibria, the paper calls $V$ a *strict* Lyapounov function; that special case is not needed here.)
--
--   A Lyapounov function turns questions about the long-run behaviour of $\Phi$ (and of stochastic approximation processes that shadow it) into questions about the real numbers $V(\Lambda)$.
--
--   **Formalization Note** The standing assumptions of the definition — $\Lambda$ compact and invariant — are part of the predicate `IsLyapunovFunction Φ Λ V`, together with continuity of $V$. Strict decrease is `StrictAnti` in $t\in\mathbb R_{\ge0}$; a merely non-increasing condition would make every constant function a Lyapounov function.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 27, Section 6.2 "Lyapounov Functions and Stochastic Gradients", first paragraph

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_Invariance

open scoped NNReal

namespace StochApproxDyn.Lyapunov

/-- A *Lyapounov function* for `Λ` (Benaïm 1999, §6.2, p. 27). The definition is made for a
compact invariant set `Λ` of the semiflow `Φ`, and these standing assumptions are part of the
predicate: `Λ` is compact and invariant (`Φ_t(Λ) = Λ` for all `t ≥ 0`), `V : M → ℝ` is
continuous, `t ↦ V(Φ_t(x))` is constant on `ℝ₊` for `x ∈ Λ` (equivalently `V(Φ_t x) = V x`,
since `Φ_0 = id`), and `t ↦ V(Φ_t(x))` is strictly decreasing on `ℝ₊` for `x ∈ M \ Λ`. -/
def IsLyapunovFunction {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (Λ : Set M)
    (V : M → ℝ) : Prop :=
  IsCompact Λ ∧ StochApproxDyn.LimitSet.IsInvariantSet Φ Λ ∧ Continuous V ∧
    (∀ x ∈ Λ, ∀ t : ℝ≥0, V (Φ t x) = V x) ∧
    (∀ x ∉ Λ, StrictAnti (fun t : ℝ≥0 => V (Φ t x)))

end StochApproxDyn.Lyapunov


