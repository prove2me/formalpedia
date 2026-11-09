-- Prove2me | Definitions.Def_MinSumFPT_Delta
-- name    : MinSumFPT_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:59.327536+00:00
-- url     : https://prove2.me/theorems/0a03f204-e620-4cbd-a8a2-930cb8f16cd2
-- title:
--   Unit vectors, $\mu_C$, $\Delta_C$ and $\mathrm{core}_\alpha(C)$
-- statement:
--   Let $\|\cdot\|_{W_1}$ be the transportation norm on zero-sum vectors in $\mathbb R^A$: $\|f\|_{W_1}$ is the least cost $\sum_{x,y}F(x,y)\,d(x,y)$ of a nonnegative flow $F$ with $f=\sum_{x,y}F(x,y)(e_y-e_x)$, where $e_x$ is the unit vector of the point $x$.
--
--   For a nonempty cluster $C\subseteq A$, $\mu_C$ is the uniform distribution on $C$ (the vector with entries $1/|C|$ on $C$ and $0$ elsewhere),
--
--   $$
--   \Delta_C=\frac1{|C|}\sum_{x\in C}\|e_x-\mu_C\|_{W_1},
--   \qquad
--   \mathrm{core}_\alpha(C)=\{x\in C:\ \|e_x-\mu_C\|_{W_1}\le\alpha\,\Delta_C\}.
--   $$
--
--   By Lemma 3, $\mathrm{cost}(C)=|C|^2\Delta_C$, so $\Delta_C$ is the cost of $C$ per ordered pair; $\mathrm{core}_\alpha(C)$ holds the points that are at most $\alpha$ times the average distance from the cluster's center.
--
--   **Formalization Note** The norm is the published `PerturbedWF.transNorm` (flow form). For a metric it is the norm whose unit ball is $\mathrm{conv}\{(e_x-e_y)/d(x,y)\}$ (p.7); for a pseudometric that formula divides by $0$ and the flow form is its extension. $\mu_C$ and $\Delta_C$ are used only for nonempty $C$.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), §2.1, pp.7–8 (W₁(A,d), Lemma 3, core_α(C))

import Mathlib
import Definitions.Def_PerturbedWF_transNorm

namespace MinSumFPT

/-!
# Unit vectors, the uniform distribution µ_C, the cluster cost parameter Δ_C and core_α(C)

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), §2.1, pp.7–8: the space W₁(A, d) with the transportation norm, Lemma 3 (µ_C the uniform
distribution on C, Δ_C = (1/|C|) ∑_{x∈C} ‖e_x − µ_C‖_{W₁}) and core_α(C) = {x ∈ C : ‖e_x − µ_C‖_{W₁}
≤ α ⋅ Δ_C}.

This module bundles `unitVec`, `centroid`, `Delta`, `core`.

**Formalization Note.** The norm ‖·‖_{W₁} is the published `PerturbedWF.transNorm d`, the least cost
∑ F(x,y) d(x,y) of a nonnegative flow F with f = ∑ F(x,y)(e_y − e_x). For a metric this is the norm
whose unit ball is conv{(e_x − e_y)/d(x,y)} (p.7); for a pseudometric (distance 0 allowed between
distinct points) the unit-ball formula divides by 0 and the flow form is its extension. Every vector
it is applied to here has coordinate sum 0. `centroid C` and `Delta d C` divide by `|C|` and are used
only for nonempty `C` (the statements assume it). -/

/-- The unit vector `e_x ∈ ℝ^A`. -/
noncomputable def unitVec {n : ℕ} (x : Fin n) : Fin n → ℝ := Pi.single x 1

/-- `µ_C`, the uniform distribution on the cluster `C` (as a vector in `ℝ^A`). -/
noncomputable def centroid {n : ℕ} (C : Finset (Fin n)) : Fin n → ℝ :=
  fun y => if y ∈ C then 1 / (C.card : ℝ) else 0

/-- `Δ_C = (1/|C|) ∑_{x∈C} ‖e_x − µ_C‖_{W₁}`. -/
noncomputable def Delta {n : ℕ} (d : Fin n → Fin n → ℝ) (C : Finset (Fin n)) : ℝ :=
  (1 / (C.card : ℝ)) * ∑ x ∈ C, PerturbedWF.transNorm d (unitVec x - centroid C)

/-- `core_α(C) = {x ∈ C : ‖e_x − µ_C‖_{W₁} ≤ α ⋅ Δ_C}`. -/
noncomputable def core {n : ℕ} (d : Fin n → Fin n → ℝ) (α : ℝ) (C : Finset (Fin n)) :
    Finset (Fin n) :=
  C.filter (fun x => PerturbedWF.transNorm d (unitVec x - centroid C) ≤ α * Delta d C)

end MinSumFPT


