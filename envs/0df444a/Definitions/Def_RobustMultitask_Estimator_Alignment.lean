-- Prove2me | Definitions.Def_RobustMultitask_Estimator_Alignment
-- name    : RobustMultitask_Estimator_Alignment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:08.321469+00:00
-- url     : https://prove2.me/theorems/bfcc5425-e693-40ab-b58b-df6839f0a819
-- title:
--   Definition 2, p. 14, and p. 41 — ζ-poorly and ζ-well-aligned components, 𝒥ᵢ, ℐⱼ and ℐ̄ⱼ = ℐ_well ∪ ℐⱼ
-- statement:
--   Let $\beta^1,\dots,\beta^N\in\mathbb R^d$ be task parameters and $\beta^\dagger\in\mathbb R^d$ a shared parameter.
--
--   1. For a component $i\in[d]$, the set of tasks that differ from $\beta^\dagger$ in that component is $\mathcal J_i=\{j\in[N] : \beta^j_{(i)}\neq\beta^\dagger_{(i)}\}$.
--   2. **Definition 2.** Given $\zeta\in[0,1]$, a component $i$ is $\zeta$-poorly-aligned, $i\in\mathcal I^\zeta_{\mathrm{poor}}$, if
--   $$\frac{|\{j\in[N] : \beta^j_{(i)}\neq\beta^\dagger_{(i)}\}|}{N}<\zeta ;$$
--   otherwise it is $\zeta$-well-aligned, $i\in\mathcal I^\zeta_{\mathrm{well}}$.
--   3. For a task $j$, $\mathcal I_j=\{i\in[d] : \beta^j_{(i)}\neq\beta^\dagger_{(i)}\}$ is the set of components where $\beta^j$ differs from $\beta^\dagger$, and $\bar{\mathcal I}_j=\mathcal I_{\mathrm{well}}\cup\mathcal I_j$.
--
--   A poorly-aligned component is one in which few tasks deviate from the shared parameter, so the trimmed mean across tasks can recover $\beta^\dagger_{(i)}$; the well-aligned components are few, and together with $\mathcal I_j$ they form the support that the LASSO step must recover.
--
--   **Formalization Note** The defining inequality is kept in the printed form $|\mathcal J_i|/N<\zeta$ (with Lean's $x/0=0$, every component is poorly aligned when $N=0$). No range for $\zeta$ is built into the definitions; the theorems state the ranges they need.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 14, Definition 2 and 𝒥ᵢ; p. 41, ℐⱼ and ℐ̄ⱼ

import Mathlib

namespace RobustMultitask.Estimator

/-- `𝒥ᵢ = {j ∈ [N] | βʲ_(i) ≠ β†_(i)}` (p. 14): the tasks whose parameter differs from the shared
parameter in component `i`. -/
noncomputable def misalignedTasks {N d : ℕ} (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ)
    (i : Fin d) : Finset (Fin N) :=
  Finset.univ.filter (fun j => β j i ≠ βdag i)

/-- `ℐ^ζ_poor` (Definition 2, p. 14): the components `i ∈ [d]` with
`|{j ∈ [N] | βʲ_(i) ≠ β†_(i)}| / N < ζ`. -/
noncomputable def poorlyAligned {N d : ℕ} (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ)
    (ζ : ℝ) : Finset (Fin d) :=
  Finset.univ.filter (fun i => ((misalignedTasks β βdag i).card : ℝ) / N < ζ)

/-- `ℐ^ζ_well` (Definition 2, p. 14): the components that are not ζ-poorly-aligned. -/
noncomputable def wellAligned {N d : ℕ} (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ)
    (ζ : ℝ) : Finset (Fin d) :=
  (poorlyAligned β βdag ζ)ᶜ

/-- `ℐⱼ = {i ∈ [d] | βʲ_(i) ≠ β†_(i)}` (p. 41): the components of `βʲ` that differ from `β†`. -/
noncomputable def taskSupport {N d : ℕ} (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ)
    (j : Fin N) : Finset (Fin d) :=
  Finset.univ.filter (fun i => β j i ≠ βdag i)

/-- `ℐ̄ⱼ = ℐ_well ∪ ℐⱼ` (p. 41). -/
noncomputable def augSupport {N d : ℕ} (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (ζ : ℝ)
    (j : Fin N) : Finset (Fin d) :=
  wellAligned β βdag ζ ∪ taskSupport β βdag j

end RobustMultitask.Estimator


