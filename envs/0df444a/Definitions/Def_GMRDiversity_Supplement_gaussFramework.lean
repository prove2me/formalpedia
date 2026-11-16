-- Prove2me | Definitions.Def_GMRDiversity_Supplement_gaussFramework
-- name    : GMRDiversity_Supplement_gaussFramework
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:08:55.195377+00:00
-- url     : https://prove2.me/theorems/cb0c880a-9a11-462a-8f42-7025e52e3016
-- title:
--   The one-dimensional Gaussian GMR framework and its drift parameter $\alpha$
-- statement:
--   Fix $\mu,\lambda_1,\lambda_2\in\mathbb R$, noise levels $\sigma_M,\sigma_R$ and costs $c_G,c_M,c_R\in\mathbb N_{>0}$. The **Gaussian GMR framework** of §4 has $X=\mathbb R$, $U(x)=x$ and full feedback, with
--
--   1. generation: an independent standard Gaussian $N(0,1)$ sample;
--   2. mutation: $x\mapsto \mu x+\sigma_M Z$;
--   3. recombination: $(x,y)\mapsto\lambda_1x+\lambda_2y+\sigma_R Z$ (ordered parents),
--
--   where every operator call uses its own fresh $Z\sim N(0,1)$, independent of everything else. Its **drift parameter** is
--   $$
--   \alpha:=\min\Big\{1,\ \frac{1-\mu}{\sigma_M},\ \frac{1-\lambda_1-\lambda_2}{\sigma_R}\Big\}.
--   $$
--
--   This is the framework of Theorem 1, whose three regimes are distinguished by the sign of $\alpha$.
--
--   **Formalization Note** The parameter ranges $\mu,\lambda_1,\lambda_2\ge0$ and $\sigma_M,\sigma_R>0$ are hypotheses of Theorem 1, not of this construction. Mutation and recombination are Markov kernels; their independence across rounds comes from the run law of `GMRDiversity.Supplement.Policy`.
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), §4, p.6 (framework and α in Theorem 1)

import Mathlib
import Definitions.Def_GMRDiversity_Supplement_GMRFramework

namespace GMRDiversity.Supplement

open MeasureTheory ProbabilityTheory

/-- The Gaussian mutation kernel `x ↦ law of µx + σZ`, `Z ∼ N(0, 1)` (§4, p.6). -/
noncomputable def gaussMutation (μ σ : ℝ) : Kernel ℝ ℝ :=
  ((Kernel.deterministic id measurable_id) ×ₖ (Kernel.const ℝ (gaussianReal 0 1))).map
    (fun p => μ * p.1 + σ * p.2)

/-- The Gaussian recombination kernel `(x, y) ↦ law of λ₁x + λ₂y + σZ`, `Z ∼ N(0, 1)` (§4, p.6). -/
noncomputable def gaussRecombination (l₁ l₂ σ : ℝ) : Kernel (ℝ × ℝ) ℝ :=
  ((Kernel.deterministic id measurable_id) ×ₖ (Kernel.const (ℝ × ℝ) (gaussianReal 0 1))).map
    (fun p => l₁ * p.1.1 + l₂ * p.1.2 + σ * p.2)

/-- **The one-dimensional Gaussian GMR framework of §4** (Brandenberger, Doron-Arad, Mossel,
*Genetic Algorithms with Optimization Guided Operators*, STOC 2027 submission, manuscript sha256
f89f4f77…, §4, p.6): `X = ℝ`, `U(x) = x`, full feedback; generation samples an independent
`N(0, 1)`; mutation maps `x ↦ µx + σ_M Z`; recombination maps `(x, y) ↦ λ₁x + λ₂y + σ_R Z`, "where
the `Z ∼ N(0, 1)` variables are independent"; `D = D₀ ∪ D₁ ∪ D₂`; costs `c_G, c_M, c_R` (any cost
function with strictly positive image).

**Formalization Note.** Each operator call uses its own fresh `Z`: the kernels are applied
independently in every round by the run law of `GMRDiversity.Supplement.Policy`. The parameter
ranges `µ, λ₁, λ₂ ≥ 0`, `σ_M, σ_R > 0` are hypotheses of Theorem 1, not of this construction. -/
noncomputable def gaussFramework (μ l₁ l₂ σM σR : ℝ) (cG cM cR : ℕ) (hG : 0 < cG) (hM : 0 < cM)
    (hR : 0 < cR) : GMRFramework ℝ where
  U := id
  measurable_U := measurable_id
  generation := gaussianReal 0 1
  generation_prob := inferInstance
  mutation := gaussMutation μ σM
  mutation_markov := Kernel.IsMarkovKernel.map _ (by fun_prop)
  recombination := gaussRecombination l₁ l₂ σR
  recombination_markov := Kernel.IsMarkovKernel.map _ (by fun_prop)
  cG := cG
  cM := cM
  cR := cR
  cG_pos := hG
  cM_pos := hM
  cR_pos := hR

/-- The drift parameter `α := min{1, (1 − µ)/σ_M, (1 − λ₁ − λ₂)/σ_R}` of Theorem 1 (p.6). -/
noncomputable def gaussAlpha (μ l₁ l₂ σM σR : ℝ) : ℝ :=
  min 1 (min ((1 - μ) / σM) ((1 - l₁ - l₂) / σR))

end GMRDiversity.Supplement


