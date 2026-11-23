-- Prove2me | Definitions.Def_InnovAlloc_Optimal_Supplement_MonoSharing
-- name    : InnovAlloc_Optimal_Supplement_MonoSharing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:47:51.951338+00:00
-- url     : https://prove2.me/theorems/84008b0f-6aa3-4d5a-b814-cf397b826b30
-- title:
--   §4.1, p. 18 — the one-agent sharing optimization and candidate formulas
-- statement:
--   For capacity $B>1$, write $\Pi_m(\gamma,B)$ for the published profit at allocation $(B,0)$. A maximizing one-agent share is an admissible $\gamma\in(0,1)$ satisfying
--
--   $$\Pi_m(\eta,B)\le\Pi_m(\gamma,B)\quad\text{for every }\eta\in(0,1).$$
--
--   The candidate functions are $\gamma_m(B)=1/\sqrt B$ and $M(B)=(1-1/\sqrt B)^2$. Proposition 4 asserts their optimality and identifies the actual game payoffs; neither assertion is assumed here. These functions supply the one-agent benchmark for comparing endogenous allocation strategies.
--
--   **Formalization Note** The displayed candidate formulas are used only at $B>1$, where the square root is positive and the candidate share is admissible.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), p. 18, one-agent optimization preceding Proposition 4

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model

namespace InnovAlloc.Optimal.Supplement

noncomputable section

/-- The one-agent sharing problem immediately before Proposition 4 (p. 18). -/
def IsMonoShare (B γ : ℝ) : Prop :=
  γ ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∀ η ∈ Set.Ioo (0 : ℝ) 1, profitMono η B ≤ profitMono γ B

/-- The candidate share in Proposition 4; its optimality is a theorem, not a definition. -/
def gammaM (B : ℝ) : ℝ := 1 / Real.sqrt B

/-- The candidate optimized one-agent value of Proposition 4, used only for B > 1. -/
def monoValue (B : ℝ) : ℝ := (1 - 1 / Real.sqrt B) ^ 2

end
end InnovAlloc.Optimal.Supplement


