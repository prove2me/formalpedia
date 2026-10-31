-- Prove2me | Definitions.Def_DivideChooseBayes_algOutput
-- name    : DivideChooseBayes_algOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:29:01.553171+00:00
-- url     : https://prove2.me/theorems/77ab92b1-a6d9-4ba4-9663-835dd5eecac9
-- title:
--   Output $(p_1,\dots,p_n)$ of Algorithm 1
-- statement:
--   The output of Algorithm 1 is the division $p$ held after the last iteration of the main loop (line 13), for a given selection of optimal solutions of the programs $\mathcal C_{P_k}$.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Algorithm 1, line 13, p.9

import Mathlib
import Definitions.Def_DivideChooseBayes_algRun
import Definitions.Def_DivideChooseBayes_iterationCount

namespace DivideChooseBayes

/-- **The output `(p₁, …, pₙ)` of Algorithm 1.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Algorithm 1, line 13, p.9: "return (p₁, p₂, …, pₙ)".

The division held by the state after the last iteration of the main loop, for the selection
`sol` of optimal solutions of the programs `C_{P_k}`. -/
noncomputable def algOutput {ι : Type*} [Fintype ι] (gD : ι → ℝ) (γ : ℝ) (sol : ℕ → ι → ℝ) :
    ι → ℝ :=
  (algRun gD γ sol (iterationCount gD γ)).2

end DivideChooseBayes


