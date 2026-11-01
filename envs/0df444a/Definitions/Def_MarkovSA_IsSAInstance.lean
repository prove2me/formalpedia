-- Prove2me | Definitions.Def_MarkovSA_IsSAInstance
-- name    : MarkovSA_IsSAInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:06.116006+00:00
-- url     : https://prove2.me/theorems/b9071ad1-a767-4b42-a450-2e5bd02d5440
-- title:
--   An instance of Algorithm (6) under Assumptions 2.1, 2.2 and 2.4
-- statement:
--   Fix a probability space $(\Omega,\mathbb P)$, a transition matrix $P$ with distribution $\mu$, constants $\beta,A_1,B_1,A_2,B_2$, stepsizes $(\alpha_k)$, an operator $F$, a fixed initial point $x_0$, a point $x^*$, a chain $(Y_k)$, a filtration $(\mathcal G_k)$ and noise $(w_k)$. They form an **instance of Algorithm (6)** if
--
--   1. $F$ satisfies Assumption 2.1 with $A_1,B_1$;
--   2. $\bar F$ satisfies Assumption 2.2 with $\beta$;
--   3. $x^*$ solves Eq. (5): $\bar F(x^*)=x^*$;
--   4. $(Y_k)$ is a Markov chain with transition matrix $P$ relative to $(\mathcal G_k)$;
--   5. the iterates $x_k$ of Algorithm (6) are $\mathcal G_k$-measurable for every $k$;
--   6. the noise satisfies Assumption 2.4 with $A_2,B_2$ along these iterates.
--
--   Assumption 2.3 concerns $P$ and $\mu$ only and is stated separately.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, §2.1, pp.5–6

import Mathlib
import Definitions.Def_MarkovSA_Fbar
import Definitions.Def_MarkovSA_saIter
import Definitions.Def_MarkovSA_IsMarkovWrt
import Definitions.Def_MarkovSA_Assumption21
import Definitions.Def_MarkovSA_Assumption22
import Definitions.Def_MarkovSA_Assumption24
open MeasureTheory

namespace MarkovSA

/-- An **instance of Algorithm (6) under Assumptions 2.1, 2.2 and 2.4** (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §2.1, pp.5–6), run with
stepsizes `α` from the fixed vector `x₀`:
`F` satisfies Assumption 2.1 with `A₁, B₁`; `F̄` satisfies Assumption 2.2 with `β`; `x*` solves Eq. (5),
`F̄(x*) = x*`; `Y` is a Markov chain with transition matrix `P` relative to the filtration `G`, to which the
iterates are adapted (reading R1); and the noise satisfies Assumption 2.4 with `A₂, B₂` along the iterates.

Assumption 2.3 concerns `P, μ` only and is a separate hypothesis. -/
def IsSAInstance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴] [MeasurableSpace 𝒴] [MeasurableSingletonClass 𝒴] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Pr : Measure Ω) (P : Matrix 𝒴 𝒴 ℝ) (μ : 𝒴 → ℝ) (β A₁ B₁ A₂ B₂ : ℝ) (α : ℕ → ℝ)
    (F : E → 𝒴 → E) (x₀ xstar : E) (Y : ℕ → Ω → 𝒴) (G : Filtration ℕ mΩ) (w : ℕ → Ω → E) : Prop :=
  Assumption21 F A₁ B₁ ∧ Assumption22 F μ β ∧ Fbar F μ xstar = xstar ∧ IsMarkovWrt Pr P G Y ∧
    (∀ k, Measurable[G k] (saIter F α x₀ Y w k)) ∧
    Assumption24 Pr (saIter F α x₀ Y w) Y w A₂ B₂

end MarkovSA


