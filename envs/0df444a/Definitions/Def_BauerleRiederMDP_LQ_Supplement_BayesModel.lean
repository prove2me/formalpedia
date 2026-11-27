-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel
-- name    : BauerleRiederMDP_LQ_Supplement_BayesModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:55:48.938813+00:00
-- url     : https://prove2.me/theorems/bff3139f-bc47-473f-899b-0461460b0433
-- title:
--   A Bayesian Model
-- statement:
--   **A Bayesian Model** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Example 5.2.4, p.155, PDF 168, with §5.1–§5.2, pp.148–154, PDF 161–167, and §5.4, pp.159–163, PDF 172–176): the unobservable state is a parameter $\vartheta $ with prior $Q_0$ on $\Theta $; the observable state $x \in  E_X$ moves by $x_{n+1} = T_X(x_n, a_n, z_{n+1})$, where the disturbance $z_{n+1}$ has law $Q^Z(\cdot |x_n, \theta , a_n)$, which has a density $q^Z(z|x, \theta , a)$ with respect to a σ-finite measure $\lambda $ (§5.2, p.154). Rewards $r(x, \theta , a)$, terminal reward $g(x, \theta )$ and a discount factor $\beta  \in  (0, 1]$. $D \subset  E_X \times  A$ contains the graph of a measurable map.
--
--   **Formalization Note.** Kernel and reward are given on all of $E_X \times  \Theta  \times  A$; only their values for $(x, a) \in  D$ enter. The Borel-space requirements of Chapter 5 (p.148) are imposed in the theorems. Densities are $[0, \infty ]$-valued and jointly measurable.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Example 5.2.4, p.155, PDF 168, with §5.1–§5.2, pp.148–154, PDF 161–167, and §5.4, pp.159–163, PDF 172–176

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **A Bayesian Model** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Example 5.2.4, p.155, PDF 168, with §5.1–§5.2, pp.148–154, PDF 161–167, and §5.4,
pp.159–163, PDF 172–176): the unobservable state is a parameter `ϑ` with prior `Q_0` on `Θ`; the
observable state `x ∈ E_X` moves by `x_{n+1} = T_X(x_n, a_n, z_{n+1})`, where the disturbance
`z_{n+1}` has law `Q^Z(·|x_n, θ, a_n)`, which has a density `q^Z(z|x, θ, a)` with respect to a
σ-finite measure `λ` (§5.2, p.154). Rewards `r(x, θ, a)`, terminal reward `g(x, θ)` and a discount
factor `β ∈ (0, 1]`. `D ⊂ E_X × A` contains the graph of a measurable map.

**Formalization Note.** Kernel and reward are given on all of `E_X × Θ × A`; only their values for
`(x, a) ∈ D` enter. The Borel-space requirements of Chapter 5 (p.148) are imposed in the theorems.
Densities are `[0, ∞]`-valued and jointly measurable. -/
structure BayesModel (EX A Z Θ : Type*) [MeasurableSpace EX] [MeasurableSpace A]
    [MeasurableSpace Z] [MeasurableSpace Θ] where
  /-- The admissible state-action pairs `D`. -/
  D : Set (EX × A)
  D_meas : MeasurableSet D
  D_sel : ∃ f : EX → A, Measurable f ∧ ∀ x, (x, f x) ∈ D
  /-- The law `Q^Z(·|x, θ, a)` of the disturbance. -/
  QZ : Kernel (EX × Θ × A) Z
  QZ_markov : IsMarkovKernel QZ
  /-- The σ-finite reference measure `λ` on `𝒵`. -/
  lam : Measure Z
  lam_sigmaFinite : SigmaFinite lam
  /-- The density `q^Z(z|x, θ, a)`. -/
  qZ : EX × Θ × A → Z → ℝ≥0∞
  qZ_meas : Measurable (Function.uncurry qZ)
  QZ_eq : ∀ p, QZ p = lam.withDensity (qZ p)
  /-- The transition function `T_X`. -/
  TX : EX × A × Z → EX
  TX_meas : Measurable TX
  /-- The one-stage reward `r(x, θ, a)`. -/
  r : EX × Θ × A → ℝ
  r_meas : Measurable r
  /-- The terminal reward `g(x, θ)`. -/
  g : EX × Θ → ℝ
  g_meas : Measurable g
  /-- The discount factor. -/
  β : ℝ
  β_pos : 0 < β
  β_le_one : β ≤ 1
  /-- The prior `Q_0` of `ϑ`. -/
  Q0 : Measure Θ
  Q0_prob : IsProbabilityMeasure Q0

attribute [instance] BayesModel.QZ_markov

end BauerleRiederMDP.LQ.Supplement


