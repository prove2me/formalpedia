-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_CreditModel
-- name    : BauerleRiederMDP_AmericanPut_CreditModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:51.750471+00:00
-- url     : https://prove2.me/theorems/07370395-ee97-4e59-bc81-9f88ee445c34
-- title:
--   Credit granting model: kernel $Q^X$ on $\mathbb R$, reward $c$, discount $\beta\in(0,1]$
-- statement:
--   In the **credit granting problem** a bank observes information $x_n\in E:=\mathbb R$ about a borrower (e.g. a rating class), which evolves as a Markov process $(X_n)$ with transition kernel $Q^X$. With actions $a=0$ (extend the credit) and $a=1$ (cancel the contract), extending at state $x$ yields the reward $c(x)$ (of arbitrary sign), cancelling ends the contract with reward $g\equiv0$, and rewards are discounted by $\beta\in(0,1]$. The maximal duration of the contract is $N$.
--
--   **Formalization Note** $Q^X$ is a Markov kernel on $\mathbb R$ and $c$ is measurable, as one-stage rewards of a Markov Decision Model are (§10.1). $g\equiv0$ is built into the recursions for $J_n$ and for policy values.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §11.2, p.340, PDF 348

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.AmericanPut

/-- The **credit granting model** of §11.2 (Bäuerle & Rieder, Markov Decision Processes with Applications to
Finance (2011), §11.2, p.340, PDF 348): a stationary stopping problem with bounded horizon and data
* `E := ℝ`, where `x` denotes the information about the borrower (rating class),
* `A := {0, 1}`, where `a = 0` means extend the credit and `a = 1` means cancel the contract,
* `Q^X` is the transition kernel of the information process `(X_n)`,
* `c(x)` is arbitrary and `g(x) ≡ 0`,
* `β ∈ (0, 1]`.

**Formalization Note.** `Q^X` is a Markov kernel on `ℝ` (Mathlib's `Kernel` with `IsMarkovKernel`, so it is
measurable in `x`); `c` is measurable, as every one-stage reward of a Markov Decision Model is (§10.1, p.304,
"a measurable reward `c_n(X_n)`"). The terminal and stopping reward `g ≡ 0` is built into the recursions
`CreditModel.J` and `CreditModel.policyValue`. The existence of an upper bounding function, assumed on p.340,
is the separate predicate `CreditModel.IsUpperBoundingFunction`. -/
structure CreditModel where
  /-- The transition kernel `Q^X` of the information process. -/
  QX : Kernel ℝ ℝ
  isMarkovKernel_QX : IsMarkovKernel QX
  /-- The one-stage reward `c(x)` of extending the credit. -/
  c : ℝ → ℝ
  measurable_c : Measurable c
  /-- The discount factor `β`. -/
  beta : ℝ
  beta_pos : 0 < beta
  beta_le_one : beta ≤ 1

end BauerleRiederMDP.AmericanPut


