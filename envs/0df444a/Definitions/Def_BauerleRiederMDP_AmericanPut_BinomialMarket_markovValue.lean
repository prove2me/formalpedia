-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_markovValue
-- name    : BauerleRiederMDP_AmericanPut_BinomialMarket_markovValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:37.356783+00:00
-- url     : https://prove2.me/theorems/9057428a-dc45-4f42-b7cd-048fc749cb3a
-- title:
--   Value $J_\infty$ of the positive stopping MDP over Markov policies
-- statement:
--   $J_\infty$ is the value of the infinite-stage positive Markov Decision Model of the perpetual put: state space $E=\mathbb R_+$, actions $\{0,1\}$ (continue, exercise), exercise reward $(K-x)^+$, no continuation reward, kernel $q\delta_{xu}+(1-q)\delta_{xd}$, discount factor $\beta$. For $x\in E$,
--   $$J_\infty(x)=\sup_\pi\ \mathbb E^{\mathbb Q}_x\big[\beta^{\tau_\pi}(K-X_{\tau_\pi})^+\mathbf 1_{\{\tau_\pi<\infty\}}\big],$$
--   the supremum over Markov policies $\pi=(f_0,f_1,\dots)$ with measurable decision rules, where $\tau_\pi$ is the first $n$ with $f_n(X_n)=1$.
--
--   **Formalization Note** Decision rules are represented by measurable exercise sets $A_n=\{f_n=1\}$. The supremum is taken in $[0,\infty]$, where each term is at most $K$, and converted to a real number.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, proof of Theorem 11.1.3 a), p.338, PDF 346; Remark 11.1.4, p.338, PDF 346; §10.1, pp.305–306, PDF 313–314

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_putReward
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_policyTime

open MeasureTheory
open scoped ENNReal

namespace BauerleRiederMDP.AmericanPut

/-- The **value `J_∞` of the infinite-stage positive Markov Decision Model of the perpetual put** (Bäuerle &
Rieder, Markov Decision Processes with Applications to Finance (2011), proof of Theorem 11.1.3 a), p.338,
PDF 346, and Remark 11.1.4, p.338, PDF 346): the stopping problem of §11.1 (p.332, PDF 340) with `E = ℝ₊`,
`A = {0, 1}`, `g = (K − x)⁺`, `c ≡ 0`, kernel `q δ_{xu} + (1 − q) δ_{xd}` and discount `β`, whose value is the
supremum over Markov policies `π = (f_0, f_1, …)` of the expected discounted reward
`J_{∞π}(x) = 𝔼^ℚ_x[β^{τ_π} (K − X_{τ_π})⁺ 1_{τ_π < ∞}]`, `τ_π` the first `n` with `f_n(X_n) = 1`.

**Formalization Note.** A decision rule `f_n` is represented by its measurable exercise set `A_n = {f_n = 1}`;
the reward of the stopping MDP is earned once, at the exercise time `policyTime`, after which the process sits
in the cemetery state with reward `0`. The supremum is taken in `ℝ≥0∞` (each term is at most `K`), and
`toReal` is exact. -/
noncomputable def BinomialMarket.markovValue (M : BinomialMarket) (K x : ℝ) : ℝ :=
  (⨆ A : {A : ℕ → Set ℝ // ∀ n, MeasurableSet (A n)}, M.putReward K x (M.policyTime x A.1)).toReal

end BauerleRiederMDP.AmericanPut


