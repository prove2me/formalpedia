-- Prove2me | Definitions.Def_UniversalNonstochastic_Main_Supplement_Deficiencies
-- name    : UniversalNonstochastic_Main_Supplement_Deficiencies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:24:55.612216+00:00
-- url     : https://prove2.me/theorems/b2ecdc49-5ffd-475f-bf2e-7a9305987353
-- title:
--   Deficiency $d_K$, randomness p-tests, a largest p-test $d_p$, and the sets $N^C_{\alpha,\beta}(d)$, $N^{qu}_{\alpha,\beta}$
-- statement:
--   Let $U$, $V$ be the optimal prefix and plain decoders, $\omega\in\mathcal X=\mathbb N$ an object and $Q$ an elementary probability measure (finite support, rational values).
--
--   1. $d_K(\omega\mid Q)=-\log Q(\{\omega\})-K(\omega)$, with $-\log 0:=\infty$ (equation (12) with $F=K$).
--   2. A **randomness p-test** is a function $t(\omega,Q)\in\mathbb N_0\cup\{\infty\}$ that is lower semicomputable (the set of triples $(\omega,\text{code of }Q,k)$ with $k<t(\omega,Q)$ is recursively enumerable) and satisfies
--   $$Q(\{\omega\mid t(\omega,Q)\ge n\})\le 2^{-n}\qquad\text{for all }Q\text{ and all }n\in\mathbb N.$$
--   3. $d_p$ is a **largest** randomness p-test: it is a randomness p-test, and for every randomness p-test $t$ there is a constant $c$ with $t\le d_p+c$ everywhere. Its values, read as extended reals, give the randomness p-deficiency $d_p(\omega\mid Q)$.
--   4. $N^C_{\alpha,\beta}(d)$, for a deficiency $d$, $\alpha\in\mathbb N_0$ and $\beta\in[0,\infty)$, is the set of $\omega$ for which no elementary $Q$ has $C(Q)\le\alpha$ and $d(\omega\mid Q)\le\beta$.
--   5. $N^{qu}_{\alpha,\beta}$, for $\alpha\in\mathbb N_0$ and $\beta\in[0,\infty]$, is the set of $\omega$ for which no elementary $Q$ has $K(Q)\le\alpha$, $Q(\{\omega\})>0$ and $K(\omega)\ge-\log Q(\{\omega\})-\beta$.
--
--   These objects carry the omnibus Theorems 13–15 and Theorem 8.
--
--   **Formalization Note** Deficiencies are `EReal`-valued. $N^{qu}_{\alpha,\beta}$ keeps the clause $Q(\{\omega\})>0$ explicitly, so that for $\beta=+\infty$ the condition reduces to $K(Q)\le\alpha$ and $Q(\{\omega\})>0$, as in the source.
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, p.8–9 (N^qu), p.10 (deficiencies, N^C_{α,β}(d), eq. (12)), p.12 (randomness p-tests and d_p)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_ElementaryModels
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities

namespace UniversalNonstochastic.Main.Supplement

/-- `d_K(ω | Q) = -log₂ Q({ω}) - K(ω)` (S, p.10: eq. (12) with `F = K`), `+∞` when
`Q({ω}) = 0`. -/
noncomputable def dK (U : OptimalPrefixDecoder) (ω : ℕ+) (Q : ElemMeasure) : EReal :=
  if Q.w ω = 0 then ⊤ else
    ((-Real.logb 2 (Q.w ω : ℝ) : ℝ) : EReal) - toEReal (Kobj U ω)

/-- The `Q`-probability `Q({ω | t(ω, Q) ≥ n})` of the event that a test takes a value at
least `n` (a finite sum over the support of `Q`). -/
noncomputable def testTailProb (t : ℕ+ → ElemMeasure → ℕ∞) (Q : ElemMeasure) (n : ℕ) : ℝ :=
  open Classical in
  ∑ ω ∈ Q.supp.filter (fun ω => (n : ℕ∞) ≤ t ω Q), (Q.w ω : ℝ)

/-- A randomness p-test (S, p.12): a function `t(ω, Q) ∈ ℕ₀ ∪ {∞}` of an object and an
elementary probability measure that is lower semicomputable (the set of triples
`(ω, code Q, k)` with `k < t(ω, Q)` is recursively enumerable) and satisfies
`Q({ω | t(ω, Q) ≥ n}) ≤ 2^{-n}` for all `Q` and all `n ∈ ℕ = {1, 2, …}`. -/
def IsRandomnessPTest (t : ℕ+ → ElemMeasure → ℕ∞) : Prop :=
  REPred (fun p : ℕ+ × ℕ × ℕ => ∃ Q : ElemMeasure, Q.code = p.2.1 ∧ (p.2.2 : ℕ∞) < t p.1 Q) ∧
    ∀ (Q : ElemMeasure) (n : ℕ), 1 ≤ n → testTailProb t Q n ≤ (1 / 2 : ℝ) ^ n

/-- `d_p` is a largest randomness p-test to within an additive constant (S, p.12): it is a
randomness p-test and every randomness p-test `t` satisfies `t ≤ d_p + c` everywhere for
some constant `c` (depending on `t` only). -/
def IsLargestPTest (dp : ℕ+ → ElemMeasure → ℕ∞) : Prop :=
  IsRandomnessPTest dp ∧
    ∀ t : ℕ+ → ElemMeasure → ℕ∞, IsRandomnessPTest t →
      ∃ c : ℕ, ∀ ω Q, t ω Q ≤ dp ω Q + c

/-- The randomness p-deficiency `d_p(ω | Q)` as an extended-real deficiency. -/
noncomputable def pDeficiency (dp : ℕ+ → ElemMeasure → ℕ∞) (ω : ℕ+) (Q : ElemMeasure) : EReal :=
  toEReal (dp ω Q)

/-- `N^C_{α,β}(d)` (S, p.10): objects for which no elementary probability measure `Q` has
plain complexity `C(Q) ≤ α` and `d(ω | Q) ≤ β`. -/
def nonQuasiStochasticC (V : OptimalPlainDecoder) (d : ℕ+ → ElemMeasure → EReal)
    (α : ℕ) (β : ℝ) : Set ℕ+ :=
  {ω | ¬ ∃ Q : ElemMeasure, Cmeas V Q ≤ (α : ℕ∞) ∧ d ω Q ≤ ((β : ℝ) : EReal)}

/-- `N^{qu}_{α,β}` (S, p.9), for `β ∈ [0, ∞]`: objects `ω` for which no elementary
probability measure `Q` has `K(Q) ≤ α`, `Q({ω}) > 0` and `K(ω) ≥ -log₂ Q({ω}) - β`
(unconditional complexity). For `β = +∞` the last condition always holds. -/
def nonQuasiStochasticU (U : OptimalPrefixDecoder) (α : ℕ) (β : EReal) : Set ℕ+ :=
  {ω | ¬ ∃ Q : ElemMeasure, Kmeas U Q ≤ (α : ℕ∞) ∧ 0 < Q.w ω ∧
      ((-Real.logb 2 (Q.w ω : ℝ) : ℝ) : EReal) - β ≤ toEReal (Kobj U ω)}

end UniversalNonstochastic.Main.Supplement


