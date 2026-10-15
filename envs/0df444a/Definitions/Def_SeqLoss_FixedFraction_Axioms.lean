-- Prove2me | Definitions.Def_SeqLoss_FixedFraction_Axioms
-- name    : SeqLoss_FixedFraction_Axioms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:17.949269+00:00
-- url     : https://prove2.me/theorems/3bd76f28-422f-4c41-bbf8-4f9dc4505381
-- title:
--   pp. 9–12 — Axioms 1–4: additivity, zero truncation, population monotonicity (corrected range), merging proofness
-- statement:
--   Let $\varphi$ be a rule (see the Setting) and $e_n=(0,\dots,0,1)\in L^n$ the elementary problems.
--
--   1. **Additivity (Axiom 1, p. 9).** For each $n$ and $\ell,\ell'\in L^n$, $\ \varphi(\ell)+\varphi(\ell')=\varphi(\ell+\ell')$.
--   2. **Zero truncation (Axiom 2, p. 10).** For each $n$, $\ell\in L^n$ and $i\in\{1,\dots,n\}$,
--   $$\varphi_i(\ell)=\varphi_i(\ell,0)=\varphi_i(\ell_1,\dots,\ell_n,0):$$
--   appending a trailing zero loss changes no existing agent's liability.
--   3. **Population monotonicity (Axiom 3, p. 11).** For each $n$, each $1\le j<n$ and each $1\le i\le j<k\le n$,
--   $$\varphi_i(e_n)\ \ge\ \varphi_i(e_{n+1})\qquad\text{and}\qquad \varphi_k(e_n)\ \ge\ \varphi_{k+1}(e_{n+1}).$$
--   Here $e_{n+1}$ is $e_n$ with a zero loss inserted after agent $j$: agents up to $j$ keep their index and agent $k>j$ becomes agent $k+1$. Adding an agent with no loss makes no old agent worse off.
--   4. **Merging proofness (Axiom 4, p. 12).** For each $i\in\{1,2\}$,
--   $$\varphi_i(e_3)+\varphi_{i+1}(e_3)\ \le\ \varphi_i(e_2):$$
--   two consecutive agents of $e_3$ cannot lower their joint liability by merging into one agent of $e_2$.
--
--   These are the four axioms of Theorem 1, which shows that together they single out the fixed-fraction rules.
--
--   **Formalization Note.** Agents are 0-based. Axioms 1 and 2 quantify over loss vectors $\ell\ge 0$ only; $(\ell,0)$ is `Fin.snoc ℓ 0`, in which agent $i$ of $\ell$ is `i.castSucc`. **Axiom 3 is stated with $1\le j<n$; the manuscript prints $1<j<n$.** With the printed range Theorem 1 and Proposition 2 are false: the rule with $\varphi(e_1)=(1)$, $\varphi(e_2)=(\tfrac12,\tfrac12)$, $\varphi(e_3)=(\tfrac12,0,\tfrac12)$, $\varphi(e_n)=(\tfrac14,0,\dots,0,\tfrac12,\tfrac14)$ for $n\ge 4$, extended to all problems by Proposition 1's formula, satisfies all four printed axioms but is no fixed-fraction rule. The paper's own consequences of the axiom (p. 11) and the proof of Proposition 2 (p. 23) use $j=1$. In 0-based indices, $i\le j$ reads `i.val + 1 ≤ j` and $j<k$ reads `j < k.val + 1`. In Axiom 4, $\varphi_2(e_3)$ is `φ 3 (elem 3) 1`.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses: Automated Conflict Resolution Through Smart Contracts, accepted manuscript (2023), Management Science 70(3) 1773–1786, doi:10.1287/mnsc.2023.4772, pp. 9–12: Axiom 1 (p. 9), Axiom 2 (p. 10), Axiom 3 (p. 11, range corrected to 1 ≤ j < n), Axiom 4 (p. 12)

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting

namespace SeqLoss.FixedFraction

/-- Axiom 1 (Additivity), p. 9: `φ(ℓ) + φ(ℓ') = φ(ℓ + ℓ')` for all `ℓ, ℓ' ∈ L^n`. -/
def Additive (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ n (ℓ ℓ' : Fin n → ℝ), IsLoss ℓ → IsLoss ℓ' → φ n (ℓ + ℓ') = φ n ℓ + φ n ℓ'

/-- Axiom 2 (Zero truncation), p. 10: `φ_i(ℓ) = φ_i(ℓ, 0)` for every `ℓ ∈ L^n` and every agent
`i ∈ {1, …, n}`; `(ℓ, 0)` is `Fin.snoc ℓ 0`, in which agent `i` of `ℓ` is `i.castSucc`. -/
def ZeroTruncation (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ n (ℓ : Fin n → ℝ), IsLoss ℓ →
    ∀ i : Fin n, φ (n + 1) (Fin.snoc ℓ 0) i.castSucc = φ n ℓ i

/-- Axiom 3 (Population monotonicity), p. 11, with the range of `j` corrected from the printed
`1 < j < n` to `1 ≤ j < n`: for `1 ≤ i ≤ j < k ≤ n` (1-based),
`φ_i(e_n) ≥ φ_i(e_{n+1})` and `φ_k(e_n) ≥ φ_{k+1}(e_{n+1})`.
In 0-based indices `i, k : Fin n`, `i ≤ j` reads `i.val + 1 ≤ j` and `j < k` reads `j < k.val + 1`;
agent `i` of `e_n` stays agent `i` (`i.castSucc`) and agent `k` moves to `k + 1` (`k.succ`). -/
def PopulationMonotone (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ n j : ℕ, 1 ≤ j → j < n → ∀ i k : Fin n, i.val + 1 ≤ j → j < k.val + 1 →
    φ (n + 1) (elem (n + 1)) i.castSucc ≤ φ n (elem n) i ∧
    φ (n + 1) (elem (n + 1)) k.succ ≤ φ n (elem n) k

/-- Axiom 4 (Merging proofness), p. 12: for `i ∈ {1, 2}`, `φ_i(e_3) + φ_{i+1}(e_3) ≤ φ_i(e_2)`
(0-based: agents `0, 1, 2` of `e_3` and `0, 1` of `e_2`). -/
def MergingProof (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  φ 3 (elem 3) 0 + φ 3 (elem 3) 1 ≤ φ 2 (elem 2) 0 ∧
  φ 3 (elem 3) 1 + φ 3 (elem 3) 2 ≤ φ 2 (elem 2) 1

end SeqLoss.FixedFraction


