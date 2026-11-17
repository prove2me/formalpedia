-- Prove2me | Definitions.Def_MultitaskContracts_Supplement_MinBudgetLang
-- name    : MultitaskContracts_Supplement_MinBudgetLang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:06:25.324167+00:00
-- url     : https://prove2.me/theorems/7e617a6e-91ba-46c8-88ab-9d098e8e8a17
-- title:
--   The decision language "$\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinBudget}}>B$" for independent instances with rational data
-- statement:
--   An input of the decision problem of Theorem 5 is a number of tasks $n$, rational parameters $p_k,q_k,c_k$ for $k<n$ and a rational budget $B$. Each rational is written in lowest terms $a/b$ ($b>0$) in binary, as a sign bit, the binary digits of $|a|$, a separator, the binary digits of $b$ and a separator. The input is the binary code of $n$, a separator, the codes of $p_k,q_k,c_k$ for $k=0,\dots,n-1$, and the code of $B$, so its length is the bit length of the input. The alphabet has three symbols: two bits and a separator.
--
--   The **language** consists of exactly the codes of the inputs for which there is an instance $I$ of the multitask model on the tasks $\{0,\dots,n-1\}$ such that:
--   1. $I$ has independent tasks, i.e. $P_S$ is the product of its marginals;
--   2. task $k$ has success probabilities $p_k$ under effort and $q_k$ under shirking, and cost $c_k$;
--   3. the minimum budget of bundle contracts exceeds the budget, i.e.
--   $$\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinBudget}}(I)\;>\;B.$$
--
--   Theorem 5 states that this language is NP-hard.
--
--   **Formalization Note** Independence and the marginals determine $P_S$, so "some instance" is the same as "the instance". Such an instance exists exactly when the parameters are valid ($0\le q_k<p_k\le1$, $c_k>0$; then $P_K(K)=\prod_kp_k>0$). Strings that are not codes, or that code invalid parameters, are outside the language. The comparison $\mathrm{OPT}>B$ is made in the extended reals, so it is exact also for a negative $B$. The alphabet is `Option Bool` (`some b` a bit, `none` the separator), and binary digits are little-endian (`Nat.bits`).
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Theorem 5, p.32 (PDF p.34), and its proof, "All parameters are rationals of polynomial bit length", p.32

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle
import Definitions.Def_MultitaskContracts_Instance_IsIndependent

set_option autoImplicit false

open scoped ENNReal

namespace MultitaskContracts.Supplement

/-- Binary code of a natural number over the alphabet `Option Bool` (`some b` is a bit, `none`
a separator): its little-endian binary digits (`Nat.bits`); `0` has the empty code. -/
def encNat (n : ℕ) : List (Option Bool) :=
  (Nat.bits n).map some

/-- Binary code of a rational `x = a/b` in lowest terms (`b > 0`): a sign bit, the binary
digits of `|a|`, a separator, the binary digits of `b`, a separator. -/
def encRat (x : ℚ) : List (Option Bool) :=
  some (decide (x.num < 0)) :: encNat x.num.natAbs ++ none :: encNat x.den ++ [none]

/-- Binary code of an input of Theorem 5: the number of tasks `n` and a separator, then for each
task `k < n` the rationals `p_k, q_k, c_k`, then the rational budget `B`. Its length is the bit
length of the input. -/
def encInput (n : ℕ) (p q c : Fin n → ℚ) (B : ℚ) : List (Option Bool) :=
  encNat n ++ none :: (List.ofFn (fun k : Fin n => encRat (p k) ++ encRat (q k) ++ encRat (c k))).flatten
    ++ encRat B

/-- **The decision problem of Theorem 5** (p.32, PDF 34): given an instance with independent tasks
and a rational budget `B`, is `OPT^Bun_MinBudget > B`? The language contains exactly the codes
`encInput n p q c B` of inputs with rational parameters for which some instance `I` on the tasks
`Fin n` with independent tasks has marginals `p_k`, `q_k` and costs `c_k`, and
`OPT^Bun_MinBudget(I) > B`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Theorem 5, p.32 (PDF 34).

**Formalization Note.** Independence and the marginals determine `P_S` (published
`Instance.IsIndependent`), so the existential is equivalent to the universal; such an `I` exists
exactly when the parameters are valid (`0 ≤ q_k < p_k ≤ 1`, `c_k > 0`; then `P_K(K) = ∏ p_k > 0`).
Strings that are not codes, or code invalid parameters, are outside the language. The comparison
`OPT > B` is made in `EReal`, so it is exact also for a negative `B` and for `OPT = ∞`. Rationals are
written in binary in lowest terms, so the input size is the bit length. -/
def MinBudgetLang : Set (List (Option Bool)) :=
  {w | ∃ (n : ℕ) (p q c : Fin n → ℚ) (B : ℚ), w = encInput n p q c B ∧
    ∃ I : Instance (Fin n), I.IsIndependent ∧
      (∀ k, I.p k = (p k : ℝ) ∧ I.q k = (q k : ℝ) ∧ I.c k = (c k : ℝ)) ∧
      (((B : ℝ) : EReal) < ((I.optMinBudget (bundle (Fin n)) : ℝ≥0∞) : EReal))}

end MultitaskContracts.Supplement


