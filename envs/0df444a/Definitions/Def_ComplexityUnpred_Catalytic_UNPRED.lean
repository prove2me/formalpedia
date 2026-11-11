-- Prove2me | Definitions.Def_ComplexityUnpred_Catalytic_UNPRED
-- name    : ComplexityUnpred_Catalytic_UNPRED
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:02:32.345476+00:00
-- url     : https://prove2.me/theorems/be5df291-0188-42ca-9bae-5896167ca1f0
-- title:
--   UNPRED: the search problem of Definition 2.4, with its instance and answer codes
-- statement:
--   An **UNPRED instance** consists of $n\in\mathbb N$ (written in unary), an integer $r\ge1$ (written in unary; $\epsilon=1/r$, so $0<\epsilon\le1$), and $m\ge1$ predictors, each a Boolean circuit $P_j$ on $n-1$ inputs with AND, OR, NOT and THRESHOLD gates together with an index $\mathrm{ind}_j\in[n]$; $P_j$ is read as the middle-bit predictor over $\{0,1\}^n$ at index $\mathrm{ind}_j$ computed by the circuit. The instance is coded as $1^n0\,1^r0$ followed by the list (length, then entries) of the pairs (code of $P_j$, binary code of $\mathrm{ind}_j$). A **solution** is a non-empty multiset $S\subseteq\{0,1\}^n$, of any size, with
--   $$\mathrm{adv}_{U(S)}(\{P_1,\dots,P_m\})<\epsilon=\frac1r,$$
--   coded as the list of its elements (length, then each string as its $n$ bits; any order, repetitions for multiplicities).
--
--   UNPRED is a search problem: valid inputs are exactly the codes of such instances, and the answers to an instance are exactly the codes of its solutions. It is the target of the reductions of this mission.
--
--   **Formalization Note** The search problem is the published `TetrisHard.Rows.SearchProblem` (a validity predicate and an answer relation on `List Bool`). `UnpredInstance.WF` requires $n\ge1$, $r\ge1$, $m\ge1$, every circuit well formed on $n-1$ inputs and every index in $[n]$ (1-based in the code). The family $\{P_1,\dots,P_m\}$ is indexed by $j\in\{1,\dots,m\}$, so equal circuits are counted separately. The answer is strict ($<$), $\epsilon>0$ and $S$ non-empty: answers always exist, by the paper's random-multiset argument. The output size is not bounded. The paper's footnote 8 (rounding $\epsilon$ to $1/\lceil1/\epsilon\rceil$) is built into giving $r$.
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 19, Definition 2.4

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_ComplexityUnpred_Catalytic_Predictor
import Definitions.Def_ComplexityUnpred_Catalytic_Circuit

namespace ComplexityUnpred.Catalytic

/-! **Definition 2.4 (UNPRED)**, Agarwala, Dorfman, *The Complexity of Unpredictability*,
arXiv:2611.05956v1, p. 19, as a search problem on bit strings (the published
`TetrisHard.Rows.SearchProblem`: a validity predicate on instance codes and an answer relation).

"Input: `n, m ∈ ℕ`, `0 < ϵ ≤ 1`, Boolean circuits `P₁, …, P_m`, and `ind₁, …, ind_m ∈ [n]` …
Output: A non-empty multiset `S ⊆ {0,1}ⁿ` such that `adv_{U(S)}({P₁, …, P_m}) < ϵ`. … we are
given an integer `r` in unary and `ϵ := 1/r`. We assume that `n` is also given in unary." -/

/-- The data of an UNPRED instance: `n`, `r` (with `ϵ = 1/r`), and the list of the `m`
predictors, each a circuit `Pᵢ` and its index `indᵢ` (1-based, as in the paper). -/
structure UnpredInstance where
  n : ℕ
  r : ℕ
  preds : List (Circuit × ℕ)

/-- Well-formed instance: `n ≥ 1`, `r ≥ 1` (so `0 < ϵ = 1/r ≤ 1`), `m ≥ 1`, every circuit is
well formed on `n − 1` inputs, and every index lies in `[n] = {1, …, n}`. -/
def UnpredInstance.WF (I : UnpredInstance) : Prop :=
  1 ≤ I.n ∧ 1 ≤ I.r ∧ I.preds ≠ [] ∧
    ∀ p ∈ I.preds, p.1.WF (I.n - 1) ∧ 1 ≤ p.2 ∧ p.2 ≤ I.n

/-- Instance code: `n` and `r` in unary, then the list of predictors, each written as the code
of its circuit followed by its index (`encNat`). -/
def UnpredInstance.encode (I : UnpredInstance) : List Bool :=
  encUnary I.n ++ encUnary I.r ++ encList (fun p => p.1.encode ++ encNat p.2) I.preds

/-- The `j`-th predictor of a well-formed instance, as a middle-bit predictor over `{0,1}ⁿ`:
the function computed by its circuit, at the 0-based index `indⱼ − 1`. (The fallback index `0`
is never used on a well-formed instance, where `1 ≤ indⱼ ≤ n`.) -/
def UnpredInstance.predictor (I : UnpredInstance) (h : I.WF) (j : Fin I.preds.length) :
    MiddleBitPredictor I.n where
  ind := if hj : (I.preds.get j).2 - 1 < I.n then ⟨(I.preds.get j).2 - 1, hj⟩ else ⟨0, h.1⟩
  P := fun s => (I.preds.get j).1.eval (List.ofFn s)

/-- Answer code: the list of the strings of the multiset (any order, repetitions for
multiplicity), each written as its `n` bits. -/
def encStrings {n : ℕ} (L : List (Fin n → Bool)) : List Bool :=
  encList (fun s => List.ofFn s) L

/-- **UNPRED** (Definition 2.4). Valid instances are the codes of well-formed instances. An
answer to the instance coded by `s` is the code of a non-empty multiset `S ⊆ {0,1}ⁿ` with
`adv_{U(S)}({P₁, …, P_m}) < 1/r`. The output size is not bounded. -/
noncomputable def UNPRED : TetrisHard.Rows.SearchProblem where
  valid s := ∃ I : UnpredInstance, I.WF ∧ s = I.encode
  answer s t := ∃ (I : UnpredInstance) (h : I.WF), s = I.encode ∧
    ∃ L : List (Fin I.n → Bool), L ≠ [] ∧ t = encStrings L ∧
      -- the family `{P₁, …, P_m}` is non-empty because `m ≥ 1` on a well-formed instance
      @advFam I.n (Fin I.preds.length) _ ⟨⟨0, List.length_pos_of_ne_nil h.2.2.1⟩⟩
        (L : Multiset (Fin I.n → Bool)) (I.predictor h) < 1 / (I.r : ℝ)

end ComplexityUnpred.Catalytic


