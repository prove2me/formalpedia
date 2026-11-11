-- Prove2me | Definitions.Def_ComplexityUnpred_Catalytic_Predictor
-- name    : ComplexityUnpred_Catalytic_Predictor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:01:54.872485+00:00
-- url     : https://prove2.me/theorems/77d7953d-2efa-4c68-b860-36d472883841
-- title:
--   Middle-bit predictors, success and advantage on a multiset (Definitions 2.2–2.3)
-- statement:
--   An **$n$-bit string** is $s\in\{0,1\}^n$, written $s_1\dots s_n$. For an index $i\in[n]=\{1,\dots,n\}$, $s_{-i}=s_1\dots s_{i-1}s_{i+1}\dots s_n\in\{0,1\}^{n-1}$ is $s$ without its $i$-th bit; for $s\in\{0,1\}^{n-1}$ and a bit $b$, $s^{i,b}=s_1\dots s_{i-1}\,b\,s_i\dots s_{n-1}\in\{0,1\}^n$ inserts $b$ at position $i$; and $v\oplus i$ is $v$ with its $i$-th bit flipped.
--
--   A **middle-bit predictor over $\{0,1\}^n$ at index $\mathrm{ind}\in[n]$** is a function $P:\{0,1\}^{n-1}\to\{0,1\}$; it **succeeds** on $s\in\{0,1\}^n$ if $P(s_{-\mathrm{ind}})=s_{\mathrm{ind}}$.
--
--   For a non-empty finite multiset $S\subseteq\{0,1\}^n$, $U(S)$ is the uniform distribution on $S$ (each element with probability proportional to its multiplicity). The **success** and **advantage** of $P$ on $U(S)$ are
--   $$\mathrm{succ}_{U(S)}(P)=\Pr_{s\sim U(S)}[P\text{ succeeds on }s]=\frac{\#\{s\in S: P\text{ succeeds on }s\}}{|S|},\qquad \mathrm{adv}_{U(S)}(P)=\max\Big\{0,\ \mathrm{succ}_{U(S)}(P)-\tfrac12\Big\},$$
--   counting with multiplicity, and for a non-empty finite family $\mathcal P$ of predictors $\mathrm{adv}_{U(S)}(\mathcal P)=\max_{P\in\mathcal P}\mathrm{adv}_{U(S)}(P)$. For a family of tests $(T_i)_{i\in\iota}$ (each the set of strings a predictor succeeds on), $\Pr_{i\in\iota}[T_i(s)]$ is the fraction of indices $i$ with $T_i(s)$, families being uniform over their index set (repetitions counted).
--
--   These are the objects of UNPRED: a solution is a multiset on which no predictor of the given family beats a coin by $\epsilon$.
--
--   **Formalization Note** Strings are `Fin n → Bool`, indices are 0-based (`Fin n`; the paper's index $i$ is `i - 1`). Multisets are Mathlib `Multiset`s. `probOn S T` is $\Pr_{s\sim U(S)}[T(s)]$ (it is $0$ for $S=\emptyset$, and every statement using it assumes $S\neq\emptyset$); `famProb`, `testAdv`, `testAdvFam` are the same notions for an arbitrary family of success tests, and `succ`, `adv`, `advFam` specialise them to `MiddleBitPredictor`s. Families are indexed by a non-empty `Fintype`, so the maximum is a `Finset.sup'` over a non-empty set. Values are real numbers.
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, pp. 17, 19, 31, Definitions 2.2, 2.3 and the notation of §2.1 and §4.1

import Mathlib

namespace ComplexityUnpred.Catalytic

/-! Agarwala, Dorfman, *The Complexity of Unpredictability*, arXiv:2611.05956v1, §2.1 (p. 17),
Definitions 2.2–2.3 (p. 19), and the notation `s^{i,b}` of §4.1 (p. 31).

An `n`-bit string is a function `Fin n → Bool`; the paper's index `i ∈ [n] = {1, …, n}` is the
Lean index `i - 1 : Fin n` (0-based). A finite multiset of strings is a Mathlib `Multiset`, and
`U(S)` (sampling with probability proportional to multiplicity) is the counting average over it. -/

/-- `s₋ᵢ`: the string `s ∈ {0,1}ⁿ` without its character at index `i` (p. 17). -/
def eraseAt {n : ℕ} (s : Fin n → Bool) (i : Fin n) : Fin (n - 1) → Bool :=
  fun j => if j.val < i.val then s ⟨j.val, by have h1 := j.isLt; omega⟩
    else s ⟨j.val + 1, by have h1 := j.isLt; omega⟩

/-- `s^{i,b} := s₁ … s_{i−1} ∘ b ∘ sᵢ … s_{n−1}`: the bit `b` inserted at index `i` of the
`(n−1)`-bit string `s` (§4.1, p. 31). -/
def insertAt {n : ℕ} (s : Fin (n - 1) → Bool) (i : Fin n) (b : Bool) : Fin n → Bool :=
  fun j => if h : j.val < i.val then s ⟨j.val, by have h1 := i.isLt; omega⟩
    else if h' : j.val = i.val then b
    else s ⟨j.val - 1, by have h1 := j.isLt; omega⟩

/-- `v ⊕ i`: the string `v` with its bit at index `i` flipped (p. 33). -/
def flipAt {n : ℕ} (v : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update v i (!v i)

/-- `Pr_{s ∼ U(S)}[T(s)]`: the fraction of the elements of the multiset `S`, counted with
multiplicity, on which the test `T` holds. (Only used for non-empty `S`; for `S = ∅` the
value is `0/0 = 0`, so every statement that uses it assumes `S ≠ 0`.) -/
noncomputable def probOn {α : Type} (S : Multiset α) (T : α → Bool) : ℝ :=
  (S.countP (fun s => T s = true) : ℝ) / (S.card : ℝ)

/-- `Pr_{i ∈ ι}[T_i(s)]`: the fraction of the indices `i` of a finite indexed family of tests
for which `T_i(s)` holds (the family is uniform over its index set, repetitions counted). -/
noncomputable def famProb {ι α : Type} [Fintype ι] (T : ι → α → Bool) (s : α) : ℝ :=
  ((Finset.univ.filter (fun i => T i s = true)).card : ℝ) / (Fintype.card ι : ℝ)

/-- The advantage `max{0, Pr_{s∼U(S)}[T(s)] − 1/2}` of a success test `T` on `U(S)`
(Definition 2.3, for any kind of predictor, given by the set of strings it succeeds on). -/
noncomputable def testAdv {α : Type} (S : Multiset α) (T : α → Bool) : ℝ :=
  max 0 (probOn S T - 1 / 2)

/-- The advantage of a non-empty finite family of success tests on `U(S)`: the maximum of the
advantages of its members (Definition 2.3). -/
noncomputable def testAdvFam {ι α : Type} [Fintype ι] [Nonempty ι] (S : Multiset α)
    (T : ι → α → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => testAdv S (T i))

/-- **Definition 2.2** (p. 19). A middle-bit predictor over `{0,1}ⁿ` at index `ind ∈ [n]` is a
function `P : {0,1}^{n−1} → {0,1}`; here it carries its index. -/
structure MiddleBitPredictor (n : ℕ) where
  /-- The predicted index (0-based: the paper's `ind` is `ind.val + 1`). -/
  ind : Fin n
  /-- The predicting function `{0,1}^{n−1} → {0,1}`. -/
  P : (Fin (n - 1) → Bool) → Bool

/-- `P` succeeds on `s ∈ {0,1}ⁿ` if `P(s₋ind) = s_ind` (Definition 2.2). -/
def MiddleBitPredictor.succeeds {n : ℕ} (P : MiddleBitPredictor n) (s : Fin n → Bool) : Bool :=
  P.P (eraseAt s P.ind) == s P.ind

/-- `succ_{U(S)}(P) := Pr_{s∼U(S)}[P succeeds on s]` (Definition 2.3). -/
noncomputable def succ {n : ℕ} (S : Multiset (Fin n → Bool)) (P : MiddleBitPredictor n) : ℝ :=
  probOn S P.succeeds

/-- `adv_{U(S)}(P) := max{0, succ_{U(S)}(P) − 1/2}` (Definition 2.3). -/
noncomputable def adv {n : ℕ} (S : Multiset (Fin n → Bool)) (P : MiddleBitPredictor n) : ℝ :=
  testAdv S P.succeeds

/-- `adv_{U(S)}(𝒫) := max_{P ∈ 𝒫} adv_{U(S)}(P)` for a non-empty finite indexed family `𝒫`
(Definition 2.3). -/
noncomputable def advFam {n : ℕ} {ι : Type} [Fintype ι] [Nonempty ι]
    (S : Multiset (Fin n → Bool)) (P : ι → MiddleBitPredictor n) : ℝ :=
  testAdvFam S (fun i => (P i).succeeds)

end ComplexityUnpred.Catalytic


