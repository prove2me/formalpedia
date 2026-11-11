-- Prove2me | Definitions.Def_LZEndAccess_Main_LZEnd
-- name    : LZEndAccess_Main_LZEnd
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:33:22.426637+00:00
-- url     : https://prove2.me/theorems/089a7788-6856-446a-a9ea-63ef807fbc7b
-- title:
--   LZ-End factorizations, phrases, r- and ℓ-values, the jump $J$, the levels $\mathbb K$, and $\mathrm{pre}$
-- statement:
--   A **string** $S[1..n]$ is a sequence of natural-number characters, read with 1-based indices: $S[i]$ for $i\in[1..n]$, where $[i..j]=\{i,\dots,j\}$ (empty if $j<i$).
--
--   An **LZ-End factorization** $\mathcal Z=P_1,\dots,P_z$ of $S$ ($z\ge 1$) is a partition of $[1..n]$ into nonempty consecutive **phrases** $P_t=S[a_t..b_t]$ with $a_1=1$, $b_z=n$ and $a_t=b_{t-1}+1$ for $t\in(1..z]$. Each phrase is either **terminal** (length one, no source) or a **reference phrase** with a **source** $P_j$, $j<t$, such that
--   $$S(b_j-|P_t|\,..\,b_j]=P_t,$$
--   i.e. an earlier copy of $P_t$ ends exactly at the end of an earlier phrase. The factorization need not be greedy, and reference phrases may have length one. In Lean a phrase is $\langle a,b,\mathrm{src}\rangle$ with $\mathrm{src}=0$ meaning "no source".
--
--   For an index $i$ in the phrase $P=S[a..b]$, the **r-value** is $r_i=b-i$ and the **ℓ-value** is $\ell_i=i-a$. For a reference phrase $P_t$ with source $P_j$, $\delta_{P_t}=b_t-b_j$, and the **jump** is $J(i)=i-\delta_P$ for $i\in P$ (undefined when $P$ has no source); $J^x$ is its $x$-fold iterate. An index $j$ is a **legal jump** for $i$ if $1\le j\le i$, $S[i]=S[j]$ and $r_j\le r_i$.
--
--   The **levels** are the real numbers $\mathbb K=\{1.5^e : e\in\mathbb N,\ 1.5^e\le n/z\}$, and $\lg=\log_2(n/z)$.
--
--   For $b\le e$, $\mathrm{pre}(b,e)=\mathrm{pre}(J(b),J(e))$ if $b$ and $e$ lie in the same phrase and that phrase has a source, and $\mathrm{pre}(b,e)=b$ otherwise; $\delta\text{-}\mathrm{pre}(b,e)=b-\mathrm{pre}(b,e)$.
--
--   **Formalization Note.** `pre` is defined by well-founded recursion on $b$; its guard also checks $J(b)<b$, which holds for every index of a reference phrase in a valid factorization ($\delta_P\ge1$ and $J(b)\ge 1$), so it changes no value there.
-- source:
--   Boneh, Gawrychowski, Random Access to LZ-End: Faster and Deterministic, arXiv:2607.14923 (sha256 3c96c6ff…), p. 4, §2 (strings, LZ-End factorization, K); p. 5, §3 (r- and ℓ-values); pp. 12–13, Definitions 4.4, 4.5, 4.8

import Mathlib

set_option autoImplicit false

namespace LZEndAccess.Main

/-!
# LZ-End factorizations, r- and ℓ-values, the jump `J`, the levels `K`, and `pre`

Boneh, Gawrychowski, *Random Access to LZ-End: Faster and Deterministic*, arXiv:2607.14923
(sha256 3c96c6ff…), §2 p. 4 (strings, LZ-End factorization, `K`), §3 p. 5 (r- and ℓ-values),
§4.2 pp. 12–13 (Definitions 4.4, 4.5, 4.8).

**Formalization Note.**
* A string `S[1..n]` is `S : List ℕ` (characters are natural numbers); `charAt S i` is the
  1-based character `S[i]` (Lean returns `0` outside `[1..n]`; it is only used inside).
* A phrase is `⟨a, b, src⟩` with `P = S[a..b]`; `src = 0` codes "no source" and `src = j ≥ 1`
  names the source phrase `P_j`. A factorization is a list `Z` of phrases; phrase `t ∈ [1..z]`
  is `ph Z t` (1-based).
* `IsLZEnd S Z` is the definition on p. 4: consecutive nonempty phrases `a₁ = 1`, `b_z = n`,
  `a_t = b_{t-1} + 1`; each phrase is terminal (`src = 0`, length one) or a reference phrase with a
  source `j < t` and `S(b_j − |P_t|..b_j] = P_t`. Greediness is not required; reference phrases of
  length one are allowed.
* `phraseIdx Z i` is the index of the phrase containing `i` (for `i ∈ [1..n]` and a valid `Z`).
* `K` (p. 4) is the set of real numbers `1.5^e`, `e ∈ ℕ`, `e ≤ log_{1.5}(n/z)`, i.e. `1.5^e ≤ n/z`.
* `pre` (Definition 4.8) is defined by well-founded recursion on `b`; its guard also asks
  `J(b) < b`, which holds for every index of a reference phrase of a valid factorization, so the
  guard changes no value on valid inputs.
-/

/-- A phrase `S[a..b]` with source index `src` (`0` = no source). -/
structure Phrase where
  a : ℕ
  b : ℕ
  src : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The length `|P| = b − a + 1` of a phrase. -/
def Phrase.len (p : Phrase) : ℕ := p.b + 1 - p.a

/-- The 1-based character `S[i]`. -/
def charAt (S : List ℕ) (i : ℕ) : ℕ := S.getD (i - 1) 0

/-- The `t`-th phrase `P_t` of `Z` (1-based). -/
def ph (Z : List Phrase) (t : ℕ) : Phrase := Z.getD (t - 1) default

/-- `Z` is an LZ-End factorization of `S` (p. 4). -/
def IsLZEnd (S : List ℕ) (Z : List Phrase) : Prop :=
  Z ≠ [] ∧ (ph Z 1).a = 1 ∧ (ph Z Z.length).b = S.length ∧
  (∀ t, 2 ≤ t → t ≤ Z.length → (ph Z t).a = (ph Z (t - 1)).b + 1) ∧
  (∀ t, 1 ≤ t → t ≤ Z.length → (ph Z t).a ≤ (ph Z t).b ∧
    (((ph Z t).src = 0 ∧ (ph Z t).a = (ph Z t).b) ∨
     (1 ≤ (ph Z t).src ∧ (ph Z t).src < t ∧ (ph Z t).len ≤ (ph Z (ph Z t).src).b ∧
      ∀ m, m < (ph Z t).len →
        charAt S ((ph Z t).a + m) =
          charAt S ((ph Z (ph Z t).src).b + 1 - (ph Z t).len + m))))

/-- Index `i` lies in phrase `t ∈ [1..z]`: `i ∈ [a_t..b_t]`. -/
def InPhrase (Z : List Phrase) (t i : ℕ) : Prop :=
  1 ≤ t ∧ t ≤ Z.length ∧ (ph Z t).a ≤ i ∧ i ≤ (ph Z t).b

instance (Z : List Phrase) (t i : ℕ) : Decidable (InPhrase Z t i) := by
  unfold InPhrase; infer_instance

/-- The index of the phrase containing `i` (the first phrase with `i ≤ b_t`). -/
def phraseIdx (Z : List Phrase) (i : ℕ) : ℕ := Z.findIdx (fun p => decide (i ≤ p.b)) + 1

/-- The r-value `r_i = b − i` (p. 5), `P = S[a..b]` the phrase containing `i`. -/
def rVal (Z : List Phrase) (i : ℕ) : ℕ := (ph Z (phraseIdx Z i)).b - i

/-- The ℓ-value `ℓ_i = i − a` (p. 5). -/
def lVal (Z : List Phrase) (i : ℕ) : ℕ := i - (ph Z (phraseIdx Z i)).a

/-- `δ_{P_t} = b_t − b_j` for the phrase `P_t` with source `P_j` (p. 12). -/
def delta (Z : List Phrase) (t : ℕ) : ℕ := (ph Z t).b - (ph Z (ph Z t).src).b

/-- The jumping rule `J(i) = i − δ_P` (Definition 4.5); undefined (`none`) when the phrase `P`
containing `i` has no source. -/
def J (Z : List Phrase) (i : ℕ) : Option ℕ :=
  if (ph Z (phraseIdx Z i)).src = 0 then none else some (i - delta Z (phraseIdx Z i))

/-- The iterate `J^x(i)` (`none` as soon as some step is undefined). -/
def Jiter (Z : List Phrase) : ℕ → ℕ → Option ℕ
  | 0, i => some i
  | x + 1, i => (Jiter Z x i).bind (J Z)

/-- `j` is a legal jump for `i` (Definition 4.4): an index `1 ≤ j ≤ i` with `S[i] = S[j]`
and `r_j ≤ r_i`. -/
def IsLegalJump (S : List ℕ) (Z : List Phrase) (i j : ℕ) : Prop :=
  1 ≤ j ∧ j ≤ i ∧ charAt S i = charAt S j ∧ rVal Z j ≤ rVal Z i

/-- The levels `K = {1.5^e | e ∈ [0..log_{1.5}(n/z)]}` (p. 4), as real numbers. -/
def Klev (n z : ℕ) : Set ℝ :=
  {k | ∃ e : ℕ, k = (3 / 2 : ℝ) ^ e ∧ (3 / 2 : ℝ) ^ e ≤ (n : ℝ) / z}

/-- `log₂(n/z)`. -/
noncomputable def lg (n z : ℕ) : ℝ := Real.logb 2 ((n : ℝ) / z)

/-- `J` with the source test removed (used only inside `pre`, where the test is made). -/
def jmp (Z : List Phrase) (i : ℕ) : ℕ := i - delta Z (phraseIdx Z i)

/-- `pre(b, e)` (Definition 4.8): if `b` and `e` lie in the same phrase `P` and `P` has a
source, `pre(b, e) = pre(J(b), J(e))`; otherwise `pre(b, e) = b`. -/
def pre (Z : List Phrase) (b e : ℕ) : ℕ :=
  if h : InPhrase Z (phraseIdx Z b) b ∧ InPhrase Z (phraseIdx Z b) e ∧
      (ph Z (phraseIdx Z b)).src ≠ 0 ∧ jmp Z b < b then
    pre Z (jmp Z b) (jmp Z e)
  else b
termination_by b
decreasing_by exact h.2.2.2

/-- `δ-pre(b, e) = b − pre(b, e)` (Definition 4.8). -/
def deltaPre (Z : List Phrase) (b e : ℕ) : ℕ := b - pre Z b e

end LZEndAccess.Main


