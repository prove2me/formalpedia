-- Prove2me | Definitions.Def_PolyTimeMBLG_Monotone_Generation
-- name    : PolyTimeMBLG_Monotone_Generation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:36.611876+00:00
-- url     : https://prove2.me/theorems/3d8704d8-0096-4598-84a3-80f5a55599e4
-- title:
--   §3, Definitions 5–6 — generators, mistakes and polynomial-time MBLG
-- statement:
--   These definitions set up the polynomial-time mistake-bounded language generation (MBLG) model of §3.
--
--   A **word** of length $n$ is an element of $\{0,1\}^n$, and a **language** is a subset $L\subseteq\{0,1\}^n$. A **history** consists of a length $n$ (given in unary) and a finite sequence $x^1,\dots,x^i$ of pairwise distinct words of length $n$. A **generator** $G$ assigns to every history a word $G(1^n,x^1\cdots x^i)$ of length $n$.
--
--   Histories are written for a machine over the alphabet $\{0,1,\#\}$: first $n$ copies of $1$, then $\#$, then each word's $n$ bits followed by $\#$. A history of $i$ words of length $n$ is a string of length $(n+1)(i+1)$. The generator is **polynomial-time** when one Turing machine (a finite multi-stack machine in the sense of Mathlib's `TM2`) and one polynomial $P$ with natural coefficients are such that, on every encoded history $w$, the machine halts with the $n$ output bits within $P(|w|)$ steps.
--
--   Given a language $L$ and an enumeration $x^1,\dots,x^{|L|}$ of $L$ (all words of $L$, each exactly once), an index $i\in\{0,1,\dots,|L|-1\}$ is a **mistake** of $G$ when
--   $$G(1^n,x^1\cdots x^i)\notin L\setminus\{x^1,\dots,x^i\}.$$
--   For a sequence $\{F_n\}_{n\ge1}$ of families of languages ($F_n$ a set of languages in $\{0,1\}^n$) and a bound $e(n)$, $G$ **makes at most $e(n)$ mistakes** on $\{F_n\}$ if for every $n\ge1$, every $L\in F_n$ and every enumeration of $L$, the number of mistakes is at most $e(n)$ (Definition 5).
--
--   The sequence is **polynomial-time MBLG** (Definition 6) if $|F_n|\le 2^{q(n)}$ for some polynomial $q$ and all $n\ge1$, and some polynomial-time generator makes at most $e(n)$ mistakes for some polynomial $e$. The variant *polynomial-time MBLG with bound $e$* requires the same with a given bound $e:\mathbb N\to\mathbb R$.
--
--   These are the objects in which the paper's upper bounds are stated; the generator receives only $n$ and the words printed so far, never the target language or any feedback.
--
--   **Formalization Note** Words are `Fin n → Bool`; histories are `Σ n, {xs : List (Fin n → Bool) // xs.Nodup}`, so the generator is required exactly on sequences of distinct words. The encoding uses the alphabet `Option Bool` (`some true` for the unary digit, `none` as separator, `some b` for a bit) and the output is the bit list of the word. Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime`, wrapped in `Nonempty`; its polynomial is evaluated at the encoding length $(n+1)(i+1)$, which for $n\ge1$ is within a factor 2 of the paper's $n(i+1)$. Languages are `Finset`s, enumerations are duplicate-free lists whose set of entries is $L$, and the mistake count ranges over $i<|L|$. The mistake bound $e$ is real-valued; when $e(n)\ge0$, a natural mistake count is at most $e(n)$ exactly when it is at most the natural floor $\lfloor e(n)\rfloor$. A negative bound fails for every language at that dimension, even an empty language, whereas an empty family imposes no mistake constraint. The word "purple" printed in Definition 5 is a typesetting artefact and is omitted.
-- source:
--   Héctor Jimenez, Alexander Kozachinskiy, Vicente Opazo, STOC 2027 submission #402 (October 2026), §3 (generator), Definition 5 and Definition 6, p. 5; time bound poly(n(i+1)) from §1, p. 3. PDF SHA-256 2e6ec485290626cb762f55f7c45588eeb0047572a27748b20af18d34ebad7511, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/402.pdf

import Mathlib

namespace PolyTimeMBLG.Monotone

/-- A history handed to a generator (§3, p. 5): a word length `n` (given in unary) and a
duplicate-free finite sequence `x¹, …, xⁱ` of binary words of length `n`, in the order printed.
A word of length `n` is a function `Fin n → Bool`. -/
def History : Type := Σ n : ℕ, {xs : List (Fin n → Bool) // xs.Nodup}

/-- A generator (§3, p. 5): a function that takes `1ⁿ` and a sequence of distinct binary words
of length `n` and returns a binary word of length `n`. The output type forces length `n`. -/
def Generator : Type := (h : History) → (Fin h.1 → Bool)

/-- Input encoding over the finite alphabet `Option Bool`: `n` copies of `some true` (the unary
length), then `none`, then for each word in order its bits `some b₁, …, some bₙ` followed by
`none`. A history of `i` words of length `n` has an encoding of length `(n + 1) * (i + 1)`. -/
def encodeHistory (h : History) : List (Option Bool) :=
  List.replicate h.1 (some true) ++
    none :: h.2.1.flatMap (fun x => (List.ofFn x).map some ++ [none])

/-- The generator's output word as a raw list of `n` bits. -/
def Generator.outputBits (G : Generator) (h : History) : List Bool :=
  List.ofFn (G h)

/-- `G` is a polynomial-time generator: one finite TM2 machine computes the output bits of `G`
from the encoded history within `P(length of the encoding)` steps, for one polynomial `P`,
on every history. -/
def Generator.IsPolyTime (G : Generator) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encodeHistory id G.outputBits)

/-- Definition 5, p. 5: the number of indices `i ∈ {0, 1, …, |L| - 1}` at which the generator,
shown the first `i` words of the enumeration `xs`, outputs a word outside `L \ {x¹, …, xⁱ}`. -/
def mistakeCount (G : Generator) {n : ℕ} (L : Finset (Fin n → Bool))
    (xs : List (Fin n → Bool)) (hxs : xs.Nodup) : ℕ :=
  ((Finset.range L.card).filter (fun i =>
    G ⟨n, ⟨xs.take i, hxs.sublist (List.take_sublist i xs)⟩⟩ ∉
      L \ (xs.take i).toFinset)).card

/-- A sequence of families of languages: for every `n`, a set of languages `L ⊆ {0,1}ⁿ`. -/
abbrev FamilySeq : Type := (n : ℕ) → Set (Finset (Fin n → Bool))

/-- Definition 5, p. 5: `G` makes at most `e(n)` mistakes on `{Fₙ}`: for every `n ≥ 1`, every
`L ∈ Fₙ`, and every enumeration `x¹, …, x^{|L|}` of `L` (a duplicate-free list whose set of
entries is `L`), at most `e(n)` indices are mistakes. -/
def MakesAtMostMistakes (G : Generator) (F : FamilySeq) (e : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ L ∈ F n, ∀ (xs : List (Fin n → Bool)) (hxs : xs.Nodup),
    xs.toFinset = L → (mistakeCount G L xs hxs : ℝ) ≤ e n

/-- The size condition of Definition 6, p. 5: `|Fₙ| ≤ 2^{q(n)}` for a polynomial `q` and all
`n ≥ 1`. (Each `Fₙ` is a set of subsets of a finite cube, hence finite.) -/
def HasExpSize (F : FamilySeq) : Prop :=
  ∃ q : Polynomial ℕ, ∀ n : ℕ, 1 ≤ n → (F n).ncard ≤ 2 ^ q.eval n

/-- Definition 6, p. 5, with an explicit mistake bound `e`: the family has size `2^{poly(n)}`
and admits one polynomial-time generator making at most `e(n)` mistakes. -/
def IsPolyTimeMBLGWith (F : FamilySeq) (e : ℕ → ℝ) : Prop :=
  HasExpSize F ∧ ∃ G : Generator, G.IsPolyTime ∧ MakesAtMostMistakes G F e

/-- Definition 6, p. 5: the family is polynomial-time MBLG (size `2^{poly(n)}`, a polynomial-time
generator making `poly(n)` mistakes). -/
def IsPolyTimeMBLG (F : FamilySeq) : Prop :=
  ∃ e : Polynomial ℕ, IsPolyTimeMBLGWith F (fun n => ((e.eval n : ℕ) : ℝ))

end PolyTimeMBLG.Monotone


