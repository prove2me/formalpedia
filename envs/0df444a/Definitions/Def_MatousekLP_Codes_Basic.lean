-- Prove2me | Definitions.Def_MatousekLP_Codes_Basic
-- name    : MatousekLP_Codes_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T12:51:20.253598+00:00
-- url     : https://prove2.me/theorems/528c1c04-88ce-4d83-9321-6f4a0f76bb1a
-- title:
--   Definition 8.4.1 — binary codes, Hamming distance, codes of distance d, and A(n, d)
-- statement:
--   A **word** of length $n$ is an element $\mathbf w = (w_1,\dots,w_n)$ of $\{0,1\}^n$, and a **code** is any subset $C \subseteq \{0,1\}^n$. For words $\mathbf w, \mathbf w'$:
--
--   1. the **Hamming distance** $d_H(\mathbf w,\mathbf w') = |\{j : w_j \ne w'_j\}|$ is the number of positions in which they differ;
--   2. the **weight** $|\mathbf w| = |\{j : w_j = 1\}|$ is the number of ones of $\mathbf w$;
--   3. the **sum modulo 2** $\mathbf w \oplus \mathbf w'$ is the word with $j$th entry $(w_j + w'_j) \bmod 2$;
--   4. the **scalar product** $\mathbf u^T \mathbf v$ of two words, regarded as 0/1 vectors, is the number of positions where both have a one;
--   5. for a set of indices $I \subseteq \{1,\dots,n\}$, the **restricted Hamming distance** $d_H^I(\mathbf w,\mathbf w')$ is the number of indices $i \in I$ with $w_i \ne w'_i$.
--
--   **Definition 8.4.1.** A code $C$ **has distance** $d$ if $d_H(\mathbf w,\mathbf w') \ge d$ for any two distinct words $\mathbf w,\mathbf w' \in C$. For $n, d \ge 0$,
--   $$
--   A(n,d) = \max\{\, |C| : C \subseteq \{0,1\}^n \text{ has distance } d \,\}.
--   $$
--
--   Determining or estimating $A(n,d)$ is one of the main problems of coding theory; all results of the mission are upper bounds on it or the identities used to derive them.
--
--   **Formalization Note** Words are `Fin n → Bool` (bit $1$ is `true`; the book's positions $1,\dots,n$ are `0, …, n-1`), codes are `Finset`s of words, and $d_H$ is Mathlib's `hammingDist`. $A(n,d)$ is the `Finset.sup` of the cardinality over the finite family of all codes with distance $d$; this family contains the empty code, so the supremum is an attained maximum.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 157 (Hamming distance, weight, sum modulo 2), p. 158, Definition 8.4.1, p. 161 (restricted distance d_H^I), p. 161, Corollary 8.4.6 (scalar product)

import Mathlib

open Finset

namespace MatousekLP.Codes

/-- A binary word of length `n`, an element of `{0,1}^n` (Matoušek–Gärtner, §8.4, p. 157).
The book's bit `1` is `true`, its bit `0` is `false`; the book's positions `1, …, n` are
`0, …, n-1`. A code is a `Finset (Word n)`. -/
abbrev Word (n : ℕ) := Fin n → Bool

/-- The weight `|w|` of a word: the number of positions `j` with `w_j = 1` (p. 157). -/
def weight {n : ℕ} (w : Word n) : ℕ := #{j | w j = true}

/-- The sum modulo 2 `w ⊕ w'` of two words, computed position by position (p. 157). -/
def xorWord {n : ℕ} (w w' : Word n) : Word n := fun j => xor (w j) (w' j)

/-- The scalar product `uᵀ v` of two words regarded as 0/1 vectors: the number of positions
where both `u` and `v` have a `1` (used in Corollary 8.4.6, p. 161). -/
def dot {n : ℕ} (u v : Word n) : ℕ := #{j | u j = true ∧ v j = true}

/-- The restricted Hamming distance `d_H^I(w, w')`: the number of indices `i ∈ I` with
`w_i ≠ w'_i`; components outside `I` are ignored (p. 161). -/
def restrictedDist {n : ℕ} (I : Finset (Fin n)) (w w' : Word n) : ℕ := #{i ∈ I | w i ≠ w' i}

/-- Definition 8.4.1 (p. 158): a code `C ⊆ {0,1}^n` has distance `d` if `d_H(w, w') ≥ d`
for any two distinct words `w, w'` of `C`. The Hamming distance `d_H` is Mathlib's
`hammingDist`, the number of positions in which the two words differ. -/
def HasDistance {n : ℕ} (C : Finset (Word n)) (d : ℕ) : Prop :=
  ∀ w ∈ C, ∀ w' ∈ C, w ≠ w' → d ≤ hammingDist w w'

open Classical in
/-- Definition 8.4.1 (p. 158): `A(n, d)`, the maximum cardinality of a code `C ⊆ {0,1}^n` with
distance `d`, written as the supremum of `|C|` over the finite family of all such codes. This
family always contains the empty code, so the supremum is an attained maximum. -/
noncomputable def A (n d : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Word n))).filter (fun C => HasDistance C d)).sup Finset.card

end MatousekLP.Codes


