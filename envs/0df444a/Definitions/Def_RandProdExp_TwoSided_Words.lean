-- Prove2me | Definitions.Def_RandProdExp_TwoSided_Words
-- name    : RandProdExp_TwoSided_Words
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:17:50.392198+00:00
-- url     : https://prove2.me/theorems/e385edb5-b54c-42cb-9b2f-13ce1578169c
-- title:
--   Words, weak Wigner words, equivalence classes, and the bipartite walks of Definition 8.4 with $W_p(\Delta)$ (Definitions 8.4, 8.10–8.23)
-- statement:
--   A **word** is a nonempty finite sequence of letters from an alphabet (Definition 8.10); it is **closed** if its first and last letters agree. Its **support** is the set of its letters and its **weight** $\mathrm{wt}(w)$ the number of distinct letters (Definition 8.11). The graph $\Gamma_w$ has vertex set the support and edges the distinct undirected pairs $\{w_i,w_{i+1}\}$ (Definition 8.12). A **weak Wigner word** is a closed word that traverses each edge of $\Gamma_w$ at least twice (Definition 8.13). Two words $w,w'$ of equal length are **equivalent** if a bijection $\psi:\operatorname{supp}(w)\to\operatorname{supp}(w')$ has $\psi(w_i)=w'_i$ for every $i$ (Definition 8.14).
--
--   For integers $p\ge1$ and $\Delta\ge0$, the walks of Definition 8.4 are words $w=(w_0,\dots,w_{4p})$ over the letters $(L,x)$, $x\in[n]$, and $(R,r)$, $r\in[k]$, with left letters exactly at even positions. Such a walk is **non-left-backtracking** if at each right vertex the preceding and following left vertices differ, **even** if every edge is traversed an even number of times, and its **deficiency** is $\Delta(w)=2p+1-\mathrm{wt}(w)$ (Definition 8.20). $W_p(\Delta)$ is the set of equivalence classes of even non-left-backtracking closed walks of length $4p+1$ with these left and right positions and deficiency $\Delta$ (Definition 8.23).
--
--   These are the combinatorial objects of the trace-moment count in §8: the number of such classes bounds the expected trace of a power of the sparse blocks.
--
--   **Formalization Note** A word of length $N+1$ over `α` is `Fin (N + 1) → α`. The number of traversals of an edge counts the steps $i$ with $\{w_i,w_{i+1}\}=e$ as `Sym2`. An equivalence class is the set of all words equivalent to a representative; `wignerClasses α N W` and `walkClasses n k p Δ` are the sets of such classes. The alphabet of Definition 8.4 is `Fin n ⊕ Fin k` (`Sum.inl` = left letter, `Sum.inr` = right letter).
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), pp. 57–60, Definitions 8.4, 8.10–8.14, 8.19–8.20, 8.23

import Mathlib

namespace RandProdExp.TwoSided

/-!
# Words, weak Wigner words, equivalence classes, and the bipartite walks of Definition 8.4

Chattopadhyay, Ringach, Spooner, *Product Expansion of Random Codes via Analytic Techniques*,
STOC 2027 submission, §8.2–§8.4, pp. 57–60: Definitions 8.4, 8.10–8.14, 8.19–8.20, 8.23.

A word of length `N + 1` over an alphabet `α` is a function `Fin (N + 1) → α` (words are nonempty).
-/

/-- Words of length `N + 1` over the alphabet `α` (Definition 8.10). -/
abbrev Word (α : Type) (N : ℕ) := Fin (N + 1) → α

variable {α : Type} {N : ℕ}

/-- A word is **closed** if its first and last letters agree (Definition 8.10). -/
def IsClosedWord (w : Word α N) : Prop := w 0 = w (Fin.last N)

/-- The **weight** `wt(w) = |supp(w)|`, the number of distinct letters (Definition 8.11). -/
noncomputable def wordWeight (w : Word α N) : ℕ := (Set.range w).ncard

/-- The `i`-th step `{w_i, w_{i+1}}` of the word, as an undirected edge of its graph `Γ_w`
(Definition 8.12; the edges of `Γ_w` are the steps). -/
def wordEdge (w : Word α N) (i : Fin N) : Sym2 α := s(w i.castSucc, w i.succ)

open Classical in
/-- The number of times the word traverses the undirected edge `e` (in either direction). -/
noncomputable def traversals (w : Word α N) (e : Sym2 α) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => wordEdge w i = e)).card

/-- **Weak Wigner word** (Definition 8.13): closed, and every edge of `Γ_w` is traversed at least
twice. -/
def IsWeakWigner (w : Word α N) : Prop :=
  IsClosedWord w ∧ ∀ i : Fin N, 2 ≤ traversals w (wordEdge w i)

/-- **Equivalence** of words of equal length (Definition 8.14): a bijection
`ψ : supp(w) → supp(w')` with `ψ(w_i) = w'_i` for every position `i`. -/
def WordEquiv (w w' : Word α N) : Prop :=
  ∃ ψ : Set.range w → Set.range w', Function.Bijective ψ ∧
    ∀ i : Fin (N + 1), (ψ ⟨w i, i, rfl⟩ : α) = w' i

/-- The set of equivalence classes of weak Wigner words of length `N + 1` and weight `W` over the
alphabet `α` (Proposition 8.25), each class as the set of words equivalent to a representative. -/
def wignerClasses (α : Type) (N W : ℕ) : Set (Set (Word α N)) :=
  {S | ∃ w : Word α N, IsWeakWigner w ∧ wordWeight w = W ∧ S = {w' | WordEquiv w w'}}

/-- The words of Definition 8.4: length `4p + 1` over the alphabet `({L} × [n]) ⊔ ({R} × [k])`
(`Sum.inl` = left letter `(L, x)`, `Sum.inr` = right letter `(R, r)`), with left letters exactly at
the even positions and right letters at the odd positions. -/
def IsBipartiteShape {n k p : ℕ} (w : Word (Fin n ⊕ Fin k) (4 * p)) : Prop :=
  ∀ i : Fin (4 * p + 1), Even i.val ↔ (w i).isLeft = true

/-- **Non-left-backtracking** (Lemma 8.6, footnote 11): at each visit to a right vertex (odd
position `i`), the preceding and following left vertices differ. -/
def IsNonLeftBacktracking {n k p : ℕ} (w : Word (Fin n ⊕ Fin k) (4 * p)) : Prop :=
  ∀ i : ℕ, ∀ h : i + 1 < 4 * p + 1, Odd i →
    w ⟨i - 1, by omega⟩ ≠ w ⟨i + 1, h⟩

/-- **Even** walk (Corollary 8.9): every edge of `Γ_w` is traversed an even number of times. -/
def IsEvenWalk {n k p : ℕ} (w : Word (Fin n ⊕ Fin k) (4 * p)) : Prop :=
  ∀ i : Fin (4 * p), Even (traversals w (wordEdge w i))

/-- `W_p(Δ)` (Definition 8.23): the equivalence classes of even non-left-backtracking closed walks
of length `4p + 1` with left and right positions as in Definition 8.4 and deficiency
`Δ(w) = 2p + 1 − wt(w)` (Definition 8.20) equal to `Δ`. -/
def walkClasses (n k p Δ : ℕ) : Set (Set (Word (Fin n ⊕ Fin k) (4 * p))) :=
  {S | ∃ w : Word (Fin n ⊕ Fin k) (4 * p), IsBipartiteShape w ∧ IsClosedWord w ∧
    IsNonLeftBacktracking w ∧ IsEvenWalk w ∧
    (2 * p + 1 : ℤ) - (wordWeight w : ℤ) = (Δ : ℤ) ∧ S = {w' | WordEquiv w w'}}

end RandProdExp.TwoSided


