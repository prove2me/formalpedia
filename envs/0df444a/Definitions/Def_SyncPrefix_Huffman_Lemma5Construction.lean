-- Prove2me | Definitions.Def_SyncPrefix_Huffman_Lemma5Construction
-- name    : SyncPrefix_Huffman_Lemma5Construction
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-27T06:14:35.931616+00:00
-- url     : https://prove2.me/theorems/60cbc041-1660-46cd-a84f-7e34e0c69391
-- title:
--   Lemma 5 Huffman Decoder Construction from a Strongly Acyclic Synchronizing Automaton
-- statement:
--   Given a complete deterministic automaton $A = (Q, \Sigma, \delta)$ with $n$ states and $k$ letters, `huffmanOfStronglyAcyclic A` constructs the automaton $A_H$ over $k + 2$ letters from the proof of Lemma 5 (Ryzhikov–Szykuła 2018, p. 6). When $n \ge 2$ and $k \ge 1$, let $f = \mathrm{sinkOf}(A)$ be the sink state of $A$ and $S = \mathrm{sourcesOf}(A, f)$ be the list of non-sink states with in-degree $0$ in $A$. The automaton $A_H$ has $2n$ states (the $n$ original states of $A$ together with $n$ auxiliary tree states) and $k + 2$ letters ($\Sigma \cup \{b_1, b_2\}$): original letters act as $\delta$ on $Q$ and map all auxiliary states to $f$; on $Q \setminus \{f\}$, the new letters $b_1, b_2$ act identically to letter $0 \in \Sigma$; from $f$, $b_1$ and $b_2$ enter a delay stem of $n - |S|$ auxiliary states followed by $|S|$ caterpillar tree states whose leaves under $b_1$ are the source states in $S$.
-- source:
--   Ryzhikov–Szykuła 2018, Synchronizing Prefix Codes and Huffman’s Algorithm, arXiv:1806.06299v1, p. 6, Lemma 5

import Definitions.Def_SyncPrefix_Huffman_Automata

namespace SyncPrefix.Huffman

/-- First sink state of `A` in `Fin A.n` (with `h : 0 < A.n`), or `0` if none exists. -/
def sinkOf (A : Automaton) (h : 0 < A.n) : Fin A.n :=
  match ((List.finRange A.n).filter fun q =>
      (List.finRange A.k).all fun a => decide (A.δ q a = q)).head? with
  | some q => q
  | none => ⟨0, h⟩

/-- List of non-sink source states of `A` (states `q ≠ f` with no incoming transitions in `A`). -/
def sourcesOf (A : Automaton) (f : Fin A.n) : List (Fin A.n) :=
  (List.finRange A.n).filter fun q =>
    decide (q ≠ f) &&
      (List.finRange A.n).all fun p =>
        (List.finRange A.k).all fun a => decide (A.δ p a ≠ q)

/-- Construction for Lemma 5 (p. 6): converts a synchronizing strongly acyclic automaton `A`
into a Huffman decoder over `A.k + 2` letters with the same shortest synchronizing word length
and between `A.n` and `2 * A.n` states. -/
def huffmanOfStronglyAcyclic (A : Automaton) : Automaton :=
  if h : 2 ≤ A.n ∧ 1 ≤ A.k then
    let hn : 0 < A.n := by omega
    let hk : 0 < A.k := by omega
    let f : Fin A.n := sinkOf A hn
    let S : List (Fin A.n) := sourcesOf A f
    let d : ℕ := A.n - S.length
    { n := 2 * A.n
      k := A.k + 2
      δ := fun q a =>
        if hq : q.val < A.n then
          let q₀ : Fin A.n := ⟨q.val, hq⟩
          if ha : a.val < A.k then
            let q' := A.δ q₀ ⟨a.val, ha⟩
            ⟨q'.val, by omega⟩
          else if q₀ = f then
            ⟨A.n, by omega⟩
          else
            let q' := A.δ q₀ ⟨0, hk⟩
            ⟨q'.val, by omega⟩
        else
          let i : ℕ := q.val - A.n
          if _ha : a.val < A.k then
            ⟨f.val, by omega⟩
          else if i < d then
            if hnext : i + 1 < A.n then
              ⟨A.n + (i + 1), by omega⟩
            else
              ⟨f.val, by omega⟩
          else
            let j : ℕ := i - d
            let s_j : Fin A.n := S.getD j f
            if a.val = A.k then
              ⟨s_j.val, by omega⟩
            else if hnext : i + 1 < A.n then
              ⟨A.n + (i + 1), by omega⟩
            else
              ⟨s_j.val, by omega⟩ }
  else
    { n := A.n
      k := A.k + 2
      δ := fun q _ => q }

@[simp]
theorem huffmanOfStronglyAcyclic_k (A : Automaton) :
    (huffmanOfStronglyAcyclic A).k = A.k + 2 := by
  unfold huffmanOfStronglyAcyclic
  split_ifs <;> rfl

theorem le_huffmanOfStronglyAcyclic_n (A : Automaton) :
    A.n ≤ (huffmanOfStronglyAcyclic A).n := by
  unfold huffmanOfStronglyAcyclic
  split_ifs <;> dsimp <;> omega

theorem huffmanOfStronglyAcyclic_n_le (A : Automaton) :
    (huffmanOfStronglyAcyclic A).n ≤ 2 * A.n := by
  unfold huffmanOfStronglyAcyclic
  split_ifs <;> dsimp <;> omega

end SyncPrefix.Huffman


