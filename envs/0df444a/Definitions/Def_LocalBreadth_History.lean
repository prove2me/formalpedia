-- Prove2me | Definitions.Def_LocalBreadth_History
-- name    : LocalBreadth_History
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:08.683272+00:00
-- url     : https://prove2.me/theorems/cb95a649-1a8f-45f4-b2a9-003b24771f43
-- title:
--   Histories: finite strictly descending chains of languages
-- statement:
--   A **history** over a family $\mathcal X$ is a finite strictly descending chain $H=(L_0\supsetneq L_1\supsetneq\dots\supsetneq L_d)$ of languages of $\mathcal X$, with arbitrary starting language. Its starting language is $L_0$ and $\mathrm{end}(H)=L_d$. For $M\in\mathcal X$ with $M\subsetneq\mathrm{end}(H)$, $H^\frown M$ is the history obtained by appending $M$.
--
--   Histories are the points of the topological space on which the paper's second formula for the optimal density lives.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), §2.1, p.14; §5.3.2, p.25

import Mathlib

namespace LocalBreadth

/-- A **history** over `X` (pp.14, 25): a finite strictly descending chain
`L₀ ⊋ L₁ ⊋ ⋯ ⊋ L_d` of languages of `X`, with arbitrary starting language.
Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), §2.1, p.14; §5.3.2, p.25. -/
@[ext] structure History (X : Set (Set ℤ)) where
  /-- The chain, starting language first. -/
  chain : List (Set ℤ)
  ne_nil : chain ≠ []
  mem : ∀ L ∈ chain, L ∈ X
  desc : chain.IsChain (fun A B => B ⊂ A)

namespace History

variable {X : Set (Set ℤ)}

/-- The starting language. -/
def first (H : History X) : Set ℤ := H.chain.head H.ne_nil

/-- `end(H)`, the last language. -/
def last (H : History X) : Set ℤ := H.chain.getLast H.ne_nil

/-- `H⌢M`: the one-step extension by a language `M ∈ X` with `M ⊊ end(H)`. -/
def snoc (H : History X) (M : Set ℤ) (hM : M ∈ X) (hlt : M ⊂ H.last) : History X where
  chain := H.chain ++ [M]
  ne_nil := by simp
  mem := by
    intro L hL
    rcases List.mem_append.mp hL with h | h
    · exact H.mem L h
    · rw [List.mem_singleton.mp h]; exact hM
  desc := H.desc.append (List.isChain_singleton M) (by
    intro a ha b hb
    rw [List.getLast?_eq_some_getLast H.ne_nil, Option.mem_def, Option.some.injEq] at ha
    have ha' : a = H.last := ha.symm
    have hb' : b = M := by simpa using hb.symm
    rw [ha', hb']; exact hlt)

/-- The one-language history `(K)`. -/
def single (K : Set ℤ) (hK : K ∈ X) : History X where
  chain := [K]
  ne_nil := by simp
  mem := by simpa using hK
  desc := List.isChain_singleton K

end History

end LocalBreadth


