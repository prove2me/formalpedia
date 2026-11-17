-- Prove2me | Definitions.Def_LocalBreadth_Supplement_HistoryP
-- name    : LocalBreadth_Supplement_HistoryP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:19:56.6922+00:00
-- url     : https://prove2.me/theorems/61bc16e0-d3b2-486e-85a0-622e7b22371d
-- title:
--   Histories of languages in $\mathbb Z^d$
-- statement:
--   A **history** over a family $\mathcal X$ of languages is a finite strictly descending chain $H=(L_0\supsetneq L_1\supsetneq\dots\supsetneq L_r)$ of members of $\mathcal X$, with arbitrary starting language. Its starting language is $L_0$ and $\mathrm{end}(H)=L_r$. For $M\in\mathcal X$ with $M\subsetneq\mathrm{end}(H)$, $H^\frown M$ appends $M$.
--
--   This is the published one-dimensional `LocalBreadth.History` over an arbitrary universe of strings, needed for languages in $\mathbb Z^d$ in §7.
--
--   **Formalization Note** The chain is a nonempty list, starting language first; the universe $P$ is a parameter.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), §5.3.2, p.25; §7.3, p.55 and p.57

import Mathlib

namespace LocalBreadth.Supplement

/-- A **history** over a family `X` of languages in a universe `P` (pp.14, 25, 57): a finite strictly
descending chain `L₀ ⊋ L₁ ⊋ ⋯ ⊋ L_r` of languages of `X`, with arbitrary starting language.
Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), §5.3.2, p.25; §7.3, p.55.

**Formalization Note.** The published `LocalBreadth.History` with `ℤ` replaced by a universe `P`
(§7 uses `P = Fin d → ℤ`; "this topology does not depend on the dimension", p.57). -/
@[ext] structure HistoryP (P : Type) (X : Set (Set P)) where
  /-- The chain, starting language first. -/
  chain : List (Set P)
  ne_nil : chain ≠ []
  mem : ∀ L ∈ chain, L ∈ X
  desc : chain.IsChain (fun A B => B ⊂ A)

namespace HistoryP

variable {P : Type} {X : Set (Set P)}

/-- The starting language. -/
def first (H : HistoryP P X) : Set P := H.chain.head H.ne_nil

/-- `end(H)`, the last language. -/
def last (H : HistoryP P X) : Set P := H.chain.getLast H.ne_nil

/-- `H⌢M`: the one-step extension by a language `M ∈ X` with `M ⊊ end(H)`. -/
def snoc (H : HistoryP P X) (M : Set P) (hM : M ∈ X) (hlt : M ⊂ H.last) : HistoryP P X where
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

end HistoryP

end LocalBreadth.Supplement


