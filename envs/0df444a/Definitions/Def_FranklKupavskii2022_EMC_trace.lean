-- Prove2me | Definitions.Def_FranklKupavskii2022_EMC_trace
-- name    : FranklKupavskii2022_EMC_trace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:13:49.55933+00:00
-- url     : https://prove2.me/theorems/690dc8d6-64b2-4eba-8876-9b094b8a3702
-- title:
--   The families $\mathcal F(S)$, $S\subseteq[s+1]$
-- statement:
--   Let $s\ge 0$ and let $\mathcal F$ be a family of finite subsets of $\{1,2,\dots\}$. For $S\subseteq[s+1]$ define
--
--   $$
--   \mathcal F(S)=\{F\setminus S : F\in\mathcal F,\ F\cap[s+1]=S\}.
--   $$
--
--   In particular $\mathcal F(\emptyset)$ is the subfamily of members of $\mathcal F$ disjoint from $[s+1]$, and $\partial\mathcal F(S)$ denotes the (immediate) shadow of $\mathcal F(S)$: all sets obtained from a member by deleting one element.
--
--   These families split $\mathcal F$ according to its trace on the first $s+1$ elements; the proof of the main theorem compares them with the corresponding families of the extremal example.
--
--   **Formalization Note** $[s+1]=\{1,\dots,s+1\}$. The shadow is Mathlib's `Finset.shadow`, which for a uniform family is exactly the immediate shadow.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Sect. 2, p. 4 (definition of F(S)); Sect. 4, p. 10

import Mathlib

namespace FranklKupavskii2022.EMC

/-- The family `F(S)` (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 2, p. 4): "For any
S ⊂ [s + 1], define the family F(S) by F(S) := {F − S : F ∈ F, F ∩ [s + 1] = S}."

**Formalization Note.** `[s + 1] = Finset.Icc 1 (s + 1)`. `F(∅)` is `trace s F ∅`, the family of
members of `F` that avoid `[s + 1]`; the paper's `∂F(S)` is Mathlib's shadow `∂ (trace s F S)`
(`Finset.shadow`, scoped notation in `FinsetFamily`), which for a uniform family is exactly the
paper's immediate shadow. -/
def trace (s : ℕ) (F : Finset (Finset ℕ)) (S : Finset ℕ) : Finset (Finset ℕ) :=
  (F.filter (fun A => A ∩ Finset.Icc 1 (s + 1) = S)).image (· \ S)

end FranklKupavskii2022.EMC


