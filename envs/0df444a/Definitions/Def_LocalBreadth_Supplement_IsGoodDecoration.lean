-- Prove2me | Definitions.Def_LocalBreadth_Supplement_IsGoodDecoration
-- name    : LocalBreadth_Supplement_IsGoodDecoration
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:23:12.326843+00:00
-- url     : https://prove2.me/theorems/ca8bfc51-fc15-4303-ba0f-819651309172
-- title:
--   Prefix-closed sets of histories and $q$-good geometric decorations
-- statement:
--   Let $\mathcal U\subseteq\mathcal H_K$ be an open neighborhood of $(K)$ closed under taking prefixes. A **geometric decoration** of $\mathcal U$ assigns to each history $H\in\mathcal U$ a cutoff $s_H\ge1$ and a radius $a_H\ge0$ such that $a_{H^\frown M}>a_H$ whenever $H^\frown M\in\mathcal U$. It is **$q$-good** if every $H=(K=L_0\supsetneq\dots\supsetneq L_r)\in\mathcal U$ is geometrically $q$-feasible at the cutoffs $s_{H_0},\dots,s_{H_r}$ of its prefixes $H_i=(L_0\supsetneq\dots\supsetneq L_i)$ outside $Q_{a_H}=[-a_H,a_H]^d\cap\mathbb Z^d$.
--
--   Decorated neighborhoods are the topological form of protected trees (Theorem 7.7).
--
--   **Formalization Note** Cutoffs and radii are functions of a history's chain; the prefix $H_i$ is the first $i+1$ languages. Openness, $\mathcal U\subseteq\mathcal H_K$ and $(K)\in\mathcal U$ are stated where decorations are used.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), Definition 7.6, p.58

import Mathlib
import Definitions.Def_LocalBreadth_Supplement_historyTopologyP
import Definitions.Def_LocalBreadth_Supplement_IsGeomFeasible

namespace LocalBreadth.Supplement

/-- `U` is closed under taking prefixes: with a history it contains all of its (nonempty) initial
segments `H_i = (L_0 ⊋ ⋯ ⊋ L_i)`. -/
def IsPrefixClosed {P : Type} {X : Set (Set P)} (U : Set (HistoryP P X)) : Prop :=
  ∀ H ∈ U, ∀ H' : HistoryP P X, H'.chain <+: H.chain → H' ∈ U

/-- A **q-good geometric decoration** of `U`. Kleinberg, Wei, STOC 2027 submission (manuscript sha256
f924cbfc…), Definition 7.6, p.58: to each history `H ∈ U` a cutoff `s_H ≥ 1` and a radius `a_H ≥ 0`,
with `a_{H⌢M} > a_H` whenever `H⌢M ∈ U`, such that every `H = (K = L_0 ⊋ ⋯ ⊋ L_r) ∈ U` is
geometrically `q`-feasible at the cutoffs `s_{H_0}, …, s_{H_r}` of its prefixes outside `Q_{a_H}`.

**Formalization Note.** The cutoff and radius are functions of the chain of a history (a history is
determined by its chain); the prefix `H_i` is `H.chain.take (i + 1)`. Only values on chains of
histories in `U` matter. Definition 7.6 is stated for open, prefix-closed neighborhoods `U ⊆ ℋ_K` of
`(K)`; those conditions are stated where the decoration is used (Theorem 7.7). -/
def IsGoodDecoration {d : ℕ} (h : ℕ → ℝ) (q : Set (Fin d → ℤ) → ℝ) {X : Set (Set (Fin d → ℤ))}
    (U : Set (HistoryP (Fin d → ℤ) X)) (s a : List (Set (Fin d → ℤ)) → ℝ) : Prop :=
  (∀ H ∈ U, 1 ≤ s H.chain ∧ 0 ≤ a H.chain) ∧
  (∀ H ∈ U, ∀ (M : Set (Fin d → ℤ)) (hM : M ∈ X) (hlt : M ⊂ H.last),
    H.snoc M hM hlt ∈ U → a H.chain < a (H.snoc M hM hlt).chain) ∧
  (∀ H ∈ U, IsGeomFeasible h (fun i => H.chain.getD i ∅) (fun i => q (H.chain.getD i ∅))
    (fun i => s (H.chain.take (i + 1))) (H.chain.length - 1) (a H.chain))

end LocalBreadth.Supplement


