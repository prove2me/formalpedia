-- Prove2me | Definitions.Def_RevisitXor_validSeqs
-- name    : RevisitXor_validSeqs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:05:03.811788+00:00
-- url     : https://prove2.me/theorems/fb48d5a4-3900-458d-a2d4-d08727c85ebd
-- title:
--   Random matching as an edge sequence $X_1,\dots,X_{M/2}$, and its weight $W$
-- statement:
--   Let $M=2^m$. A uniformly random perfect matching of the complete graph on $[2]^m$ is sampled by choosing its edges $X_1,X_2,\dots,X_{M/2}$ one at a time. The sample space is the set of **valid edge sequences**: sequences of $M/2$ edges $\{u,v\}$, $u\ne v$, no two of which share a vertex; it carries the uniform law. Every perfect matching has $(M/2)!$ orderings, so the matching it induces is uniform.
--
--   For $h$ as in the edge weights, the **weight** of a sequence is
--
--   $$W=w(X_1,\dots,X_{M/2})=w(X_1)+\cdots+w(X_{M/2}).$$
--
--   The average of a quantity $f$ over a finite set $s$ is $\operatorname{avg}_s f=|s|^{-1}\sum_{x\in s}f(x)$; expectations under the uniform law on valid sequences are such averages.
--
--   **Formalization Note** The module defines `avg`, the predicate `IsEdgeSeq`, the finite set `validSeqs m` of valid sequences `Fin (2^m/2) → Sym2 ([2]^m)`, and `W h xs`. For $m=0$ the only sequence is empty. `avg` of an empty set is $0$; it is applied only to nonempty sets in this mission.
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), §1, p.6, (2)

import Mathlib
import Definitions.Def_RevisitXor_wEdge

namespace RevisitXor

/-- The uniform average of `f` over a finite set `s` (`0` on the empty set). -/
noncomputable def avg {β : Type*} (s : Finset β) (f : β → ℝ) : ℝ :=
  (s.card : ℝ)⁻¹ * ∑ x ∈ s, f x

/-- A sequence `X₁, …, X_{M/2}` (`M = 2^m`, indexed `0, …, M/2 - 1`) of edges of the complete graph
on `[2]^m` is **valid** when no edge is a loop and distinct edges share no vertex. Such a sequence
lists the edges of a perfect matching in some order. -/
def IsEdgeSeq {m : ℕ} (xs : Fin (2 ^ m / 2) → Sym2 (Cube m)) : Prop :=
  (∀ i, ¬ (xs i).IsDiag) ∧ ∀ i j, i ≠ j → ∀ v, v ∈ xs i → v ∉ xs j

open Classical in
/-- **The edge sequences `X₁, …, X_{M/2}`.** Viola, *Revisiting the XOR lemma*, STOC 2027
submission (manuscript of August 25, 2026, sha256 3b49e10d…716), §1, p.6: "We sample the permutation
π by selecting the edges X1, X2, . . . , XM/2 in the corresponding matching."

**Formalization Note.** The sample space is the finite set of valid edge sequences
(`IsEdgeSeq`), with the uniform law: averages and probabilities over it are `avg` and card ratios.
Every perfect matching has `(M/2)!` orderings, so the induced matching is uniform. For `m = 0`
there is exactly one (empty) sequence. -/
noncomputable def validSeqs (m : ℕ) : Finset (Fin (2 ^ m / 2) → Sym2 (Cube m)) :=
  Finset.univ.filter IsEdgeSeq

/-- **The weight `W`.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of
August 25, 2026, sha256 3b49e10d…716), §1, p.6: "For edges x1, x2, . . . , xi we also write
w(x1, x2, . . . , xi) for w(x1) + w(x2) + · · · + w(xi)", and (2): "w(X1, X2, . . . , XM/2) =: W". -/
noncomputable def W {m : ℕ} (h : Cube m × Cube m → ZMod 2)
    (xs : Fin (2 ^ m / 2) → Sym2 (Cube m)) : ℝ :=
  ∑ i, wEdge h (xs i)

end RevisitXor


