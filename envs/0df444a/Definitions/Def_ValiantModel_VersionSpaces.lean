-- Prove2me | Definitions.Def_ValiantModel_VersionSpaces
-- name    : ValiantModel_VersionSpaces
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:04.100325+00:00
-- url     : https://prove2.me/theorems/a9c91b64-95e6-4aad-8395-8a1e7b2ce582
-- title:
--   Definition 8, p.16 — version spaces $V(S)$ and $V(q,r)$, and the closure of a version space
-- statement:
--   For a class $H_d$, the **positive-sample version space** of a finite set $S\subseteq\{0,1\}^d$ and the **query-transcript version space** of a query sequence $q$ with responses $r$ are
--
--   $$
--   V(S)=\{h\in H_d: S\subseteq\mathrm{supp}(h)\},\qquad V(q,r)=\{h\in H_d: h(q)=r\}.
--   $$
--
--   Both are subsets of $H_d$; in particular $V(q,r)$ is not restricted to any $V(S)$. For a strategy $\sigma$, $V(\sigma,r)=V(q(\sigma,r),r)$.
--
--   The **closure** of a set $V$ of hypotheses is the indicator of $\bigcap_{h\in V}\mathrm{supp}(h)$, the points every member of $V$ labels positive. For empty $V$ it is the all-one function, the empty intersection.
--
--   **Formalization Note** The equal-length sequences $q,r$ are one list of pairs.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.16 (PDF p.18), Definition 8 and display (2)

import Mathlib
import Definitions.Def_ValiantModel_ConceptSequence

namespace ValiantModel

/-- **Definition 8 (1)**, arXiv:2605.13840 (version held), p.16 (PDF p.18): the positive-sample
version space `V(S) = {h ∈ Hd : S ⊆ supp(h)}`. -/
def positiveVS {d : ℕ} (Hd : Set (Hypothesis d)) (S : Finset (Point d)) : Set (Hypothesis d) :=
  {h | h ∈ Hd ∧ ∀ x ∈ S, h x = true}

/-- **Definition 8 (2)**, ibid.: the query-transcript version space
`V(q, r) = {h ∈ Hd : h(q) = r}`, with the equal-length sequences `q, r` given as one list of pairs.
It is a subset of `Hd`, not of a positive-sample version space. -/
def transcriptVS {d : ℕ} (Hd : Set (Hypothesis d)) (T : List (Point d × Bool)) :
    Set (Hypothesis d) :=
  {h | h ∈ Hd ∧ ∀ t ∈ T, h t.1 = t.2}

/-- The indicator of the intersection `⋂_{h ∈ V} supp(h)`. For `V = ∅` this is the all-one function,
the empty intersection. -/
noncomputable def closureOf {d : ℕ} (V : Set (Hypothesis d)) : Hypothesis d :=
  open Classical in fun x => decide (∀ h ∈ V, h x = true)

end ValiantModel


