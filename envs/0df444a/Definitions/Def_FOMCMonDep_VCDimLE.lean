-- Prove2me | Definitions.Def_FOMCMonDep_VCDimLE
-- name    : FOMCMonDep_VCDimLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:23.405194+00:00
-- url     : https://prove2.me/theorems/c3e9ae03-a5fe-4563-b26e-d8019a15ab9c
-- title:
--   VC-dimension of a graph at most $d$
-- statement:
--   The **VC-dimension** of a graph $G$ is the maximal size of a set $A\subseteq V(G)$ that is shattered by the neighbourhoods, i.e. $\{N(v)\cap A: v\in V(G)\}=2^A$. A graph has VC-dimension at most $d$ if every shattered set has at most $d$ elements.
--
--   Monadically dependent classes have bounded VC-dimension, and Lemma 5.7 is stated for graphs of bounded VC-dimension.
--
--   **Formalization Note** The vertex type is arbitrary. Only finite shattered sets are considered; this loses nothing, since every subset of a shattered set is shattered.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §3, p.11 (PDF 13)

import Mathlib

set_option autoImplicit false

namespace FOMCMonDep

/-- **VC-dimension at most `d`.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §3, p.11 (PDF 13): "The VC-dimension of a graph G is
the maximal size of a set A ⊆ V(G) such that {N(v) ∩ A : v ∈ V(G)} = 2^A."

**Formalization Note.** "VC-dimension at most d": every finite shattered set has at most `d` elements. The vertex type
is arbitrary (Lemma 5.7 is in Part I). Restricting to finite `A` loses nothing: every subset of a shattered set is
shattered, so an infinite shattered set has shattered subsets of every finite size. -/
def VCDimLE {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ A : Finset V, (∀ B ⊆ A, ∃ v : V, ∀ a ∈ A, (G.Adj v a ↔ a ∈ B)) → A.card ≤ d

end FOMCMonDep


