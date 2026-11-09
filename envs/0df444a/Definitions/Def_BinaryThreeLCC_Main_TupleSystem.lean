-- Prove2me | Definitions.Def_BinaryThreeLCC_Main_TupleSystem
-- name    : BinaryThreeLCC_Main_TupleSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:01:57.689022+00:00
-- url     : https://prove2.me/theorems/e094540e-a40f-422c-9547-6b3c42587bb9
-- title:
--   Flattening tuples, real and fake tuple copies, and transition matrices
-- statement:
--   A tuple system $\mathcal H$ contains $(u,\{a,b\},u')$ with two distinct labels and at most one tuple using each pair $(u,a)$. Its flattening has one labelled directed edge per tuple. Vector parity is a separate predicate. The constructed multiset $\mathcal T$ adds $(u,a,b,u')$, $(u,b,a,u')$, $(u,a,a,u)$ and $(u,b,b,u)$ for each tuple; an uncovered $(u,a)$ gets two copies of $(u,a,a,u)$. The list enumeration retains these multiplicities as separate identities. The transition graph and matrices are computed from these copies:
--
--   $$Q_{\mathcal T}(u',u)=|\{(u,\star,\star,u')\in\mathcal T\}|,\qquad
--   M_a(u',u)=\tfrac12|\{(u,a,\star,u')\in\mathcal T\}|.$$
--
--   The independent types $\Omega$ and $\Lambda$ need not coincide. Fake tuples and real copies remain distinguishable, and every transition object is a function of $\mathcal H$.
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Lemma 4.1, printed p.10, PDF p.12; construction of T, printed p.13, PDF p.15; Definition 5.4, printed p.14, PDF p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_CodeModel
import Definitions.Def_BinaryThreeLCC_Main_Graphs

set_option autoImplicit false

namespace BinaryThreeLCC.Main

open ContPatrol

/-- Unordered pairs of distinct labels, unique at each (source,label). -/
structure TupleSystem (Ω Λ : Type) where
  tuples : Finset (Ω × Finset Λ × Ω)
  pairs : ∀ t ∈ tuples, t.2.1.card = 2
  unique : ∀ t ∈ tuples, ∀ s ∈ tuples, t.1 = s.1 →
    ∀ a ∈ t.2.1, a ∈ s.2.1 → t = s

def tupleGraph {Ω Λ : Type} (H : TupleSystem Ω Λ) : Multigraph Ω H.tuples where
  src t := t.val.1
  tgt t := t.val.2.2

def TupleParity {Ω Λ : Type} {W : Type*} [AddCommGroup W] [Module Bit W]
    (H : TupleSystem Ω Λ) (v : Ω → W) (w : Λ → W) : Prop :=
  ∀ t ∈ H.tuples, v t.1 + (∑ a ∈ t.2.1, w a) + v t.2.2 = 0

abbrev OrderedTuple (Ω Λ : Type) := Ω × Λ × Λ × Ω

noncomputable def completions {Ω Λ : Type} (H : TupleSystem Ω Λ) (u : Ω) (a : Λ) :
    Finset (Λ × Ω) := by
  classical
  exact H.tuples.biUnion (fun t => if t.1 = u ∧ a ∈ t.2.1 then
    (t.2.1.erase a).image (fun b => (b, t.2.2)) else ∅)

/-- Exactly the real and fake tuple multiset of printed p.13; uncovered pairs get two copies. -/
noncomputable def transitionTuples {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    (H : TupleSystem Ω Λ) : Multiset (OrderedTuple Ω Λ) := by
  classical
  exact ∑ u : Ω, ∑ a : Λ,
    if (completions H u a).Nonempty then
      ∑ p ∈ completions H u a,
        (({(u, a, p.1, p.2)} : Multiset (OrderedTuple Ω Λ)) + {(u, a, a, u)})
    else Multiset.replicate 2 (u, a, a, u)

/-- The list is just an enumeration of copies, not a removal of repetitions. -/
noncomputable def transitionList {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    (H : TupleSystem Ω Λ) : List (OrderedTuple Ω Λ) := (transitionTuples H).toList

abbrev TupleCopy {Ω Λ : Type} [Fintype Ω] [Fintype Λ] (H : TupleSystem Ω Λ) :=
  Fin (transitionList H).length

noncomputable def tupleAt {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    (H : TupleSystem Ω Λ) (e : TupleCopy H) : OrderedTuple Ω Λ := (transitionList H).get e

noncomputable def transitionGraph {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    (H : TupleSystem Ω Λ) : Multigraph Ω (TupleCopy H) where
  src e := (tupleAt H e).1
  tgt e := (tupleAt H e).2.2.2

noncomputable def transitionQ {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    (H : TupleSystem Ω Λ) : Matrix Ω Ω ℝ := by
  classical
  exact fun v u => ((Finset.univ.filter (fun e : TupleCopy H =>
    (tupleAt H e).1 = u ∧ (tupleAt H e).2.2.2 = v)).card : ℝ)

noncomputable def transitionM {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    (H : TupleSystem Ω Λ) (a : Λ) : Matrix Ω Ω ℝ := by
  classical
  exact fun v u => ((Finset.univ.filter (fun e : TupleCopy H =>
    (tupleAt H e).1 = u ∧ (tupleAt H e).2.1 = a ∧
      (tupleAt H e).2.2.2 = v)).card : ℝ) / 2

end BinaryThreeLCC.Main


