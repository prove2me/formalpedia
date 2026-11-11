-- Prove2me | Definitions.Def_InducedMinorDeletion1657_Main_Logic
-- name    : InducedMinorDeletion1657_Main_Logic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:32:08.701048+00:00
-- url     : https://prove2.me/theorems/0cc4423b-bc2f-444b-a3e4-15d867d31e5c
-- title:
--   MSO deletion, boundaried extensions and complete tables
-- statement:
--   A sentence is a closed, constant-free incidence MSO2 formula, with one trivial vertex color. It has individual vertex and edge quantifiers and quantifiers over their subsets, with the published satisfaction relation. No hereditary or satisfiability condition is imposed.
--
--   A finite $\ell$-boundaried graph has an injective map from $\mathrm{Fin}(\ell)$ to its vertices. Gluing takes disjoint internal copies and identifies equally labelled boundary vertices, retaining the union of the edge sets. Its $\varphi$-type records truth after every finite extension:
--   $$F\sim_\varphi F'\iff\forall K,\ (F\oplus K\models\varphi\iff F'\oplus K\models\varphi).$$
--   At empty boundary this tests every disjoint-union extension. Repeated boundary edges are permitted and become one edge. No treewidth restriction is imposed on $K$.
--
--   A deletion is feasible exactly when its residual graph has treewidth at most $t$ and satisfies $\varphi$. Optimality compares with every feasible deletion. The optimum is option-valued, with `none` exactly for infeasibility. A table contains feasible witnesses and, for every feasible $R$, a witness $S$ of no greater cardinality with the same extension type. This is the full two-clause table used in Section 5.
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), Section 1, p. 2 (PDF p. 3); Section 5, pp. 24–25 (PDF pp. 25–26)

import Definitions.Def_InducedMinorDeletion1657_Main_Graphs
import Definitions.Def_TwMSOCount_Main_MSO2

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

abbrev Sentence := {φ : TwMSOCount.Main.Formula 1 Empty // φ.IsSentence}

def models {V : Type} (G : SimpleGraph V) (φ : Sentence) : Prop :=
  TwMSOCount.Main.Formula.Models G (fun _ => 0) (fun e => nomatch e) φ.val

/-- All finite l-boundaried graphs, with no bound on treewidth. -/
structure BoundaryGraph (l : ℕ) where
  V : Type
  [fin : Fintype V]
  [dec : DecidableEq V]
  graph : SimpleGraph V
  boundary : Fin l → V
  inj : Function.Injective boundary

attribute [instance] BoundaryGraph.fin BoundaryGraph.dec

abbrev Internal {l : ℕ} (F : BoundaryGraph l) := {v : F.V // v ∉ Set.range F.boundary}
abbrev GlueVertex {l : ℕ} (F K : BoundaryGraph l) := Fin l ⊕ (Internal F ⊕ Internal K)

noncomputable def toGlueLeft {l : ℕ} (F K : BoundaryGraph l) (v : F.V) : GlueVertex F K :=
  if h : ∃ i, F.boundary i = v then .inl (Classical.choose h)
  else .inr (.inl ⟨v, h⟩)

noncomputable def toGlueRight {l : ℕ} (F K : BoundaryGraph l) (v : K.V) : GlueVertex F K :=
  if h : ∃ i, K.boundary i = v then .inl (Classical.choose h)
  else .inr (.inr ⟨v, h⟩)

/-- Gluing identifies equal labels, keeps both sets of fresh internal vertices,
    and takes the union of edges (duplicate boundary edges are permitted). -/
noncomputable def glue {l : ℕ} (F K : BoundaryGraph l) : SimpleGraph (GlueVertex F K) :=
  SimpleGraph.fromRel fun x y =>
    (∃ u v, F.graph.Adj u v ∧ toGlueLeft F K u = x ∧ toGlueLeft F K v = y) ∨
    (∃ u v, K.graph.Adj u v ∧ toGlueRight F K u = x ∧ toGlueRight F K v = y)

def unbound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : BoundaryGraph 0 :=
  ⟨V, G, Fin.elim0, by intro x; exact Fin.elim0 x⟩

/-- Section 5's φ-type: agreement under ALL finite extensions. -/
def sameType {l : ℕ} (φ : Sentence) (F F' : BoundaryGraph l) : Prop :=
  ∀ K : BoundaryGraph l, models (glue F K) φ ↔ models (glue F' K) φ

def feasible {V : Type} [DecidableEq V] (G : SimpleGraph V) (t : ℕ)
    (φ : Sentence) (S : Finset V) : Prop :=
  modulator G t S ∧ models (residual G S) φ

def optimal {V : Type} [DecidableEq V] (G : SimpleGraph V) (t : ℕ)
    (φ : Sentence) (S : Finset V) : Prop :=
  feasible G t φ S ∧ ∀ R, feasible G t φ R → S.card ≤ R.card

/-- Explicit infeasibility; no value is assigned to an empty feasible family. -/
def infeasible {V : Type} [DecidableEq V] (G : SimpleGraph V) (t : ℕ) (φ : Sentence) : Prop :=
  ¬ ∃ S, feasible G t φ S

noncomputable def optimum {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) (φ : Sentence) : Option ℕ :=
  if ∃ S, feasible G t φ S then
    some (sInf {k : ℕ | ∃ S, feasible G t φ S ∧ S.card = k})
  else none

/-- Both table clauses, including cost coverage and extension type. -/
def deletionTable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) (φ : Sentence) (T : List (Finset V)) : Prop :=
  (∀ S ∈ T, feasible G t φ S) ∧
  ∀ R, feasible G t φ R → ∃ S ∈ T, S.card ≤ R.card ∧
    sameType φ (unbound (residual G S)) (unbound (residual G R))

end InducedMinorDeletion1657.Main


