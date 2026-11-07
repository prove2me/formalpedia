-- Prove2me | Definitions.Def_PlantedSubgraphLD_AbsGraph
-- name    : PlantedSubgraphLD_AbsGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:35.820017+00:00
-- url     : https://prove2.me/theorems/687b177e-851b-4444-99ff-c7565517e0af
-- title:
--   Abstract subgraphs of $\Gamma$, $e(F)$, $v(F)$, $N_\Gamma(F)$, $|\mathrm{Aut}(F)|$
-- statement:
--   Let $\Gamma$ be a finite simple graph. A subgraph of $\Gamma$ is specified by a set $S\subseteq E(\Gamma)$ of edges together with their incident vertices; it has no isolated vertices. An **abstract graph** is an isomorphism class of finite simple graphs without isolated vertices. This definition provides:
--
--   1. the nonempty abstract graphs $F$ with $N_\Gamma(F)>0$, as the isomorphism classes of the graphs spanned by nonempty edge sets $S\subseteq E(\Gamma)$;
--   2. $e(F)=|E(F)|$ and $v(F)=|V(F)|$;
--   3. the copies $C_\Gamma(F)=\{F^\circ\subseteq\Gamma:\ F^\circ\simeq F\}$ and their number $N_\Gamma(F)=|C_\Gamma(F)|$, the number of not-necessarily-induced subgraphs of $\Gamma$ isomorphic to $F$;
--   4. $|\mathrm{Aut}(F)|$, the number of automorphisms of $F$;
--   5. connectedness of $F$.
--
--   Every sum of the paper of the form $\sum_{F:\,N_{\Gamma_n}(F)>0}$ runs over this finite set.
--
--   **Formalization Note** `AbsGraph Γ` is the quotient of the nonempty edge subsets of $\Gamma$ by isomorphism of the spanned graphs (`spanned S`, on the vertex set `edgeSupp S` of endpoints). Its elements are exactly the nonempty abstract graphs with $N_\Gamma(F)>0$. The invariants $e$, $v$, $|\mathrm{Aut}|$ and connectedness are read off the representative `Quotient.out F`; they are isomorphism invariants, so the choice does not matter.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.1, pp.11–12 (PDF pp.13–14); §4.1, p.17 (PDF p.19, C_Γn(F))

import Mathlib

open Classical

namespace PlantedSubgraphLD

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The vertices incident to a set `S` of edges. -/
noncomputable def edgeSupp (S : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter (fun v => ∃ e ∈ S, v ∈ e)

/-- The graph specified by an edge set `S` "together with its incident vertices": vertex set
`edgeSupp S`, edge set `S`. It has no isolated vertices. -/
noncomputable def spanned (S : Finset (Sym2 V)) : SimpleGraph (edgeSupp S : Set V) :=
  (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).induce (edgeSupp S : Set V)

/-- Nonempty edge subsets of `Γ`, i.e. the nonempty (not necessarily induced) subgraphs of `Γ`
specified by their edge sets. -/
def EdgeSub (Γ : SimpleGraph V) : Type :=
  {S : Finset (Sym2 V) // S.Nonempty ∧ S ⊆ Γ.edgeFinset}

noncomputable instance (Γ : SimpleGraph V) : Fintype (EdgeSub Γ) := by
  unfold EdgeSub; infer_instance

/-- Two edge subsets are equivalent when the graphs they span are isomorphic. -/
def isoSetoid (Γ : SimpleGraph V) : Setoid (EdgeSub Γ) where
  r S T := Nonempty (spanned S.1 ≃g spanned T.1)
  iseqv :=
    ⟨fun _ => ⟨SimpleGraph.Iso.refl⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- The abstract graphs `F` with `N_Γ(F) > 0`: isomorphism classes of nonempty subgraphs of `Γ`
(each specified by an edge set together with its incident vertices).

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.1, pp.11–12: "an abstract graph is an
isomorphism class of finite simple graphs without isolated vertices. […] For an abstract graph F,
let NΓ(F) be the number of not-necessarily-induced subgraphs of Γ isomorphic to F, where a
subgraph is specified by its edge set together with its incident vertices, and let Aut(F) denote
the automorphism group of F."

**Formalization Note** `AbsGraph Γ` is the quotient of the nonempty edge subsets of `Γ` by
isomorphism of the spanned graphs. Its elements are exactly the nonempty abstract graphs `F`
with `N_Γ(F) > 0`, which is the index set of every sum of the paper ("sum over F with
NΓn(F) > 0"). The numerical invariants `e(F)`, `v(F)`, `|Aut(F)|` and connectedness are read off
the representative `Quotient.out F`; they are isomorphism invariants, so the choice does not
matter. -/
def AbsGraph (Γ : SimpleGraph V) : Type := Quotient (isoSetoid Γ)

noncomputable instance (Γ : SimpleGraph V) : Fintype (AbsGraph Γ) := by
  unfold AbsGraph; infer_instance

variable {Γ : SimpleGraph V}

/-- `e(F)`, the number of edges of the abstract graph `F`. -/
noncomputable def numEdges (F : AbsGraph Γ) : ℕ := (Quotient.out F : EdgeSub Γ).1.card

/-- `v(F)`, the number of vertices of the abstract graph `F` (it has no isolated vertices). -/
noncomputable def numVerts (F : AbsGraph Γ) : ℕ := (edgeSupp (Quotient.out F : EdgeSub Γ).1).card

/-- `C_Γ(F)`, the concrete copies of `F` in `Γ` (as edge sets). -/
noncomputable def copies (F : AbsGraph Γ) : Finset (EdgeSub Γ) :=
  Finset.univ.filter (fun S => (Quotient.mk (isoSetoid Γ) S : AbsGraph Γ) = F)

/-- `N_Γ(F) = |C_Γ(F)|`, the number of subgraphs of `Γ` isomorphic to `F`. -/
noncomputable def count (F : AbsGraph Γ) : ℕ := (copies F).card

/-- `|Aut(F)|`, the number of automorphisms of (a representative of) `F`. -/
noncomputable def autCard (F : AbsGraph Γ) : ℕ :=
  Nat.card (spanned (Quotient.out F : EdgeSub Γ).1 ≃g spanned (Quotient.out F : EdgeSub Γ).1)

/-- `F` is connected. -/
def IsConn (F : AbsGraph Γ) : Prop := (spanned (Quotient.out F : EdgeSub Γ).1).Connected

end PlantedSubgraphLD


