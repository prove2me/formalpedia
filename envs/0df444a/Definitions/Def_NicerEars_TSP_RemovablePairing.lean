-- Prove2me | Definitions.Def_NicerEars_TSP_RemovablePairing
-- name    : NicerEars_TSP_RemovablePairing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:51.970552+00:00
-- url     : https://prove2.me/theorems/848146ff-0348-4d07-822b-c035ee92ba91
-- title:
--   Definition 26, p. 20 — removable pairings (Mömke and Svensson)
-- statement:
--   **Definition 26** (Definition 3.1 of Mömke and Svensson [2011]). Let $G$ be a connected graph. A *removable pairing* of $G$ is a pair $(R,\mathcal P)$ of sets such that
--
--   1. $R\subseteq E(G)$;
--   2. for each $P\in\mathcal P$ there are three distinct edges $e,e',e''\in E(G)$ and a vertex $v\in V(G)$ with $e,e',e''\in\delta(v)$ and $P=\{e,e'\}\subseteq R$;
--   3. any two distinct pairs $P,P'\in\mathcal P$ are disjoint;
--   4. if $S\subseteq R$ and $|S\cap P|\le 1$ for all $P\in\mathcal P$, then $(V(G),E(G)\setminus S)$ is connected.
--
--   The elements of $\mathcal P$ are called pairs. A removable pairing marks edges that a tour may drop: any set of edges of $R$ that takes at most one edge from each pair can be deleted without disconnecting $G$. This is the device behind the Mömke–Svensson bound of Theorem 27.
--
--   **Formalization Note.** The family $\mathcal P$ is a finite set of edge sets, named `Pairs` in Lean. Since graphs have no loops, $e\in\delta(v)$ is the statement that $v$ is an endpoint of $e$. The connectivity of $G$ presupposed by the definition is a hypothesis of the theorems that use it.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 20, Definition 26 (Definition 3.1 of Mömke and Svensson [2011])

import Mathlib
import Definitions.Def_NicerEars_TSP_Setting

namespace NicerEars.TSP

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Definition 26, p. 20 (Definition 3.1 of Mömke and Svensson [2011]): (R, 𝒫) is a removable
pairing of G:
* R ⊆ E(G);
* every P ∈ 𝒫 is P = {e, e′} ⊆ R for three distinct edges e, e′, e″ ∈ δ(v) at some vertex v;
* distinct pairs are disjoint;
* if S ⊆ R and |S ∩ P| ≤ 1 for all P ∈ 𝒫, then (V(G), E(G) \ S) is connected.

In Lean the family 𝒫 of pairs is named `Pairs`. -/
def Graph.IsRemovablePairing (G : Graph V E) (R : Finset E) (Pairs : Finset (Finset E)) : Prop :=
  (∀ P ∈ Pairs, ∃ e e' e'' : E, ∃ v : V, e ≠ e' ∧ e ≠ e'' ∧ e' ≠ e'' ∧
      v ∈ G.ends e ∧ v ∈ G.ends e' ∧ v ∈ G.ends e'' ∧ P = {e, e'} ∧ P ⊆ R) ∧
  (∀ P ∈ Pairs, ∀ P' ∈ Pairs, P ≠ P' → Disjoint P P') ∧
  (∀ S ⊆ R, (∀ P ∈ Pairs, #(S ∩ P) ≤ 1) → (G.spanGraph (univ \ S)).Connected)

end NicerEars.TSP


