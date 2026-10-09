-- Prove2me | Definitions.Def_NicerEars_TwoEC_OneSum
-- name    : NicerEars_TwoEC_OneSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:59.103599+00:00
-- url     : https://prove2.me/theorems/3417c8ff-d427-4e61-a73a-66a5632ab307
-- title:
--   Proposition 4, p. 5 — two graphs glued at one vertex, and the even set among (T ∩ V(Gᵢ)) \ {v} and (T ∩ V(Gᵢ)) ∪ {v}
-- statement:
--   Let $G_1$ and $G_2$ be graphs and $v_1\in V(G_1)$, $v_2\in V(G_2)$. The **one-vertex sum** $G$ identifies $v_1$ with $v_2$ into one vertex $v$: its vertex set is $V(G_1)\cup V(G_2)$ with $V(G_1)\cap V(G_2)=\{v\}$, and its edge set is the disjoint union $E(G_1)\cup E(G_2)$, each edge keeping its ends. This is the graph $G:=(V(G_1)\cup V(G_2),E(G_1)\cup E(G_2))$ of Proposition 4.
--
--   For a vertex set $T$ of $G$, $T\cap V(G_i)$ is read as a vertex set of $G_i$ (it contains $v_i$ exactly when $v\in T$), and for $S\subseteq V(G_i)$ the **even set among** $S\setminus\{v_i\}$ and $S\cup\{v_i\}$ is the one of the two with even cardinality; exactly one of them is even because they differ in the single vertex $v_i$.
--
--   This is the block decomposition by which all three problems of the paper reduce to 2-vertex-connected graphs.
--
--   **Formalization Note** The vertex type of $G$ is $V_1\oplus(V_2\setminus\{v_2\})$ and its edge type $E_1\oplus E_2$; the map from $V_2$ sends $v_2$ to $v_1$ and is injective, which keeps $G$ loopless. Any graph with a cut vertex $v$ splitting it into $G_1$ and $G_2$ is isomorphic to such a sum.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 5, Proposition 4

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Setting

namespace NicerEars.TwoEC

open Finset

variable {V₁ V₂ E₁ E₂ : Type} [DecidableEq V₂]

/-- The vertex map V(G₂) → V(G) of the one-vertex sum (Proposition 4, p. 5): the vertex `v₂` of G₂
is identified with the vertex `v₁` of G₁, and every other vertex of G₂ is kept. The vertex set of
G is V₁ ⊕ (V₂ ∖ {v₂}). -/
def glueRight (v₁ : V₁) (v₂ : V₂) (w : V₂) : V₁ ⊕ {w : V₂ // w ≠ v₂} :=
  if h : w = v₂ then Sum.inl v₁ else Sum.inr ⟨w, h⟩

theorem glueRight_injective (v₁ : V₁) (v₂ : V₂) : Function.Injective (glueRight v₁ v₂) := by
  intro a b h
  unfold glueRight at h
  by_cases ha : a = v₂ <;> by_cases hb : b = v₂ <;> simp_all

/-- Proposition 4 (p. 5): G := (V(G₁) ∪ V(G₂), E(G₁) ∪ E(G₂)) for two graphs G₁ and G₂ whose vertex
sets meet exactly in one vertex v, here written as the vertex `v₁` of G₁ glued to the vertex `v₂`
of G₂. Its edge set is the disjoint union E(G₁) ⊕ E(G₂). -/
def oneSum (G₁ : Graph V₁ E₁) (G₂ : Graph V₂ E₂) (v₁ : V₁) (v₂ : V₂) :
    Graph (V₁ ⊕ {w : V₂ // w ≠ v₂}) (E₁ ⊕ E₂) where
  ends := Sum.elim (fun e => Sym2.map Sum.inl (G₁.ends e))
    (fun e => Sym2.map (glueRight v₁ v₂) (G₂.ends e))
  loopless := by
    rintro (e | e)
    · simpa [Sym2.isDiag_map Sum.inl_injective] using G₁.loopless e
    · simpa [Sym2.isDiag_map (glueRight_injective v₁ v₂)] using G₂.loopless e

variable [DecidableEq V₁]

/-- Proposition 4 (p. 5): "the even set among S \ {v} and S ∪ {v}". The two sets differ exactly in
`v`, so exactly one of them has even cardinality. -/
def evenAmong {W : Type} [DecidableEq W] (v : W) (S : Finset W) : Finset W :=
  if Even #(S.erase v) then S.erase v else insert v S

variable [Fintype V₁] [Fintype V₂]

/-- T ∩ V(G₁), as a vertex set of G₁. -/
def restrictLeft (v₂ : V₂) (T : Finset (V₁ ⊕ {w : V₂ // w ≠ v₂})) : Finset V₁ :=
  univ.filter (fun a => Sum.inl a ∈ T)

/-- T ∩ V(G₂), as a vertex set of G₂ (the glued vertex v₂ belongs to it iff v₁ ∈ T). -/
def restrictRight (v₁ : V₁) (v₂ : V₂) (T : Finset (V₁ ⊕ {w : V₂ // w ≠ v₂})) : Finset V₂ :=
  univ.filter (fun w => glueRight v₁ v₂ w ∈ T)

end NicerEars.TwoEC


