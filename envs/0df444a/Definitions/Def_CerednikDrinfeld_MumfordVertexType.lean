-- Prove2me | Definitions.Def_CerednikDrinfeld_MumfordVertexType
-- name    : CerednikDrinfeld_MumfordVertexType
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/36bc3908-9432-5f85-998d-0c65892e0b77
-- title:
--   Vertex type parity and the type-preserving subgroup
-- statement:
--   Throughout, $W$ is a type and $\mathcal T$ a simple graph on $W$ with a distinguished vertex $w_0$. The first definition, `vertexType 𝒯 w₀ w`, is the residue in $\mathbb Z/2$ of the graph distance $d_{\mathcal T}(w_0,w)$, using Mathlib's `SimpleGraph.dist`; since that distance is a total function taking the value $0$ on pairs lying in different connected components, the type is a total function on $W$ as well, and vertices not joined to $w_0$ by a path receive type $0$. Two elementary facts accompany it: the defining equation, and the statement that $w_0$ itself has type $0$. When $\mathcal T$ is connected and has no odd cycle — in particular when $\mathcal T$ is a tree — this function is exactly the two-colouring given by the bipartition, normalised so that $w_0$ is coloured $0$.
--
--   The second definition takes in addition a group $G$ acting on $W$ (by `MulAction`, with no compatibility with the edge relation demanded in the definition) and produces the subgroup `typePreserving G 𝒯 w₀` of $G$ whose underlying set consists of those $g$ with $\mathrm{vertexType}_{\mathcal T,w_0}(g\cdot w)=\mathrm{vertexType}_{\mathcal T,w_0}(w)$ for every $w\in W$; closure under $1$, products and inverses is part of the data of the subgroup. A membership criterion records that belonging to this subgroup is precisely this universally quantified condition. For a group acting by graph automorphisms on a tree, this is the subgroup of elements preserving the bipartition, of index at most $2$ in the image of the action.
--
--   **Relation to Mathlib.** Mathlib supplies the graph distance `SimpleGraph.dist` and the subgroup API used here; the parity-valued vertex type and the associated type-preserving subgroup are the project's own definitions.
--
--   **Where it is used.** These notions provide the combinatorial language for the Čerednik–Drinfeld description of the special fibre of a Shimura curve: the intended instance is the Bruhat–Tits tree of $\mathrm{PGL}_2(\mathbb Q_r)$, on which the type of a vertex is the parity of the valuation of the reduced norm, and the type-preserving subgroup of a quaternionic unit group is the one whose quotient graph is the dual graph of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_MumfordVertexType.lean

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.ZMod.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld.Mumford

variable {W : Type}

def vertexType (𝒯 : SimpleGraph W) (w₀ w : W) : ZMod 2 := (𝒯.dist w₀ w : ZMod 2)

theorem vertexType_apply (𝒯 : SimpleGraph W) (w₀ w : W) : vertexType 𝒯 w₀ w = (𝒯.dist w₀ w : ZMod 2) := rfl

@[simp] theorem vertexType_self (𝒯 : SimpleGraph W) (w₀ : W) : vertexType 𝒯 w₀ w₀ = 0 := by
  rw [vertexType, SimpleGraph.dist_self, Nat.cast_zero]

def typePreserving (G : Type) [Group G] [MulAction G W] (𝒯 : SimpleGraph W) (w₀ : W) : Subgroup G where
  carrier := {g | ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w}
  one_mem' := fun w => by rw [one_smul]
  mul_mem' {g h} hg hh := fun w => by rw [mul_smul, hg, hh]
  inv_mem' {g} hg := fun w => by rw [← hg (g⁻¹ • w), smul_inv_smul]

@[simp] theorem mem_typePreserving_iff {G : Type} [Group G] [MulAction G W] (𝒯 : SimpleGraph W) (w₀ : W) (g : G) :
    g ∈ typePreserving G 𝒯 w₀ ↔ ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w := Iff.rfl

end CerednikDrinfeld.Mumford

end


