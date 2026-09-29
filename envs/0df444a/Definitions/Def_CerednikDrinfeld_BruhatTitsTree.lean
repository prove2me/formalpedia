-- Prove2me | Definitions.Def_CerednikDrinfeld_BruhatTitsTree
-- name    : CerednikDrinfeld_BruhatTitsTree
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/e750c71c-6da7-54f2-9bab-bc41fe312cf1
-- title:
--   Bruhat–Tits tree of GL2​ as a graph with action
-- statement:
--   Throughout, $R$ is a commutative ring and $K$ a field that is an $R$-algebra; for the graph-theoretic part $K$ is moreover the fraction field of $R$. The type `Vertex R K` of homothety classes of full $R$-lattices in $K^2$, the direct-image operation `latticeMap g` on submodules, the predicate `IsFullLattice`, the scalar matrices `scalarGL` and the adjacency predicate `AdjacentLattice` on lattices are taken from the imported lattice-tree development; this module supplies the action and graph packaging. First, `Vertex.act` is registered as an action of $\mathrm{GL}_2(K)$ on `Vertex R K`, so that $g \cdot [L] = [gL]$ for a full lattice $L$, and `vertPermHom R K` is the resulting homomorphism to the permutation group of `Vertex R K`. Mathlib's scalar matrix `Matrix.GeneralLinearGroup.scalar (Fin 2) c` is identified with `scalarGL c` for $c \in K^\times$; such a matrix fixes every vertex, hence lies in the kernel of `vertPermHom R K`, and the action therefore descends to an action of `Matrix.ProjGenLinGroup (Fin 2) K`, i.e. of $\mathrm{PGL}_2(K)$, with $[g] \cdot v = g \cdot v$.
--
--   Second, `VertRel R K x y` asserts the existence of full lattices $L, L'$ representing $x$ and $y$ respectively with `AdjacentLattice L L'`; the latter, as used here, provides an element $\varpi$ of $R$ together with two strict inclusions of submodules, one of them after multiplication by the scalar matrix $\varpi$. The Bruhat–Tits graph `tree R K` is then `SimpleGraph.fromRel (VertRel R K)`: vertices $x$ and $y$ are adjacent exactly when $x \neq y$ and `VertRel R K` holds in one of the two orders. Direct image along an invertible matrix preserves `AdjacentLattice`, hence `VertRel R K`, hence adjacency in `tree R K`; thus $\mathrm{GL}_2(K)$ and $\mathrm{PGL}_2(K)$ act on `tree R K` as instances of the project's `GraphAction` class (adjacency-preserving actions). Two further lemmas transport a `GraphAction` to a subgroup of the acting group and, along a group homomorphism $\varphi : G' \to G$, to the action of $G'$ obtained by composition with $\varphi$.
--
--   **Relation to Mathlib.** Mathlib has no Bruhat–Tits tree and no class for an adjacency-preserving group action on a `SimpleGraph`; the graph is built from Mathlib's `SimpleGraph.fromRel` and the quotient group is Mathlib's `Matrix.ProjGenLinGroup`, and one lemma identifies Mathlib's `Matrix.GeneralLinearGroup.scalar` with the project's `scalarGL`.
--
--   **Where it is used.** With these instances the project's machinery for quotients of a graph by a group action — orbits of darts over orbits of vertices, with stabiliser widths, as packaged in `quotientDegeneracyData` — applies to `tree R K`, which is the combinatorial input to the Čerednik–Drinfeld/Mumford description of Shimura curves and their reduction used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_BruhatTitsTree.lean

import Definitions.Def_LatticeTreeOrbital
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
noncomputable section

open scoped MatrixGroups

namespace CerednikDrinfeld
namespace BruhatTits

open Mumford LT.LatticeTree

namespace _root_.CerednikDrinfeld.Mumford

variable {G : Type} [Group G] {W : Type} [MulAction G W] {𝒯 : SimpleGraph W}

instance GraphAction.subgroup (H : Subgroup G) [GraphAction G 𝒯] : GraphAction H 𝒯 :=
  ⟨fun h _ _ hadj => GraphAction.smul_adj (h : G) hadj⟩

theorem GraphAction.of_compHom {G' : Type} [Group G'] (φ : G' →* G) [GraphAction G 𝒯] :
    @GraphAction G' _ W (MulAction.compHom W φ) 𝒯 :=
  @GraphAction.mk G' _ W (MulAction.compHom W φ) 𝒯 fun g _ _ hadj => GraphAction.smul_adj (φ g) hadj

end _root_.CerednikDrinfeld.Mumford

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

instance instMulActionGLVertex : MulAction (GL (Fin 2) K) (Vertex R K) where
  smul := Vertex.act
  one_smul := Vertex.act_one
  mul_smul := Vertex.act_mul

theorem gl_smul_def (g : GL (Fin 2) K) (v : Vertex R K) : g • v = Vertex.act g v := rfl

@[simp] theorem gl_smul_mk (g : GL (Fin 2) K) (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    g • Vertex.mk R K L hL = Vertex.mk R K (latticeMap g L) (hL.map g) := rfl

variable (R K) in

def vertPermHom : GL (Fin 2) K →* Equiv.Perm (Vertex R K) := MulAction.toPermHom (GL (Fin 2) K) (Vertex R K)

@[simp] theorem vertPermHom_apply (g : GL (Fin 2) K) (x : Vertex R K) : vertPermHom R K g x = g • x := rfl

theorem scalar_eq_scalarGL (c : Kˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) c = scalarGL c := by
  ext i j
  simp [Matrix.GeneralLinearGroup.coe_scalar, scalarGL_coe, Matrix.one_apply, Matrix.diagonal_apply]

theorem scalar_smul_vertex (c : Kˣ) (v : Vertex R K) : Matrix.GeneralLinearGroup.scalar (Fin 2) c • v = v := by
  rw [scalar_eq_scalarGL]
  exact isFixedVertex_scalarGL c v

theorem scalar_mem_ker_vertPermHom (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ (vertPermHom R K).ker := by
  rw [MonoidHom.mem_ker]
  ext x
  simp [scalar_smul_vertex]

instance instMulActionPGLVertex : MulAction (Matrix.ProjGenLinGroup (Fin 2) K) (Vertex R K) :=
  Matrix.ProjGenLinGroup.mulActionOfGL fun c v => scalar_smul_vertex c v

@[simp] theorem pgl_mk_smul (g : GL (Fin 2) K) (v : Vertex R K) : Matrix.ProjGenLinGroup.mk g • v = g • v := rfl

variable [IsFractionRing R K]

theorem adjacentLattice_latticeMap (g : GL (Fin 2) K) {L L' : Submodule R (Fin 2 → K)}
    (h : AdjacentLattice L L') : AdjacentLattice (latticeMap g L) (latticeMap g L') := by
  obtain ⟨ϖ, hϖ, h₁, h₂⟩ := h
  refine ⟨ϖ, hϖ, ?_, (latticeMap_lt_latticeMap_iff g).2 h₂⟩
  rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]
  exact (latticeMap_lt_latticeMap_iff g).2 h₁

variable (R K) in

def VertRel (x y : Vertex R K) : Prop :=
  ∃ (L L' : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) (hL' : IsFullLattice L'),
    Vertex.mk R K L hL = x ∧ Vertex.mk R K L' hL' = y ∧ AdjacentLattice L L'

variable (R K) in

def tree : SimpleGraph (Vertex R K) := SimpleGraph.fromRel (VertRel R K)

theorem tree_adj_iff (x y : Vertex R K) :
    (tree R K).Adj x y ↔ x ≠ y ∧ (VertRel R K x y ∨ VertRel R K y x) :=
  SimpleGraph.fromRel_adj _ _ _

theorem VertRel.gl_smul (g : GL (Fin 2) K) {x y : Vertex R K} (h : VertRel R K x y) :
    VertRel R K (g • x) (g • y) := by
  obtain ⟨L, L', hL, hL', rfl, rfl, hLL'⟩ := h
  exact ⟨latticeMap g L, latticeMap g L', hL.map g, hL'.map g, rfl, rfl, adjacentLattice_latticeMap g hLL'⟩

instance instGraphActionGLTree : GraphAction (GL (Fin 2) K) (tree R K) where
  smul_adj g {x y} h := by
    rw [tree_adj_iff] at h ⊢
    refine ⟨fun hxy => h.1 (MulAction.injective g hxy), ?_⟩
    exact h.2.imp (VertRel.gl_smul g) (VertRel.gl_smul g)

instance instGraphActionPGLTree : GraphAction (Matrix.ProjGenLinGroup (Fin 2) K) (tree R K) where
  smul_adj q {x y} h := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g => ?_
    rw [pgl_mk_smul, pgl_mk_smul]
    exact GraphAction.smul_adj g h

end BruhatTits
end CerednikDrinfeld
end


