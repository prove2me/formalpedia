-- Prove2me | Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
-- name    : AlgebraicCurve_GluedPic0SliceOps
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/5ed93ca7-23fb-5172-82d9-aeaf8c6b6971
-- title:
--   Block operators on Pic⁰ pairs; node-data transport
-- statement:
--   Two families of operations are introduced, matching the two slices of the glued Picard group `GluedPic0 K F S` (the quotient of admissible gluing data, i.e. pairs of degree-zero divisors vanishing at the chosen node places together with a node-unit function $\underline S \to \mathrm{Additive}\,K^\times$, by the glued principal data). For an additive commutative group $A$, `Pic0Pair.blockOp a b c d` is the endomorphism of $A \times A$ given by four endomorphisms arranged as a $2\times 2$ matrix: $(x,y) \mapsto (a x + b y,\ c x + d y)$. The accompanying lemmas identify composition of two such operators with the matrix product, $(a,b;c,d)\cdot(a',b';c',d') = (a a' + b c',\ a b' + b d';\ c a' + d c',\ c b' + d d')$, identify `blockOp a 0 0 d` with the product map $a \times d$, and identify the unit matrix with the identity. For node data, `NodeData.perm σ w` $= w \circ \sigma$ along a bijection $\sigma : S \simeq S'$, `NodeData.map θ w` $= \theta \circ w$ along a map of value sets, and `NodeData.corr B w` sends $s$ to $\sum_{s'} B(s,s') \cdot w(s')$ for an integer matrix $B : S \to S' \to \mathbb Z$ with $S'$ finite and values in an additive group. Three compatibility statements show these to be the transposes of the corresponding maps on integer-valued functions under the pairing $\mathrm{zpowProd}\,a\,w = \prod_s w(s)^{a(s)}$: pairing with `permMapFun σ a` (respectively `corrMapFun B a`, given by $s' \mapsto \sum_s a(s) B(s,s')$) equals pairing $a$ against `perm σ w` (respectively `corr B w`), and $\mathrm{zpowProd}\,a\,(\theta \circ w) = \theta(\mathrm{zpowProd}\,a\,w)$ for a homomorphism $\theta$ of commutative groups.
--
--   Finally, the functoriality of `GluedPic0` under a semilinear automorphism $g$ of $F/K$ satisfying `IsNodeStable S g` (so $(g\cdot s_1, g\cdot s_2) \in S$ for every $s \in S$) is recorded slice by slice: on the $\mathrm{Pic}^0 \times \mathrm{Pic}^0$ quotient, `glueMap` becomes the diagonal block operator with the action of $g$ in both diagonal entries, and on node units it sends `nodeUnit S w` to `nodeUnit S` of the node data obtained by precomposing $w$ with the inverse of the induced permutation `nodePerm S g hstab` of $S$ and then applying the automorphism of $K^\times$ induced by $g$ on the base field.
--
--   **Relation to Mathlib.** `blockOp` packages Mathlib's `AddMonoidHom.coprod`/`prod` into matrix notation for endomorphisms of $A \times A$; the glued Picard group, its node data and the character-lattice pairing `zpowProd` are the project's own notions, with no Mathlib counterpart.
--
--   **Where it is used.** The glued Picard group models the Picard group of a curve with prescribed pairs of identified points (as for the Deligne–Rapoport model of a modular curve at a prime of multiplicative reduction), whose two slices are the Picard groups of the components and the toric part indexed by the nodes. These operations fix the shape in which Hecke operators, diamond operators and degeneracy maps are presented on the two slices in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_GluedPic0SliceOps.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0Pushforward
import Definitions.Def_ModularCurve_CharacterLatticePairings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AlgebraicCurve

open Finset

namespace Pic0Pair

variable {A : Type*} [AddCommGroup A]

def blockOp (a b c d : A →+ A) : A × A →+ A × A :=
  (a.coprod b).prod (c.coprod d)

@[simp]
theorem blockOp_apply (a b c d : A →+ A) (x y : A) :
    blockOp a b c d (x, y) = (a x + b y, c x + d y) := rfl

theorem blockOp_comp (a b c d a' b' c' d' : A →+ A) :
    (blockOp a b c d).comp (blockOp a' b' c' d') =
      blockOp (a.comp a' + b.comp c') (a.comp b' + b.comp d') (c.comp a' + d.comp c') (c.comp b' + d.comp d') := by
  ext ⟨x, y⟩ <;> simp [blockOp_apply, map_add, add_add_add_comm]

theorem blockOp_diag (a d : A →+ A) : blockOp a 0 0 d = a.prodMap d := by
  ext ⟨x, y⟩ <;> simp [blockOp_apply]

theorem blockOp_one_zero_zero_one : blockOp (AddMonoidHom.id A) 0 0 (AddMonoidHom.id A) = AddMonoidHom.id _ := by
  ext ⟨x, y⟩ <;> simp [blockOp_apply]

end Pic0Pair

namespace NodeData

variable {S S' : Type*} {V V' : Type*}

def perm (σ : S ≃ S') (w : S' → V) : S → V := w ∘ σ

@[simp]
theorem perm_apply (σ : S ≃ S') (w : S' → V) (s : S) : perm σ w s = w (σ s) := rfl

def map (θ : V → V') (w : S → V) : S → V' := θ ∘ w

@[simp]
theorem map_apply (θ : V → V') (w : S → V) (s : S) : map θ w s = θ (w s) := rfl

def corr [AddCommGroup V] [Fintype S'] (B : S → S' → ℤ) (w : S' → V) : S → V :=
  fun s => ∑ s', B s s' • w s'

@[simp]
theorem corr_apply [AddCommGroup V] [Fintype S'] (B : S → S' → ℤ) (w : S' → V) (s : S) :
    corr B w s = ∑ s', B s s' • w s' := rfl

variable [Fintype S] [Fintype S'] {G : Type*} [CommGroup G]

theorem zpowProd_permMapFun_eq (σ : S ≃ S') (a : S → ℤ) (w : S' → Additive G) :
    ModularCurve.CharacterLattice.zpowProd (ModularCurve.CharacterLattice.permMapFun σ a) (fun s' => Additive.toMul (w s')) =
      ModularCurve.CharacterLattice.zpowProd a (fun s => Additive.toMul (perm σ w s)) :=
  ModularCurve.CharacterLattice.zpowProd_permMapFun σ a _

theorem zpowProd_corrMapFun_eq (B : S → S' → ℤ) (a : S → ℤ) (w : S' → Additive G) :
    ModularCurve.CharacterLattice.zpowProd (ModularCurve.CharacterLattice.corrMapFun B a) (fun s' => Additive.toMul (w s')) =
      ModularCurve.CharacterLattice.zpowProd a (fun s => Additive.toMul (corr B w s)) := by
  rw [ModularCurve.CharacterLattice.zpowProd_corrMapFun]
  refine congrArg (ModularCurve.CharacterLattice.zpowProd a) (funext fun s => ?_)
  simp [corr_apply, toMul_sum, toMul_zsmul]

theorem zpowProd_map {G' : Type*} [CommGroup G'] (θ : G →* G') (a : S → ℤ) (w : S → G) :
    ModularCurve.CharacterLattice.zpowProd a (map θ w) = θ (ModularCurve.CharacterLattice.zpowProd a w) := by
  simp [ModularCurve.CharacterLattice.zpowProd_def, map_prod, map_zpow]

end NodeData

namespace GluedPic0

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (S : Finset (Place K F × Place K F)) (g : SemilinearAut K F)

theorem toPic0Pair_glueMap_eq_blockOp (hstab : SemilinearAut.IsNodeStable S g) (ξ : GluedPic0 K F S) :
    toPic0Pair S (glueMap S g hstab ξ) =
      Pic0Pair.blockOp (DistribSMul.toAddMonoidHom (Pic0 K F) g) 0 0
        (DistribSMul.toAddMonoidHom (Pic0 K F) g) (toPic0Pair S ξ) := by
  rw [toPic0Pair_glueMap]
  rcases toPic0Pair S ξ with ⟨x, y⟩
  simp [Pic0Pair.blockOp_apply]

theorem glueMap_nodeUnit_eq (hstab : SemilinearAut.IsNodeStable S g) (w : ↥S → Additive Kˣ) :
    glueMap S g hstab (nodeUnit S w) =
      nodeUnit S (NodeData.map (SemilinearAut.baseAutUnitsHom g)
        (NodeData.perm (SemilinearAut.nodePerm S g hstab).symm w)) :=
  glueMap_nodeUnit S g hstab w

end GluedPic0

end AlgebraicCurve


