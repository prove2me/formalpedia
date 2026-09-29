-- Prove2me | Definitions.Def_ModularCurve_ComponentGroupOrder
-- name    : ModularCurve_ComponentGroupOrder
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/bbe67a7a-6d0e-523a-ae7c-4d156c4d6a04
-- title:
--   Gram matrices and Gram-image bases for the component group
-- statement:
--   The ambient set-up is that of the character lattice of a graph of components: for a finite type $\iota$, $X =$ `characterLattice ι` is the kernel of the degree map $(D_x)_{x}\mapsto \sum_x D_x$ on $\iota \to \mathbb{Z}$, and for widths $e : \iota \to \mathbb{N}$ the map `gramMap e` sends $D \in X$ to the functional $D' \mapsto \sum_x e(x)\,D_xD'_x$ on $X$, so its cokernel in $\operatorname{Hom}_{\mathbb{Z}}(X,\mathbb{Z})$ is the component group `componentGroup e`. Three items are introduced here. First, `gramMatrixOf e v`, for an arbitrary family $v : \kappa \to X$ indexed by a finite type $\kappa$, is the $\kappa \times \kappa$ integer matrix whose $(i,j)$ entry is $\sum_x e(x)\,(v_i)_x (v_j)_x$, i.e. the value of the width pairing on $v_i$ and $v_j$; the family is not required to be a basis, and a simp lemma records the entries. Second, under the hypothesis $e(x) > 0$ for all $x$, and given a $\mathbb{Z}$-basis $c$ of $X$ indexed by $\kappa$, `gramRangeBasisOf` is the basis of the submodule $\operatorname{range}(\mathtt{gramMap } e) \subseteq \operatorname{Hom}_{\mathbb{Z}}(X,\mathbb{Z})$ obtained by transporting $c$ along the isomorphism of $X$ onto the range induced by the injectivity of `gramMap e` (the cited theorem [`ModularCurve.gramMap_injective`](../thm.html#ModularCurve.gramMap_injective)); its $i$-th vector is, as a functional on $X$, exactly $\mathtt{gramMap } e\,(c_i)$. Third, `toMatrix_dualBasis_gramRangeOf` computes the coordinates of these vectors in the dual basis $c^{\vee}$ of $\operatorname{Hom}_{\mathbb{Z}}(X,\mathbb{Z})$: the matrix `c.dualBasis.toMatrix` of the family $i \mapsto \mathtt{gramMap } e\,(c_i)$ is the transpose of `gramMatrixOf e c`. Since the width pairing is symmetric, this matrix is the Gram matrix of $c$ itself.
--
--   **Relation to Mathlib.** Mathlib supplies the infrastructure used (`Module.Dual`, `Basis.dualBasis`, `Basis.toMatrix`, `LinearEquiv.ofInjective`, and the structure theory of finitely generated modules over a PID); the Gram matrix of a family of lattice vectors for the width pairing, and the basis of the image of `gramMap`, are the project's own constructions, and `gramMatrixOf` is formed for an arbitrary indexed family rather than for a basis as in Mathlib's bilinear-form-to-matrix constructions.
--
--   **Where it is used.** These are the linear-algebra inputs to the general order formula $\#\Phi = |\det G|$ for the component group attached to widths $e$, obtained by putting the full-rank inclusion $\operatorname{range}(\mathtt{gramMap } e) \subseteq \operatorname{Hom}_{\mathbb{Z}}(X,\mathbb{Z})$ into Smith normal form. Applied to the supersingular points of $X_0(Mq)$ in characteristic $q$, with $e_x = \tfrac12\#\operatorname{Aut}(E_x)$, this yields the order of the component group of $J_0(Mq)$ at $q$ used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ComponentGroupOrder.lean

import Definitions.Def_ModularCurve_ComponentGroup
import Theorems.Thm_ModularCurve_gramMap_injective
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Finset Module

section GramMatrix
variable {ι : Type*} [Fintype ι] {κ : Type*}

def gramMatrixOf (e : ι → ℕ) (v : κ → characterLattice ι) : Matrix κ κ ℤ :=
  Matrix.of fun i j => gramMap e (v i) (v j)

@[simp] theorem gramMatrixOf_apply (e : ι → ℕ) (v : κ → characterLattice ι) (i j : κ) :
    gramMatrixOf e v i j = gramMap e (v i) (v j) :=
  rfl

end GramMatrix

section Engine
variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ] {e : ι → ℕ}

def gramRangeBasisOf (he : ∀ x, 0 < e x) (c : Basis κ ℤ (characterLattice ι)) :
    Basis κ ℤ (LinearMap.range (gramMap e)) :=
  c.map (LinearEquiv.ofInjective (gramMap e) (ModularCurve.gramMap_injective he))

@[simp] theorem gramRangeBasisOf_coe (he : ∀ x, 0 < e x)
    (c : Basis κ ℤ (characterLattice ι)) (i : κ) :
    (gramRangeBasisOf he c i : Module.Dual ℤ (characterLattice ι)) = gramMap e (c i) := by
  rw [gramRangeBasisOf, Basis.map_apply, LinearEquiv.ofInjective_apply]

theorem toMatrix_dualBasis_gramRangeOf (he : ∀ x, 0 < e x)
    (c : Basis κ ℤ (characterLattice ι)) :
    c.dualBasis.toMatrix ((↑) ∘ gramRangeBasisOf he c) =
      (gramMatrixOf e ⇑c).transpose := by
  ext i j
  rw [Basis.toMatrix_apply, Function.comp_apply, gramRangeBasisOf_coe, Basis.dualBasis_repr]
  rfl

end Engine

end ModularCurve


