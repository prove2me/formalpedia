-- Prove2me | Definitions.Def_AlgebraicGeometry_FGSubalgebraTensorStage
-- name    : AlgebraicGeometry_FGSubalgebraTensorStage
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/7d6ed64f-b0e5-5a84-857b-535b0d37e925
-- title:
--   Tensoring the filtered system of finitely generated subalgebras
-- statement:
--   Throughout, $k$ is a commutative ring and $A$, $\Gamma$ are commutative $k$-algebras, and $\mathrm{FGSubalgebra}\ k\ A$ denotes the subtype of $k$-subalgebras of $A$ that are finitely generated, ordered by inclusion. For such a subalgebra $D$, `tensorStage` is the type $\Gamma \otimes_k D$, regarded as a $\Gamma$-algebra; for $D \le D'$, `tensorStageMap` is the $\Gamma$-algebra homomorphism $\mathrm{id}_\Gamma \otimes (D \hookrightarrow D')$, and `tensorStageToColimit` is the $\Gamma$-algebra homomorphism $\mathrm{id}_\Gamma \otimes (D \hookrightarrow A) \colon \Gamma \otimes_k D \to \Gamma \otimes_k A$. The instance `tensorStage_directedSystem` records that these stages and transition maps form a `DirectedSystem`: the transition map along $D \le D$ is the identity, and the composite of the transitions along $D \le D'$ and $D' \le D''$ is the transition along $D \le D''$. The compatibility of the maps to $\Gamma \otimes_k A$ with the transitions is `tensorStageToColimit_comp`: the composite of $\mathrm{id}_\Gamma \otimes (D \hookrightarrow D')$ followed by the map to $\Gamma \otimes_k A$ at level $D'$ equals the map at level $D$.
--
--   Two auxiliary lemmas, `tensorStageToColimit_comm` and `tensorStageMap_comm`, identify these maps, after transport along the commutativity isomorphism $D \otimes_k \Gamma \cong \Gamma \otimes_k D$, with the maps obtained by tensoring the inclusions $D \hookrightarrow A$ and $D \hookrightarrow D'$ on the right by $\Gamma$. They serve the two substantive statements, which express $\Gamma \otimes_k A$ as the direct limit of the system in the elementwise sense: `tensorStageToColimit_surj` produces, for every $b \in \Gamma \otimes_k A$, a finitely generated $D$ and an $x \in \Gamma \otimes_k D$ mapping to $b$; and `tensorStageToColimit_zero` shows that if $x \in \Gamma \otimes_k D$ dies in $\Gamma \otimes_k A$ then it already dies in $\Gamma \otimes_k D'$ for some finitely generated $D' \supseteq D$.
--
--   **Relation to Mathlib.** The transition and comparison maps are Mathlib's `Algebra.TensorProduct.map` and the directedness is packaged in Mathlib's `DirectedSystem`; the proofs of the surjectivity and vanishing statements reduce, via the commutativity isomorphism of the tensor product, to the corresponding module-theoretic facts `TensorProduct.Algebra.exists_of_fg` and `TensorProduct.Algebra.eq_of_fg_of_subtype_eq` about the first tensor factor.
--
--   **Where it is used.** Together with the diagram of finitely generated subalgebras and its `Spec` cone, these facts allow statements about $\operatorname{Spec}$ of a base change $\Gamma \otimes_k A$ to be descended to the finite-type stages $\Gamma \otimes_k D$, which is the standard device for reducing assertions about an arbitrary affine scheme to a limit of finite-type ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_FGSubalgebraTensorStage.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FGSubalgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.FGSubalgebra

variable (k : Type u) [CommRing k] (A : Type u) [CommRing A] [Algebra k A]
  (Γ : Type u) [CommRing Γ] [Algebra k Γ]

abbrev tensorStage (D : FGSubalgebra k A) : Type u := Γ ⊗[k] ↥D.1

noncomputable abbrev tensorStageMap (D D' : FGSubalgebra k A) (h : D ≤ D') :
    tensorStage k A Γ D →ₐ[Γ] tensorStage k A Γ D' :=
  Algebra.TensorProduct.map (AlgHom.id Γ Γ) (Subalgebra.inclusion (show D.1 ≤ D'.1 from h))

noncomputable abbrev tensorStageToColimit (D : FGSubalgebra k A) : tensorStage k A Γ D →ₐ[Γ] Γ ⊗[k] A :=
  Algebra.TensorProduct.map (AlgHom.id Γ Γ) D.1.val

instance tensorStage_directedSystem : DirectedSystem (tensorStage k A Γ) (fun i j h => tensorStageMap k A Γ i j h) where
  map_self := fun i x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul γ d => rw [Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, hx, hy]
  map_map := fun i j l hij hjl x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul γ d => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorStageToColimit_comp (i j : FGSubalgebra k A) (h : i ≤ j) :
    (tensorStageToColimit k A Γ j).comp (tensorStageMap k A Γ i j h) = tensorStageToColimit k A Γ i := by
  refine AlgHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul γ d => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorStageToColimit_comm (D : FGSubalgebra k A) (u : ↥D.1 ⊗[k] Γ) :
    tensorStageToColimit k A Γ D (TensorProduct.comm k _ _ u) = TensorProduct.comm k _ _ (D.1.val.toLinearMap.rTensor Γ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul d γ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorStageMap_comm (D D' : FGSubalgebra k A) (h : D ≤ D') (u : ↥D.1 ⊗[k] Γ) :
    tensorStageMap k A Γ D D' h (TensorProduct.comm k _ _ u) =
      TensorProduct.comm k _ _ ((Subalgebra.inclusion (show D.1 ≤ D'.1 from h)).toLinearMap.rTensor Γ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul d γ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorStageToColimit_surj (b : Γ ⊗[k] A) : ∃ (D : FGSubalgebra k A) (x : tensorStage k A Γ D), tensorStageToColimit k A Γ D x = b := by
  obtain ⟨D, hD, u, hu⟩ := TensorProduct.Algebra.exists_of_fg (TensorProduct.comm k _ _ b)
  refine ⟨⟨D, hD⟩, TensorProduct.comm k _ _ u, ?_⟩
  rw [tensorStageToColimit_comm, hu, ← TensorProduct.comm_symm, LinearEquiv.symm_apply_apply]

theorem tensorStageToColimit_zero (D : FGSubalgebra k A) (x : tensorStage k A Γ D) (hx : tensorStageToColimit k A Γ D x = 0) :
    ∃ (D' : FGSubalgebra k A) (h : D ≤ D'), tensorStageMap k A Γ D D' h x = 0 := by
  have hx' : D.1.val.toLinearMap.rTensor Γ ((TensorProduct.comm k _ _).symm x) =
      D.1.val.toLinearMap.rTensor Γ 0 := by
    rw [map_zero]
    have := tensorStageToColimit_comm k A Γ D ((TensorProduct.comm k _ _).symm x)
    rw [LinearEquiv.apply_symm_apply, hx] at this
    exact (LinearEquiv.map_eq_zero_iff _).mp this.symm
  obtain ⟨D', hDD', hD', h⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq D.2 hx'
  refine ⟨⟨D', hD'⟩, hDD', ?_⟩
  rw [map_zero] at h
  have := tensorStageMap_comm k A Γ D ⟨D', hD'⟩ hDD' ((TensorProduct.comm k _ _).symm x)
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this, h, map_zero]

end AlgebraicGeometry.FGSubalgebra


