-- Prove2me | Definitions.Def_AlgebraicGeometry_OModulePresheafTensorMap
-- name    : AlgebraicGeometry_OModulePresheafTensorMap
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/8934c021-5e4b-5fed-b0c9-f281ccb684d6
-- title:
--   Tensor product of morphisms of O-module presheaves
-- statement:
--   Throughout, $R$ is a commutative ring, $V$ a scheme, $\pi : V \to \operatorname{Spec} R$ a morphism, and $F, F', F'', G, G', G''$ are objects of `OModulePresheaf π`: data assigning to every open $U \subseteq V$ an abelian group $F(U)$ carrying compatible module structures over $R$ and over $\Gamma(V,U)$ (compatible via the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$), together with $R$-linear restriction maps $F(U') \to F(U)$ for $U \le U'$ that are semilinear for restriction of functions and satisfy the identity and composition laws — no sheaf condition. The tensor product `F.tensor G` has sections $F(U) \otimes_{\Gamma(V,U)} G(U)$ with diagonal restriction. A `Hom F G` is a family of $R$-linear maps $F(U) \to G(U)$ that are $\Gamma(V,U)$-linear and commute with restriction; `appSections` is the component regarded as $\Gamma(V,U)$-linear.
--
--   For $\varphi : F \to F'$ and $\psi : G \to G'$, `Hom.tensorMapApp` is, at each open $U$, the $\Gamma(V,U)$-linear map $\varphi_U \otimes \psi_U$ on the tensor products, and `Hom.tensorMap` packages these components into a morphism $F \otimes G \to F' \otimes G'$, its naturality being verified on pure tensors. Accompanying identities record the value on a pure tensor, $x \otimes y \mapsto \varphi_U(x) \otimes \psi_U(y)$, and on a general element. `Hom.ext_app` states that a morphism is determined by its family of components, and `Hom.tensorMap_id_id`, `Hom.tensorMap_comp` give bifunctoriality: the tensor of identities is the identity, and $(\varphi'\varphi) \otimes (\psi'\psi) = (\varphi' \otimes \psi') \circ (\varphi \otimes \psi)$.
--
--   The same constructions and identities are repeated verbatim for `AffHom`, where components are indexed by the affine opens of $V$, and `Hom.toAffHom_tensorMap` states that restricting a tensor of morphisms to affine opens is the tensor of the restrictions.
--
--   **Relation to Mathlib.** `OModulePresheaf` and its morphism structures `Hom`/`AffHom` are the project's own presentation of open-by-open module data over $\Gamma(V,\cdot)$, distinct from Mathlib's sheaves of modules on a scheme; the components here are built from Mathlib's `TensorProduct.map`.
--
--   **Where it is used.** These morphisms supply the maps induced on open-by-open tensor products, in particular on twists $F \otimes \mathcal{T}$ by an invertible datum, and hence the induced maps on the alternating Čech complexes attached to an ordered affine cover that are used in the coherent-sheaf finiteness and base-change arguments of the tree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OModulePresheafTensorMap.lean

import Mathlib

import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory TensorProduct

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F F' F'' G G' G'' : OModulePresheaf π}

namespace Hom

def tensorMapApp (φ : Hom F F') (ψ : Hom G G') (U : V.Opens) :
    F.obj U ⊗[Γ(V, U)] G.obj U →ₗ[Γ(V, U)] F'.obj U ⊗[Γ(V, U)] G'.obj U :=
  TensorProduct.map (φ.appSections U) (ψ.appSections U)

theorem tensorMapApp_tmul (φ : Hom F F') (ψ : Hom G G') (U : V.Opens) (x : F.obj U) (y : G.obj U) :
    tensorMapApp φ ψ U (x ⊗ₜ y) = φ.app U x ⊗ₜ ψ.app U y := rfl

def tensorMap (φ : Hom F F') (ψ : Hom G G') : Hom (F.tensor G) (F'.tensor G') where
  app U :=
    letI := F.tensorObjModule G U; letI := F'.tensorObjModule G' U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    { toFun := tensorMapApp φ ψ U
      map_add' := fun s t => map_add _ s t
      map_smul' := fun r t => by
        show tensorMapApp φ ψ U (algebraMap R Γ(V, U) r • t) = algebraMap R Γ(V, U) r • tensorMapApp φ ψ U t
        exact LinearMap.map_smul _ _ _ }
  app_smul U a t := LinearMap.map_smul (tensorMapApp φ ψ U) a t
  naturality {U U'} h := by
    letI := F.tensorObjModule G U; letI := F.tensorObjModule G U'
    letI := F'.tensorObjModule G' U; letI := F'.tensorObjModule G' U'
    refine LinearMap.ext fun t => ?_
    show tensorMapApp φ ψ U (F.tensorResₛₗ G h t) = F'.tensorResₛₗ G' h (tensorMapApp φ ψ U' t)
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      rw [tensorResₛₗ_tmul, tensorMapApp_tmul, tensorMapApp_tmul, tensorResₛₗ_tmul, φ.naturality_apply,
        ψ.naturality_apply]
    | add s t hs ht => rw [map_add, map_add, hs, ht, ← map_add, ← map_add]

theorem tensorMap_app_tmul (φ : Hom F F') (ψ : Hom G G') (U : V.Opens) (x : F.obj U) (y : G.obj U) :
    (tensorMap φ ψ).app U (show (F.tensor G).obj U from x ⊗ₜ y)
      = (show (F'.tensor G').obj U from φ.app U x ⊗ₜ ψ.app U y) := rfl

theorem tensorMap_app_apply (φ : Hom F F') (ψ : Hom G G') (U : V.Opens) (t : F.obj U ⊗[Γ(V, U)] G.obj U) :
    (tensorMap φ ψ).app U (show (F.tensor G).obj U from t)
      = (show (F'.tensor G').obj U from TensorProduct.map (φ.appSections U) (ψ.appSections U) t) := rfl

theorem ext_app {φ ψ : Hom F G} (h : ∀ U, φ.app U = ψ.app U) : φ = ψ := by
  obtain ⟨a, _, _⟩ := φ
  obtain ⟨b, _, _⟩ := ψ
  obtain rfl : a = b := funext h
  rfl

theorem tensorMap_id_id : tensorMap (Hom.id F) (Hom.id G) = Hom.id (F.tensor G) := by
  refine ext_app fun U => ?_
  letI := F.tensorObjModule G U
  refine LinearMap.ext fun t => ?_
  show TensorProduct.map ((Hom.id F).appSections U) ((Hom.id G).appSections U) t = t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rfl
  | add s t hs ht => rw [map_add, hs, ht]

theorem tensorMap_comp (φ' : Hom F' F'') (φ : Hom F F') (ψ' : Hom G' G'') (ψ : Hom G G') :
    tensorMap (φ'.comp φ) (ψ'.comp ψ) = (tensorMap φ' ψ').comp (tensorMap φ ψ) := by
  refine ext_app fun U => ?_
  letI := F.tensorObjModule G U; letI := F''.tensorObjModule G'' U
  refine LinearMap.ext fun t => ?_
  show TensorProduct.map ((φ'.comp φ).appSections U) ((ψ'.comp ψ).appSections U) t
    = TensorProduct.map (φ'.appSections U) (ψ'.appSections U) (TensorProduct.map (φ.appSections U) (ψ.appSections U) t)
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rfl
  | add s t hs ht => rw [map_add, hs, ht, map_add, map_add]

end Hom

namespace AffHom

def tensorMapApp (φ : AffHom F F') (ψ : AffHom G G') (U : V.affineOpens) :
    F.obj U.1 ⊗[Γ(V, U.1)] G.obj U.1 →ₗ[Γ(V, U.1)] F'.obj U.1 ⊗[Γ(V, U.1)] G'.obj U.1 :=
  TensorProduct.map (φ.appSections U) (ψ.appSections U)

theorem tensorMapApp_tmul (φ : AffHom F F') (ψ : AffHom G G') (U : V.affineOpens) (x : F.obj U.1) (y : G.obj U.1) :
    tensorMapApp φ ψ U (x ⊗ₜ y) = φ.app U x ⊗ₜ ψ.app U y := rfl

def tensorMap (φ : AffHom F F') (ψ : AffHom G G') : AffHom (F.tensor G) (F'.tensor G') where
  app U :=
    letI := F.tensorObjModule G U.1; letI := F'.tensorObjModule G' U.1
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U.1
    { toFun := tensorMapApp φ ψ U
      map_add' := fun s t => map_add _ s t
      map_smul' := fun r t => by
        show tensorMapApp φ ψ U (algebraMap R Γ(V, U.1) r • t) = algebraMap R Γ(V, U.1) r • tensorMapApp φ ψ U t
        exact LinearMap.map_smul _ _ _ }
  app_smul U a t := LinearMap.map_smul (tensorMapApp φ ψ U) a t
  naturality {U U'} h := by
    letI := F.tensorObjModule G U.1; letI := F.tensorObjModule G U'.1
    letI := F'.tensorObjModule G' U.1; letI := F'.tensorObjModule G' U'.1
    refine LinearMap.ext fun t => ?_
    show tensorMapApp φ ψ U (F.tensorResₛₗ G h t) = F'.tensorResₛₗ G' h (tensorMapApp φ ψ U' t)
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      rw [tensorResₛₗ_tmul, tensorMapApp_tmul, tensorMapApp_tmul, tensorResₛₗ_tmul, φ.naturality_apply,
        ψ.naturality_apply]
    | add s t hs ht => rw [map_add, map_add, hs, ht, ← map_add, ← map_add]

theorem tensorMap_app_tmul (φ : AffHom F F') (ψ : AffHom G G') (U : V.affineOpens) (x : F.obj U.1) (y : G.obj U.1) :
    (tensorMap φ ψ).app U (show (F.tensor G).obj U.1 from x ⊗ₜ y)
      = (show (F'.tensor G').obj U.1 from φ.app U x ⊗ₜ ψ.app U y) := rfl

theorem tensorMap_app_apply (φ : AffHom F F') (ψ : AffHom G G') (U : V.affineOpens)
    (t : F.obj U.1 ⊗[Γ(V, U.1)] G.obj U.1) :
    (tensorMap φ ψ).app U (show (F.tensor G).obj U.1 from t)
      = (show (F'.tensor G').obj U.1 from TensorProduct.map (φ.appSections U) (ψ.appSections U) t) := rfl

theorem ext_app {φ ψ : AffHom F G} (h : ∀ U, φ.app U = ψ.app U) : φ = ψ := by
  obtain ⟨a, _, _⟩ := φ
  obtain ⟨b, _, _⟩ := ψ
  obtain rfl : a = b := funext h
  rfl

theorem tensorMap_id_id : tensorMap (AffHom.id F) (AffHom.id G) = AffHom.id (F.tensor G) := by
  refine ext_app fun U => ?_
  letI := F.tensorObjModule G U.1
  refine LinearMap.ext fun t => ?_
  show TensorProduct.map ((AffHom.id F).appSections U) ((AffHom.id G).appSections U) t = t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rfl
  | add s t hs ht => rw [map_add, hs, ht]

theorem tensorMap_comp (φ' : AffHom F' F'') (φ : AffHom F F') (ψ' : AffHom G' G'') (ψ : AffHom G G') :
    tensorMap (φ'.comp φ) (ψ'.comp ψ) = (tensorMap φ' ψ').comp (tensorMap φ ψ) := by
  refine ext_app fun U => ?_
  letI := F.tensorObjModule G U.1; letI := F''.tensorObjModule G'' U.1
  refine LinearMap.ext fun t => ?_
  show TensorProduct.map ((φ'.comp φ).appSections U) ((ψ'.comp ψ).appSections U) t
    = TensorProduct.map (φ'.appSections U) (ψ'.appSections U) (TensorProduct.map (φ.appSections U) (ψ.appSections U) t)
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rfl
  | add s t hs ht => rw [map_add, hs, ht, map_add, map_add]

end AffHom

theorem Hom.toAffHom_tensorMap (φ : Hom F F') (ψ : Hom G G') :
    (Hom.tensorMap φ ψ).toAffHom = AffHom.tensorMap φ.toAffHom ψ.toAffHom := rfl

end AlgebraicGeometry.OModulePresheaf

end


