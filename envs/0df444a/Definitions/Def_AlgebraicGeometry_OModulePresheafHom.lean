-- Prove2me | Definitions.Def_AlgebraicGeometry_OModulePresheafHom
-- name    : AlgebraicGeometry_OModulePresheafHom
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/8f1696f4-cd0d-504b-befe-f14adc61b952
-- title:
--   Morphisms and exact sequences of O-module presheaves
-- statement:
--   Fix a commutative ring $R$, a scheme $V$ and a morphism $\pi\colon V\to\operatorname{Spec}R$. For $\mathcal O$-module presheaf data $F,G$ over $\pi$ (a family of $R$- and $\Gamma(V,U)$-modules $F(U)$, indexed by the opens of $V$, with compatible $R$-linear restriction maps), the structure `Hom F G` consists of: an $R$-linear map $\varphi_U\colon F(U)\to G(U)$ for every open $U\subseteq V$; the condition $\varphi_U(a\cdot x)=a\cdot\varphi_U(x)$ for $a\in\Gamma(V,U)$; and the naturality identity $\varphi_U\circ F.\mathrm{res}_h=G.\mathrm{res}_h\circ\varphi_{U'}$ for each inclusion $U\le U'$. `appSections` repackages $\varphi_U$ as a $\Gamma(V,U)$-linear map, and `Hom.id`, `Hom.comp` give the identity and (contravariantly written) composition. The structure `SES F₁ F₂ F₃` bundles two morphisms $\iota\colon F_1\to F_2$, $p\colon F_2\to F_3$ together with the requirements, imposed at *every* open $U$, that $\iota_U$ is injective, $p_U$ is surjective and $\operatorname{im}\iota_U=\ker p_U$; exactness is thus a condition on sections over all opens, not a sheaf-theoretic one. `AffHom` and `AffSES` are the same data and conditions stated only for $U$ ranging over the affine opens `V.affineOpens`, and `Hom.toAffHom`, `SES.toAffSES` restrict the unrestricted notions to the affine ones.
--
--   Two geometric lemmas precede this. If $\pi$ is separated, the intersection of two affine opens of $V$ is affine (`isAffineOpen_inf_of_isSeparated`, obtained from affineness of the diagonal of $\pi$); by induction, each finite intersection $U_s=\bigcap_j U_{s_j}$ attached to an index $s$ of an ordered affine cover $K$ is affine (`isAffineOpen_inter`), and `affineInter` records it as an element of `V.affineOpens`.
--
--   Consequently, for separated $\pi$, an `AffHom` $\varphi$ acts on alternating Čech cochains: `cochainMap` sends $c\mapsto(\varphi_{U_s}(c_s))_s$, `cochainMap_comp_d` states that this commutes with the Čech differential, `kerMap` is the induced map on cocycles, `H0Map` its degree-$0$ case, and `HSuccMap` the induced $R$-linear map on $\ker d^{i+1}/\operatorname{im}d^{i}$.
--
--   **Relation to Mathlib.** The `Hom`, `SES`, `AffHom`, `AffSES` structures are the project's own, attached to its `OModulePresheaf` data rather than to Mathlib's category of presheaves of modules; no category instance is introduced here. The affineness of $U\cap W$ is deduced from Mathlib's separatedness API, via `isAffineHom_diagonal_iff` applied to `pullback.diagonal π`.
--
--   **Where it is used.** These notions supply the maps of Čech complexes used in the finiteness statements for Čech cohomology of coherent module-presheaf data over a base $\operatorname{Spec}R$; exactness is demanded over each (affine) open so that kernels, images and cokernels can be formed sectionwise, without sheafification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OModulePresheafHom.lean

import Mathlib

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Morphisms.Separated

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite Limits

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

namespace Scheme.OrderedAffineCover

variable (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover)

theorem isAffineOpen_inf_of_isSeparated [IsSeparated π] {U W : V.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (U ⊓ W) := by
  haveI : IsAffineHom (pullback.diagonal π) := inferInstance
  exact isAffineHom_diagonal_iff.mp this ⊤ (isAffineOpen_top _) U (by simp) W (by simp) hU hW

theorem isAffineOpen_inter [IsSeparated π] {i : ℕ} (s : K.Idx i) : IsAffineOpen (K.inter s) := by
  suffices h : ∀ (n : ℕ) (t : Fin (n + 1) → K.ι), IsAffineOpen (⨅ j, K.U (t j)) from h i s.1
  intro n
  induction n with
  | zero =>
    intro t
    have h1 : (⨅ j : Fin 1, K.U (t j)) = K.U (t 0) :=
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)
    rw [h1]; exact K.isAffineOpen (t 0)
  | succ m ih =>
    intro t
    have hsplit : (⨅ j : Fin (m + 2), K.U (t j)) = K.U (t 0) ⊓ (⨅ j : Fin (m + 1), K.U (t j.succ)) :=
      le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
        (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
    rw [hsplit]
    exact isAffineOpen_inf_of_isSeparated π (K.isAffineOpen (t 0)) (ih (t ∘ Fin.succ))

abbrev affineInter [IsSeparated π] {i : ℕ} (s : K.Idx i) : V.affineOpens :=
  ⟨K.inter s, K.isAffineOpen_inter π s⟩

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {π : V ⟶ Spec (.of R)}

structure Hom (F G : OModulePresheaf π) where

  app : ∀ U : V.Opens, F.obj U →ₗ[R] G.obj U
  app_smul : ∀ (U : V.Opens) (a : Γ(V, U)) (x : F.obj U), app U (a • x) = a • app U x
  naturality : ∀ {U U' : V.Opens} (h : U ≤ U'), app U ∘ₗ F.res h = G.res h ∘ₗ app U'

structure SES (F₁ F₂ F₃ : OModulePresheaf π) where

  inc : Hom F₁ F₂

  proj : Hom F₂ F₃
  injective : ∀ U : V.Opens, Function.Injective (inc.app U)
  surjective : ∀ U : V.Opens, Function.Surjective (proj.app U)
  exact : ∀ U : V.Opens, LinearMap.range (inc.app U) = LinearMap.ker (proj.app U)

structure AffHom (F G : OModulePresheaf π) where

  app : ∀ U : V.affineOpens, F.obj U.1 →ₗ[R] G.obj U.1
  app_smul : ∀ (U : V.affineOpens) (a : Γ(V, U.1)) (x : F.obj U.1), app U (a • x) = a • app U x
  naturality : ∀ {U U' : V.affineOpens} (h : U.1 ≤ U'.1), app U ∘ₗ F.res h = G.res h ∘ₗ app U'

structure AffSES (F₁ F₂ F₃ : OModulePresheaf π) where

  inc : AffHom F₁ F₂

  proj : AffHom F₂ F₃
  injective : ∀ U : V.affineOpens, Function.Injective (inc.app U)
  surjective : ∀ U : V.affineOpens, Function.Surjective (proj.app U)
  exact : ∀ U : V.affineOpens, LinearMap.range (inc.app U) = LinearMap.ker (proj.app U)

namespace Hom

variable {F G H : OModulePresheaf π}

def appSections (φ : Hom F G) (U : V.Opens) : F.obj U →ₗ[Γ(V, U)] G.obj U :=
  { toFun := φ.app U, map_add' := (φ.app U).map_add, map_smul' := φ.app_smul U }

@[simp] theorem appSections_apply (φ : Hom F G) (U : V.Opens) (x : F.obj U) :
    φ.appSections U x = φ.app U x := rfl

theorem naturality_apply (φ : Hom F G) {U U' : V.Opens} (h : U ≤ U') (x : F.obj U') :
    φ.app U (F.res h x) = G.res h (φ.app U' x) :=
  congrFun (congrArg DFunLike.coe (φ.naturality h)) x

variable (F) in

protected def id : Hom F F where
  app _ := LinearMap.id
  app_smul _ _ _ := rfl
  naturality _ := rfl

def comp (ψ : Hom G H) (φ : Hom F G) : Hom F H where
  app U := ψ.app U ∘ₗ φ.app U
  app_smul U a x := by
    show ψ.app U (φ.app U (a • x)) = a • ψ.app U (φ.app U x)
    rw [φ.app_smul, ψ.app_smul]
  naturality h := by
    rw [LinearMap.comp_assoc, φ.naturality, ← LinearMap.comp_assoc, ψ.naturality, LinearMap.comp_assoc]

@[simp] theorem id_app (U : V.Opens) (x : F.obj U) : (Hom.id F).app U x = x := rfl
@[simp] theorem comp_app (ψ : Hom G H) (φ : Hom F G) (U : V.Opens) (x : F.obj U) :
    (ψ.comp φ).app U x = ψ.app U (φ.app U x) := rfl

def toAffHom (φ : Hom F G) : AffHom F G where
  app U := φ.app U.1
  app_smul U := φ.app_smul U.1
  naturality h := φ.naturality h

@[simp] theorem toAffHom_app (φ : Hom F G) (U : V.affineOpens) : φ.toAffHom.app U = φ.app U.1 := rfl

end Hom

namespace AffHom

variable {F G H : OModulePresheaf π}

def appSections (φ : AffHom F G) (U : V.affineOpens) : F.obj U.1 →ₗ[Γ(V, U.1)] G.obj U.1 :=
  { toFun := φ.app U, map_add' := (φ.app U).map_add, map_smul' := φ.app_smul U }

@[simp] theorem appSections_apply (φ : AffHom F G) (U : V.affineOpens) (x : F.obj U.1) :
    φ.appSections U x = φ.app U x := rfl

theorem naturality_apply (φ : AffHom F G) {U U' : V.affineOpens} (h : U.1 ≤ U'.1) (x : F.obj U'.1) :
    φ.app U (F.res h x) = G.res h (φ.app U' x) :=
  congrFun (congrArg DFunLike.coe (φ.naturality h)) x

variable (F) in

protected def id : AffHom F F where
  app _ := LinearMap.id
  app_smul _ _ _ := rfl
  naturality _ := rfl

def comp (ψ : AffHom G H) (φ : AffHom F G) : AffHom F H where
  app U := ψ.app U ∘ₗ φ.app U
  app_smul U a x := by
    show ψ.app U (φ.app U (a • x)) = a • ψ.app U (φ.app U x)
    rw [φ.app_smul, ψ.app_smul]
  naturality h := by
    rw [LinearMap.comp_assoc, φ.naturality, ← LinearMap.comp_assoc, ψ.naturality, LinearMap.comp_assoc]

@[simp] theorem id_app (U : V.affineOpens) (x : F.obj U.1) : (AffHom.id F).app U x = x := rfl
@[simp] theorem comp_app (ψ : AffHom G H) (φ : AffHom F G) (U : V.affineOpens) (x : F.obj U.1) :
    (ψ.comp φ).app U x = ψ.app U (φ.app U x) := rfl

end AffHom

def SES.toAffSES {F₁ F₂ F₃ : OModulePresheaf π} (S : SES F₁ F₂ F₃) : AffSES F₁ F₂ F₃ where
  inc := S.inc.toAffHom
  proj := S.proj.toAffHom
  injective U := S.injective U.1
  surjective U := S.surjective U.1
  exact U := S.exact U.1

section Cochains

variable [IsSeparated π] (K : V.OrderedAffineCover) {F G : OModulePresheaf π}

def AffHom.cochainMap (φ : AffHom F G) (i : ℕ) : F.cochain K i →ₗ[R] G.cochain K i :=
  LinearMap.pi fun s => (φ.app (K.affineInter π s)).comp (LinearMap.proj s)

theorem AffHom.cochainMap_apply (φ : AffHom F G) (i : ℕ) (f : F.cochain K i) (s : K.Idx i) :
    φ.cochainMap K i f s = φ.app (K.affineInter π s) (f s) := rfl

theorem AffHom.cochainMap_comp_d (φ : AffHom F G) (i : ℕ) :
    φ.cochainMap K (i + 1) ∘ₗ F.d K i = G.d K i ∘ₗ φ.cochainMap K i := by
  refine LinearMap.ext fun f => funext fun s => ?_
  simp only [LinearMap.comp_apply, AffHom.cochainMap_apply, OModulePresheaf.d_apply, map_sum, map_zsmul]
  exact Finset.sum_congr rfl fun j _ => congrArg _
    (φ.naturality_apply (U := K.affineInter π s) (U' := K.affineInter π (K.face s j))
      (K.inter_le_inter_face s j) _)

def AffHom.kerMap (φ : AffHom F G) (i : ℕ) :
    LinearMap.ker (F.d K i) →ₗ[R] LinearMap.ker (G.d K i) :=
  (φ.cochainMap K i).restrict fun f hf => LinearMap.mem_ker.mpr <| by
    rw [← LinearMap.comp_apply, ← AffHom.cochainMap_comp_d, LinearMap.comp_apply,
      LinearMap.mem_ker.mp hf, map_zero]

@[simp] theorem AffHom.kerMap_coe (φ : AffHom F G) (i : ℕ) (x : LinearMap.ker (F.d K i)) :
    (φ.kerMap K i x : G.cochain K i) = φ.cochainMap K i x := rfl

abbrev AffHom.H0Map (φ : AffHom F G) : F.H0 K →ₗ[R] G.H0 K := φ.kerMap K 0

def AffHom.HSuccMap (φ : AffHom F G) (i : ℕ) : F.HSucc K i →ₗ[R] G.HSucc K i :=
  Submodule.mapQ _ _ (φ.kerMap K (i + 1)) fun x hx => by
    obtain ⟨g, hg⟩ := (Submodule.mem_comap.mp hx)
    refine Submodule.mem_comap.mpr ⟨φ.cochainMap K i g, ?_⟩
    show G.d K i _ = φ.cochainMap K (i + 1) x.1
    rw [← LinearMap.comp_apply, ← AffHom.cochainMap_comp_d, LinearMap.comp_apply, hg]
    rfl

theorem AffHom.HSuccMap_mk (φ : AffHom F G) (i : ℕ) (x : LinearMap.ker (F.d K (i + 1))) :
    φ.HSuccMap K i (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φ.kerMap K (i + 1) x) := rfl

end Cochains

end OModulePresheaf

end AlgebraicGeometry

end


