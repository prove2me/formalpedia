-- Prove2me | Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
-- name    : AlgebraicGeometry_RigidifiedLineBundleOfInvertible
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/6fb131e8-1de9-5381-a76a-d8fd3a23dd3e
-- title:
--   Canonical rigidification of invertible modules over a base section
-- statement:
--   Fix a commutative ring $R$, a scheme $C$ with a structure morphism $c\colon C\to\operatorname{Spec}R$, a section $\varepsilon$ of $c$ over $\operatorname{Spec}R$, and $R$-schemes $T$, $T'$. Write $q_T=$ `pullback.snd c t` for the projection $C\times_R T\to T$ and $\varepsilon_T=$ `rigSection c t ε` for the induced section $T\to C\times_R T$; `rigSection_snd` records $\varepsilon_T$ followed by $q_T$ is $\mathrm{id}_T$, and `baseChangeSnd_snd` records that $1_C\times\psi$ followed by $q_T$ equals $q_{T'}$ followed by $\psi$ for a morphism $\psi\colon T'\to T$ over $\operatorname{Spec}R$. The abbreviation `rigCorrection ε t L` is the dual $(\varepsilon_T^{*}L)^{\vee}$, a module on $T$, and `rigSectionPullbackSndPullbackIso` is the resulting isomorphism $\varepsilon_T^{*}q_T^{*}D\cong D$. The main definition, `RigidifiedLineBundle.ofInvertible`, sends an invertible module $L$ on $C\times_R T$ (invertibility in the sense of the project predicate: every point has an open neighbourhood over which the restriction is isomorphic to the unit module) to the rigidified line bundle whose underlying module is $L\otimes q_T^{*}(\varepsilon_T^{*}L)^{\vee}$, with invertibility obtained from stability of the predicate under tensor, pullback and dual, and with the rigidification datum the existence of an isomorphism of its $\varepsilon_T$-pullback with $\mathcal O_T$. Two lemmas identify the underlying module with `Scheme.Modules.rigidify` applied to $\varepsilon_T,q_T,L$ and with the displayed tensor product. The remaining statements assert, as mere existence of isomorphisms of underlying modules (which is the equivalence relation defining classes in the rigidified relative Picard functor, not an equality of rigidified bundles): compatibility with isomorphisms $L\cong L'$; that for an already rigidified $M$ one has $\mathtt{ofInvertible}(M.L)\cong M.L$; multiplicativity in $L$ with respect to the tensor product of rigidified bundles; absorption of pullbacks from the base, $\mathtt{ofInvertible}(q_T^{*}N\otimes L)\cong\mathtt{ofInvertible}(L)$ for $N$ invertible on $T$; and compatibility with base change along $\psi$. Auxiliary monoidal lemmas give uniqueness of tensor inverses, the middle-four interchange $(W\otimes X)\otimes(Y\otimes Z)\cong(W\otimes Y)\otimes(X\otimes Z)$, and $\mathcal O^{\vee}\cong\mathcal O$.
--
--   **Relation to Mathlib.** Mathlib has no relative Picard functor, no rigidified line bundles and no invertibility predicate for sheaves of modules on a scheme; these, together with the monoidal and monoidal-closed structure on `X.Modules` used for tensor and dual, are the project's own, built on Mathlib's sheaves of modules and pullback functors.
--
--   **Where it is used.** These constructions provide the retraction from line bundles on $C\times_R T$ onto rigidified classes, so that a bundle given only up to isomorphism (for instance $\mathcal O(D-r\varepsilon_T)$ for a relative effective divisor) determines a point of the rigidified relative Picard functor. This is the input to representability of that functor and hence to the Jacobian with its relative group law as used for Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {V : Scheme.{u}}

def isoOfTensorIsoUnit (X Y Y' : V.Modules) (i : X ⊗ Y ≅ 𝟙_ _) (i' : X ⊗ Y' ≅ 𝟙_ _) : Y ≅ Y' :=
  (λ_ Y).symm ≪≫ (i'.symm ⊗ᵢ Iso.refl Y) ≪≫ ((β_ X Y') ⊗ᵢ Iso.refl Y) ≪≫ α_ Y' X Y ≪≫ (Iso.refl Y' ⊗ᵢ i) ≪≫ ρ_ Y'

def tensorTensorTensorComm (W X Y Z : V.Modules) : (W ⊗ X) ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X ⊗ Z) :=
  α_ _ _ _ ≪≫ (Iso.refl W ⊗ᵢ ((α_ _ _ _).symm ≪≫ (β_ X Y ⊗ᵢ Iso.refl Z) ≪≫ α_ _ _ _)) ≪≫ (α_ _ _ _).symm

theorem nonempty_dual_tensorUnit_iso (V : Scheme.{u}) : Nonempty (dual (𝟙_ V.Modules) ≅ 𝟙_ V.Modules) :=
  ⟨(λ_ _).symm ≪≫ (isInvertible_unit V).dual.2.some⟩

end Scheme.Modules

namespace RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T T' : Scheme.{u}}
  {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}

@[reassoc (attr := simp)]
theorem rigSection_snd (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (t : T ⟶ Spec (CommRingCat.of R)) :
    rigSection c t ε ≫ pullback.snd c t = 𝟙 T :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem baseChangeSnd_snd (ψ : SchemeHomOver t' t) :
    baseChangeSnd c ψ ≫ pullback.snd c t = pullback.snd c t' ≫ ψ.1 :=
  pullback.lift_snd _ _ _

abbrev rigCorrection (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (t : T ⟶ Spec (CommRingCat.of R))
    (L : (Limits.pullback c t).Modules) : T.Modules :=
  Scheme.Modules.dual ((Scheme.Modules.pullback (rigSection c t ε)).obj L)

def rigSectionPullbackSndPullbackIso (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (t : T ⟶ Spec (CommRingCat.of R))
    (D : T.Modules) :
    (Scheme.Modules.pullback (rigSection c t ε)).obj ((Scheme.Modules.pullback (pullback.snd c t)).obj D) ≅ D :=
  (Scheme.Modules.pullbackComp _ _).app D ≪≫ (Scheme.Modules.pullbackCongr (rigSection_snd ε t)).app D ≪≫
    (Scheme.Modules.pullbackId _).app D

def RigidifiedLineBundle.ofInvertible (L : (Limits.pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L) :
    RigidifiedLineBundle c ε t where
  L := Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t) L
  isInvertible := hL.tensor (((hL.pullback _).dual).1.pullback _)
  rigidified := ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    (Iso.refl _ ⊗ᵢ rigSectionPullbackSndPullbackIso ε t _) ≪≫ (hL.pullback _).dual.2.some⟩

@[simp] theorem RigidifiedLineBundle.ofInvertible_L (L : (Limits.pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L) :
    (RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L = Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t) L := rfl

theorem RigidifiedLineBundle.ofInvertible_L_eq_tensor (L : (Limits.pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L) :
    (RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L =
      L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (rigCorrection ε t L) := rfl

namespace RigidifiedLineBundle

theorem nonempty_ofInvertible_iso_of_iso {L L' : (Limits.pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L)
    (hL' : Scheme.Modules.IsInvertible L') (e : L ≅ L') :
    Nonempty ((ofInvertible (ε := ε) L hL).L ≅ (ofInvertible (ε := ε) L' hL').L) := by
  exact ⟨Scheme.Modules.rigidifyMapIso _ _ e⟩

theorem nonempty_ofInvertible_iso_of_rigidified (M : RigidifiedLineBundle c ε t) :
    Nonempty ((ofInvertible (ε := ε) M.L M.isInvertible).L ≅ M.L) := by
  let d := Scheme.Modules.dualMapIso M.rigidified.some
  obtain ⟨u⟩ := Scheme.Modules.nonempty_dual_tensorUnit_iso T
  exact ⟨(Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback _).mapIso (d ≪≫ u) ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _)) ≪≫
    ρ_ M.L⟩

theorem nonempty_ofInvertible_tensor_iso {L L' : (Limits.pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L)
    (hL' : Scheme.Modules.IsInvertible L') :
    Nonempty ((ofInvertible (ε := ε) (L ⊗ L') (hL.tensor hL')).L ≅
      ((ofInvertible (ε := ε) L hL).tensor (ofInvertible (ε := ε) L' hL')).L) := by
  have hεL := hL.pullback (rigSection c t ε)
  have hεL' := hL'.pullback (rigSection c t ε)

  let d₁ := Scheme.Modules.dualMapIso (Scheme.Modules.pullbackTensorObjIso (rigSection c t ε) L L')
  obtain ⟨d₂⟩ := hεL.dual_tensor hεL'
  refine ⟨(Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback _).mapIso (d₁ ≪≫ d₂) ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _)) ≪≫
    Scheme.Modules.tensorTensorTensorComm _ _ _ _⟩

theorem nonempty_ofInvertible_pullbackSnd_tensor_iso {N : T.Modules} (hN : Scheme.Modules.IsInvertible N)
    {L : (Limits.pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((ofInvertible (ε := ε) ((Scheme.Modules.pullback (pullback.snd c t)).obj N ⊗ L) ((hN.pullback _).tensor hL)).L ≅
      (ofInvertible (ε := ε) L hL).L) := by
  have hεL := hL.pullback (rigSection c t ε)

  let d₁ := Scheme.Modules.dualMapIso
    (Scheme.Modules.pullbackTensorObjIso (rigSection c t ε) _ L ≪≫ (rigSectionPullbackSndPullbackIso ε t N ⊗ᵢ Iso.refl _))
  obtain ⟨d₂⟩ := hN.dual_tensor hεL
  obtain ⟨p⟩ := hN.dual.2
  refine ⟨(Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback _).mapIso (d₁ ≪≫ d₂) ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _)) ≪≫
    Scheme.Modules.tensorTensorTensorComm _ _ _ _ ≪≫
    (((Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso p ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _) ⊗ᵢ Iso.refl _) ≪≫ λ_ _⟩

theorem nonempty_ofInvertible_pullbackAlong_iso (ψ : SchemeHomOver t' t) {L : (Limits.pullback c t).Modules}
    (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (((ofInvertible (ε := ε) L hL).pullbackAlong ψ).L ≅
      (ofInvertible (ε := ε) ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj L) (hL.pullback _)).L) := by
  have hεL := hL.pullback (rigSection c t ε)

  obtain ⟨d₁⟩ := hεL.pullback_dual ψ.1
  let d₂ := Scheme.Modules.dualMapIso
    ((Scheme.Modules.pullbackComp ψ.1 (rigSection c t ε)).app L ≪≫
      (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε ψ).symm).app L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L).symm)
  refine ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ ?_)⟩

  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr (baseChangeSnd_snd ψ)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫ (Scheme.Modules.pullback _).mapIso (d₁ ≪≫ d₂)

end RigidifiedLineBundle

end RelPicard

end AlgebraicGeometry

end


