-- Prove2me | Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
-- name    : WeierstrassCurve_DrinfeldLevelFunctor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/350fc150-95d7-5f8d-93e4-f2a734026f81
-- title:
--   Guarded group laws and the Drinfeld level component
-- statement:
--   Let $A$ be a commutative ring. `GroupLaws A` is the type of families assigning, to every $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that $\Delta(W)$ is a unit, a `RelativeGroupLaw` on the structure morphism $\mathrm{Proj}\,(T[X,Y,Z]/(W))\to\operatorname{Spec}T$ — that is, a group structure on the sets of sections $\mathrm{Hom}_{/\operatorname{Spec}T}(T',\cdot)$, natural in $T'$, with the group axioms and naturality of multiplication as fields. Compared with the unguarded family of the imported module, the quantifier is restricted to curves with invertible discriminant. Two predicates pin such a family down: `IsChordTangent` asks, for each $T,W,h_\Delta$, the existence of bijections between sections over $\operatorname{Spec}F$ and the affine point group of $W_F$, for all fields $F$ over $T$, which are additive and equivariant for $T$-automorphisms of $F$; `IsOriginIdentity` asks that the identity section factor through the chart $D_+(Y)$ via a ring homomorphism $\chi$ from the homogeneous localisation away from $Y$ with $\chi(X/Y)=\chi(Z/Y)=0$, i.e. that the identity be $[0:1:0]$.
--
--   For a raw triple $x=(W',P,Q)$, `RawDrinfeldPair.IsLevel 𝒢 q W x` says $W'=W$ and, for some unit proof, the $q^2$ sections $aP+bQ$ ($0\le a,b<q$) form a Drinfeld basis: the product of the kernel ideal sheaves of their graphs equals the ideal sheaf of the $q$-torsion subscheme. `LevelTransport` is a structure carrying base change along $A$-algebra maps and an action of variable changes on raw pairs, with functoriality, compatibility and preservation of `IsLevel` as fields; `IsSectionTransport` pins these operations on sections, requiring the transported $P,Q$ to pull back to the original ones along any graded homomorphism realising the variable change, respectively the coefficient map. Finally `levelComponent` assembles this into a [`ModularCurve.LevelComponent A`](../def/ModularCurve_WeierstrassLevelComponents.html#L15), and `rigidData` combines it with the $\Gamma_0(N)$ cyclic-kernel and level-$\ell$ components into a [`ModularCurve.RigidWeierstrassData A`](../def/ModularCurve_WeierstrassLevelModuliDatum.html#L11).
--
--   **Relation to Mathlib.** Mathlib supplies `WeierstrassCurve.Projective`, `VariableChange`, `Proj` and ideal sheaf data; the relative group law on a morphism of schemes, the graded Proj model of a Weierstrass cubic, Drinfeld bases and level components are the project's own notions, defined in the imported modules.
--
--   **Where it is used.** These data furnish the moduli problem of elliptic curves with a $\Gamma_0(N)$-structure, a level-$\ell$ structure and a Drinfeld basis of the $q$-torsion, in the rigidified form used for the representability statement underlying the modular curves of the Frey-curve argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_DrinfeldLevelFunctor.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.DrinfeldGlobal

variable {A : Type u} [CommRing A]

abbrev GroupLaws (A : Type u) [CommRing A] : Type (u + 1) :=
  ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T), IsUnit W.Δ →
    RelativeGroupLaw T (projModelStrCR W)

def GroupLaws.IsChordTangent (𝒢 : GroupLaws A) : Prop :=
  ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ),
    ∃ ev, IsPointsEval W (𝒢 T W hΔ) ev

def GroupLaws.IsOriginIdentity (𝒢 : GroupLaws A) : Prop :=
  ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ),
    ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection ((𝒢 T W hΔ).one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0

def RawDrinfeldPair.IsLevel (𝒢 : GroupLaws A) (q : ℕ)
    {T : Type u} [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (x : RawDrinfeldPair T) : Prop :=
  x.curve = W ∧ ∃ hΔ : IsUnit x.curve.Δ, IsDrinfeldBasis (𝒢 T x.curve hΔ) q x.P x.Q

structure LevelTransport (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (q : ℕ) where
  map : {T T' : Type u} → [CommRing T] → [Algebra A T] → [CommRing T'] → [Algebra A T'] →
    (T →ₐ[A] T') → RawDrinfeldPair T → RawDrinfeldPair T'
  act : {T : Type u} → [CommRing T] → [Algebra A T] →
    WeierstrassCurve.VariableChange T → RawDrinfeldPair T → RawDrinfeldPair T
  map_id : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : RawDrinfeldPair T), map (AlgHom.id A T) x = x
  map_comp : ∀ {T T' T'' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing T'']
    [Algebra A T''] (f : T →ₐ[A] T') (g : T' →ₐ[A] T'') (x : RawDrinfeldPair T),
    map (g.comp f) x = map g (map f x)
  act_one : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : RawDrinfeldPair T),
    act (1 : WeierstrassCurve.VariableChange T) x = x
  act_mul : ∀ {T : Type u} [CommRing T] [Algebra A T] (C C' : WeierstrassCurve.VariableChange T)
    (x : RawDrinfeldPair T), act (C * C') x = act C (act C' x)
  map_act : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (C : WeierstrassCurve.VariableChange T) (x : RawDrinfeldPair T),
    map f (act C x) = act (C.map f.toRingHom) (map f x)
  isLevel_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (W : WeierstrassCurve T) (x : RawDrinfeldPair T),
    RawDrinfeldPair.IsLevel 𝒢 q W x → RawDrinfeldPair.IsLevel 𝒢 q (W.map f.toRingHom) (map f x)
  isLevel_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (W : WeierstrassCurve T) (x : RawDrinfeldPair T),
    RawDrinfeldPair.IsLevel 𝒢 q W x → RawDrinfeldPair.IsLevel 𝒢 q (C • W) (act C x)

def LevelTransport.IsSectionTransport {𝒢 : GroupLaws A} {q : ℕ} (𝒯 : LevelTransport A 𝒢 q) : Prop :=
  (∀ (T : Type u) [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T) (x : RawDrinfeldPair T),
    ∃ hc : (𝒯.act C x).curve = C • x.curve,
      ∀ (φ : projModelGradingCR x.curve →+*ᵍ projModelGradingCR (C • x.curve))
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • x.curve)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR x.curve)).map φ),
        IsVariableChangeHom x.curve C φ →
          (𝒯.act C x).P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ = x.P.1 ∧
          (𝒯.act C x).Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ = x.Q.1) ∧
  (∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : RawDrinfeldPair T),
    ∃ hc : (𝒯.map f x).curve = x.curve.map f.toRingHom,
      ∀ (φ : projModelGradingCR x.curve →+*ᵍ projModelGradingCR (x.curve.map f.toRingHom))
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (x.curve.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR x.curve)).map φ),
        IsCoefficientHom x.curve f.toRingHom φ →
          (𝒯.map f x).P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ =
            Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.P.1 ∧
          (𝒯.map f x).Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ =
            Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.Q.1)

def levelComponent (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (q : ℕ) (𝒯 : LevelTransport A 𝒢 q) :
    ModularCurve.LevelComponent A where
  obj T _ _ := RawDrinfeldPair T
  IsLevel W x := RawDrinfeldPair.IsLevel 𝒢 q W x
  map f x := 𝒯.map f x
  act C x := 𝒯.act C x
  map_id x := 𝒯.map_id x
  map_comp f g x := 𝒯.map_comp f g x
  act_one x := 𝒯.act_one x
  act_mul C C' x := 𝒯.act_mul C C' x
  map_act f C x := 𝒯.map_act f C x
  isLevel_map f W x h := 𝒯.isLevel_map f W x h
  isLevel_act C W x h := 𝒯.isLevel_act C W x h

def rigidData (A : Type u) [CommRing A] (ℓ N q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (h : Polynomial T), W.IsCyclicKernel N h → (C • W).IsCyclicKernel N (ModularCurve.kernelVariableChangeDeg C ((N - 1) / 2) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q) : ModularCurve.RigidWeierstrassData.{u} A :=
  ModularCurve.weierstrassLevelRigidData A ℓ N hℓ hN (levelComponent A 𝒢 q 𝒯)

end WeierstrassCurve.DrinfeldGlobal

end


