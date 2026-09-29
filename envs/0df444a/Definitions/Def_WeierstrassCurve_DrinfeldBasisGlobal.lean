-- Prove2me | Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
-- name    : WeierstrassCurve_DrinfeldBasisGlobal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/6cf00869-c4ce-5e89-9e1c-164d2dec2d99
-- title:
--   Drinfeld bases on projective Weierstrass models; level component
-- statement:
--   Fix a commutative ring $T$ and a Weierstrass curve $W$ in projective coordinates over $T$. Write $\mathrm{base}$ for $\operatorname{Spec} T$ and let a *section* be a morphism into the projective model $\mathrm{Proj}$-scheme `projModelCR W` splitting its structure morphism `projModelStrCR W`. Given a relative group law $G$ on that structure morphism (the project's notion: functorial group structures on $T'$-valued sections, with associativity, unit, inverse and base-change naturality as fields), `linComb G P Q a b` is $aP + bQ$ formed with the iterated group law, and `basisTuple G q P Q` is the family of $q^2$ morphisms $i \mapsto (i / q)P + (i \bmod q)Q$ indexed by `Fin (q * q)`; `basisTuple_over` records that each is a section. `basisDivisor` is the product, inside the ideal-sheaf lattice of the pullback of `projModelStrCR W` along the identity of the base, of the kernel ideal sheaves of the graphs of these $q^2$ sections — the effective divisor $\sum_{a,b \bmod q} [aP+bQ]$. `torsionIdeal` is the kernel ideal sheaf of the morphism from the $q$-torsion scheme $\ker([q])$ (the pullback of the multiplication-by-$q$ morphism against the unit section) into that same pullback. `IsDrinfeldBasis G q P Q` is the equality of these two ideal sheaves: the Drinfeld condition that the divisor of the $q^2$ linear combinations is exactly $W[q]$.
--
--   A `GroupLawFamily A` assigns such a group law to every $A$-algebra $T$ and every projective Weierstrass curve over it; `IsChordTangent` asks that for each of these there exist a bijection between $F$-valued sections and affine points of the base-changed curve, for all fields $F$ over the base ring, satisfying `IsPointsEval`, i.e. additive and Galois-equivariant. A `RawDrinfeldPair T` is a projective Weierstrass curve together with two sections, and `IsDrinfeldLevel 𝒢 q W x` says that the recorded curve is $W$ and that its two sections form a Drinfeld $q$-basis. A `DrinfeldTransport` packages base change along $A$-algebra maps and the action of Weierstrass variable changes on raw pairs, with the functoriality identities and the two statements that `IsDrinfeldLevel` is preserved under base change (replacing $W$ by $W.\mathrm{map}\,f$) and under variable change (replacing $W$ by $C \bullet W$) as fields. From such data, `drinfeldComponent` produces a [`ModularCurve.LevelComponent A`](../def/ModularCurve_WeierstrassLevelComponents.html#L15), and `fullLevelRigidData` combines it, via [`ModularCurve.weierstrassLevelRigidData`](../def/ModularCurve_WeierstrassLevelComponents.html#L197), with the cyclic-$N$-kernel and level-$\ell$ components to give rigid Weierstrass moduli data for curves with unit discriminant carrying all three level structures.
--
--   **Relation to Mathlib.** Mathlib has no relative group law on a projective Weierstrass model and no Drinfeld level structures; both are the project's own, built on Mathlib's `WeierstrassCurve.Projective`, the `Proj` construction and `Scheme.IdealSheafData`.
--
--   **Where it is used.** This supplies the full level-$q$ (Drinfeld basis) component of the project's moduli description of Weierstrass curves with level structure, alongside the $\Gamma_0(N)$ cyclic-kernel and level-$\ell$ point components, and feeds into the rigid Weierstrass data from which the relevant modular curves and their $q$-expansion theory are obtained.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_DrinfeldBasisGlobal.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

namespace WeierstrassCurve.DrinfeldGlobal

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)

abbrev base : Scheme.{u} := Spec (CommRingCat.of T)

abbrev Section : Type u := SchemeHomOver (𝟙 (base (T := T))) (projModelStrCR W)

variable {W}

def linComb (G : RelativeGroupLaw T (projModelStrCR W)) (P Q : Section W) (a b : ℕ) : Section W :=
  G.mul _ (G.nsmul _ a P) (G.nsmul _ b Q)

def basisTuple (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) (P Q : Section W) :
    Fin (q * q) → (base (T := T) ⟶ projModelCR W) :=
  fun i => (linComb G P Q (i.val / q) (i.val % q)).1

theorem basisTuple_over (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) (P Q : Section W) (i : Fin (q * q)) :
    basisTuple G q P Q i ≫ projModelStrCR W = 𝟙 _ :=
  (linComb G P Q (i.val / q) (i.val % q)).2

def basisDivisor (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) (P Q : Section W) :
    (pullback (projModelStrCR W) (𝟙 (base (T := T)))).IdealSheafData :=
  prodKerGraph (projModelStrCR W) (basisTuple G q P Q) (basisTuple_over G q P Q)

def toPullbackId : projModelCR W ⟶ pullback (projModelStrCR W) (𝟙 (base (T := T))) :=
  pullback.lift (𝟙 _) (projModelStrCR W) (by simp)

def torsionIdeal (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) :
    (pullback (projModelStrCR W) (𝟙 (base (T := T)))).IdealSheafData :=
  (pullback.fst (G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1 ≫ toPullbackId).ker

def IsDrinfeldBasis (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) (P Q : Section W) : Prop :=
  basisDivisor G q P Q = torsionIdeal G q

abbrev GroupLawFamily (A : Type u) [CommRing A] : Type (u + 1) :=
  ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T), RelativeGroupLaw T (projModelStrCR W)

def GroupLawFamily.IsChordTangent {A : Type u} [CommRing A] (𝒢 : GroupLawFamily A) : Prop :=
  ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T), ∃ ev, IsPointsEval W (𝒢 T W) ev

structure RawDrinfeldPair (T : Type u) [CommRing T] where

  curve : WeierstrassCurve.Projective T

  P : Section curve

  Q : Section curve

def IsDrinfeldLevel {A : Type u} [CommRing A] (𝒢 : GroupLawFamily A) (q : ℕ)
    {T : Type u} [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (x : RawDrinfeldPair T) : Prop :=
  x.curve = W ∧ IsDrinfeldBasis (𝒢 T x.curve) q x.P x.Q

structure DrinfeldTransport (A : Type u) [CommRing A] (𝒢 : GroupLawFamily A) (q : ℕ) where

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
    IsDrinfeldLevel 𝒢 q W x → IsDrinfeldLevel 𝒢 q (W.map f.toRingHom) (map f x)
  isLevel_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (W : WeierstrassCurve T) (x : RawDrinfeldPair T),
    IsDrinfeldLevel 𝒢 q W x → IsDrinfeldLevel 𝒢 q (C • W) (act C x)

def drinfeldComponent (A : Type u) [CommRing A] (𝒢 : GroupLawFamily A) (q : ℕ) (𝒯 : DrinfeldTransport A 𝒢 q) :
    ModularCurve.LevelComponent A where
  obj T _ _ := RawDrinfeldPair T
  IsLevel W x := IsDrinfeldLevel 𝒢 q W x
  map f x := 𝒯.map f x
  act C x := 𝒯.act C x
  map_id x := 𝒯.map_id x
  map_comp f g x := 𝒯.map_comp f g x
  act_one x := 𝒯.act_one x
  act_mul C C' x := 𝒯.act_mul C C' x
  map_act f C x := 𝒯.map_act f C x
  isLevel_map f W x h := 𝒯.isLevel_map f W x h
  isLevel_act C W x h := 𝒯.isLevel_act C W x h

noncomputable def fullLevelRigidData (A : Type u) [CommRing A] (ℓ N q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (h : Polynomial T), W.IsCyclicKernel N h → (C • W).IsCyclicKernel N (ModularCurve.kernelVariableChangeDeg C ((N - 1) / 2) h))
    (𝒢 : GroupLawFamily A) (𝒯 : DrinfeldTransport A 𝒢 q) : ModularCurve.RigidWeierstrassData.{u} A :=
  ModularCurve.weierstrassLevelRigidData A ℓ N hℓ hN (drinfeldComponent A 𝒢 q 𝒯)

end WeierstrassCurve.DrinfeldGlobal

end


