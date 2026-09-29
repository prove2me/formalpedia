-- Prove2me | Definitions.Def_MvPolynomial_CrossingResolutionScheme
-- name    : MvPolynomial_CrossingResolutionScheme
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/5267cb8a-de2f-5296-9e08-e9e05ab450ef
-- title:
--   Gluing charts into a resolution of a crossing singularity
-- statement:
--   Throughout, $W$ is a commutative ring and $t \in W$; write $C = \mathtt{CrossingQuotient}\ W\ t = W[X_0,X_1]/(X_0X_1-t)$, with $x = U\,t$ and $y = V\,t$ the images of $X_0, X_1$, so $xy$ is the image of $t$. The module first builds the affine rings of the chart atlas: `OverlapRing t` is the localisation $C[1/y]$ and `TorusRing t` is its further localisation away from the image of $x$, which is identified (via $xy = t$) as the localisation of $C$ away from $t$. For $a,b$ in the torus ring with $ab = 1$, `twist` is the $W$-algebra endomorphism of the torus ring determined by $x \mapsto xa$, $y \mapsto yb$ (fixing $t$ and its inverse); `twistEquiv t i` is the resulting automorphism with $a = t^{-i}$, $b = t^{i}$, and `torusChart t i`, `torusOverlap t i` are its composites with the localisation maps from $C$ and from $C[1/y]$. Thus $\mathtt{torusChart}$ sends $U \mapsto x t^{-i}$, $V \mapsto y t^{i}$, and the cocycle identity `torusOverlap_comp_transitionUp` holds. Secondly, `transitionEquiv t` is the ring isomorphism $C[1/x] \cong C[1/y]$ extending the transition $x \mapsto y^{-1}$, $y \mapsto ty$, whence $\operatorname{Spec}$ of the transition is an open immersion. Thirdly, `GlueIndex e` is a preorder with objects: $e$ charts, the overlaps indexed by $i$ with $i+1 < e$ (each below the charts $i$ and $i+1$), and, when $e > 0$, a torus below everything; `glueDiagram t e` is the functor to schemes sending these to $\operatorname{Spec} C$, $\operatorname{Spec} C[1/y]$ and $\operatorname{Spec}$ of the torus ring, with the two inclusions of an overlap into its charts and the twisted torus inclusions; every map in the diagram is an open immersion, and the diagram is locally directed. `Resolution t e` is its colimit, with open immersions `ι`, `ιOverlap`, `ιTorus`, an affine open cover by the charts, and an extensionality principle along the charts. Finally the maps $\operatorname{Spec} C \to \operatorname{Spec} W[u,v]/(uv-t^e)$ given by $u \mapsto t^i x$, $v \mapsto t^{e-1-i} y$ form a cocone, yielding `toCrossing` and its composite `toSpec` to $\operatorname{Spec} W$.
--
--   **Relation to Mathlib.** The gluing is performed through Mathlib's colimits of locally directed diagrams of schemes with open-immersion transition maps (`Scheme.IsLocallyDirected`) rather than an explicit glue datum; the index preorder `GlueIndex` and all the chart and twist algebra maps are the project's own.
--
--   **Where it is used.** The rings $W[u,v]/(uv-t^e)$ model the local structure of an arithmetic surface at a node of thickness $e$ in a semistable fibre, and `Resolution` provides the chart-by-chart resolution of such a singularity, with the chain of charts replacing the node by a chain of lines in the special fibre. It serves as the local input for regular models of semistable curves used in the analysis of modular curves and their Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvPolynomial_CrossingResolutionScheme.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MvPolynomial

namespace CrossingQuotient

variable {W : Type u} [CommRing W] (t : W)

abbrev OverlapRing : Type u := Localization.Away (V t)

abbrev TorusRing : Type u :=
  Localization.Away (algebraMap (CrossingQuotient W t) (OverlapRing t) (U t))

instance isLocalization_away_torusRing :
    IsLocalization.Away (algebraMap W (CrossingQuotient W t) t) (TorusRing t) := by
  rw [← U_mul_V]; infer_instance

abbrev xT : TorusRing t := algebraMap (CrossingQuotient W t) (TorusRing t) (U t)

abbrev yT : TorusRing t := algebraMap (CrossingQuotient W t) (TorusRing t) (V t)

abbrev tT : TorusRing t := algebraMap W (TorusRing t) t

abbrev tinv : TorusRing t :=
  IsLocalization.Away.invSelf (S := TorusRing t) (algebraMap W (CrossingQuotient W t) t)

theorem xT_mul_yT : xT t * yT t = tT t := by
  rw [← map_mul, U_mul_V, ← IsScalarTower.algebraMap_apply]

theorem tT_mul_tinv : tT t * tinv t = 1 := by
  change algebraMap W (TorusRing t) t * _ = 1
  rw [IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (TorusRing t) t]
  exact IsLocalization.Away.mul_invSelf _

theorem tinv_mul_tT : tinv t * tT t = 1 := by rw [mul_comm, tT_mul_tinv]

theorem isUnit_tT : IsUnit (tT t) := IsUnit.of_mul_eq_one _ (tT_mul_tinv t)

theorem tinv_pow_mul_tT_pow (i : ℕ) : tinv t ^ i * tT t ^ i = 1 := by
  rw [← mul_pow, tinv_mul_tT, one_pow]

theorem tT_pow_mul_tinv_pow (i : ℕ) : tT t ^ i * tinv t ^ i = 1 := by
  rw [← mul_pow, tT_mul_tinv, one_pow]

def twist₀ (a b : TorusRing t) (hab : a * b = 1) : CrossingQuotient W t →ₐ[W] TorusRing t :=
  lift t (xT t * a) (yT t * b) (by rw [mul_mul_mul_comm, xT_mul_yT, hab, mul_one])

theorem twist₀_U (a b : TorusRing t) (hab : a * b = 1) : twist₀ t a b hab (U t) = xT t * a :=
  lift_U _ _ _ _

theorem twist₀_V (a b : TorusRing t) (hab : a * b = 1) : twist₀ t a b hab (V t) = yT t * b :=
  lift_V _ _ _ _

theorem isUnit_twist₀_apply (a b : TorusRing t) (hab : a * b = 1) :
    IsUnit ((twist₀ t a b hab).toRingHom (algebraMap W (CrossingQuotient W t) t)) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]; exact isUnit_tT t

def twistRingHom (a b : TorusRing t) (hab : a * b = 1) : TorusRing t →+* TorusRing t :=
  IsLocalization.Away.lift (S := TorusRing t) (algebraMap W (CrossingQuotient W t) t)
    (g := (twist₀ t a b hab).toRingHom) (isUnit_twist₀_apply t a b hab)

theorem twistRingHom_algebraMap (a b : TorusRing t) (hab : a * b = 1) (c : CrossingQuotient W t) :
    twistRingHom t a b hab (algebraMap _ _ c) = twist₀ t a b hab c :=
  IsLocalization.Away.lift_eq (S := TorusRing t) _ (isUnit_twist₀_apply t a b hab) c

def twist (a b : TorusRing t) (hab : a * b = 1) : TorusRing t →ₐ[W] TorusRing t :=
  { twistRingHom t a b hab with
    commutes' := fun w => by
      change twistRingHom t a b hab (algebraMap W (TorusRing t) w) = _
      rw [IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (TorusRing t) w,
        twistRingHom_algebraMap]
      exact (twist₀ t a b hab).commutes w }

variable {t}

theorem twist_algebraMap (a b : TorusRing t) (hab : a * b = 1) (c : CrossingQuotient W t) :
    twist t a b hab (algebraMap _ _ c) = twist₀ t a b hab c :=
  twistRingHom_algebraMap t a b hab c

theorem twist_xT (a b : TorusRing t) (hab : a * b = 1) : twist t a b hab (xT t) = xT t * a := by
  rw [twist_algebraMap, twist₀_U]

theorem twist_yT (a b : TorusRing t) (hab : a * b = 1) : twist t a b hab (yT t) = yT t * b := by
  rw [twist_algebraMap, twist₀_V]

theorem twist_tT (a b : TorusRing t) (hab : a * b = 1) : twist t a b hab (tT t) = tT t :=
  AlgHom.commutes _ _

theorem twist_tinv (a b : TorusRing t) (hab : a * b = 1) : twist t a b hab (tinv t) = tinv t := by
  have h1 : twist t a b hab (tinv t) * tT t = 1 := by
    rw [← twist_tT a b hab, ← map_mul, tinv_mul_tT, map_one]
  calc twist t a b hab (tinv t) = twist t a b hab (tinv t) * (tT t * tinv t) := by
        rw [tT_mul_tinv, mul_one]
    _ = tinv t := by rw [← mul_assoc, h1, one_mul]

theorem twist_comp_algebraMap (a b : TorusRing t) (hab : a * b = 1) :
    (twist t a b hab).comp (IsScalarTower.toAlgHom W (CrossingQuotient W t) (TorusRing t)) =
      twist₀ t a b hab :=
  AlgHom.ext fun c => twist_algebraMap a b hab c

theorem algHom_ext_torus {A : Type*} [CommRing A] [Algebra W A] {f g : TorusRing t →ₐ[W] A}
    (hx : f (xT t) = g (xT t)) (hy : f (yT t) = g (yT t)) : f = g := by
  have key : f.comp (IsScalarTower.toAlgHom W (CrossingQuotient W t) (TorusRing t)) =
      g.comp (IsScalarTower.toAlgHom W (CrossingQuotient W t) (TorusRing t)) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j
    · exact hx
    · exact hy
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap W (CrossingQuotient W t) t))
    (S := TorusRing t)
  exact RingHom.ext fun c => congrArg (fun φ : CrossingQuotient W t →ₐ[W] A => φ c) key

theorem twist_comp_twist (a b : TorusRing t) (hab : a * b = 1)
    (ha : twist t a b hab a = a) (hb : twist t a b hab b = b) :
    (twist t a b hab).comp (twist t b a ((mul_comm b a).trans hab)) = AlgHom.id W (TorusRing t) := by
  apply algHom_ext_torus
  · rw [AlgHom.comp_apply, twist_xT, map_mul, twist_xT, hb, mul_assoc, hab, mul_one, AlgHom.id_apply]
  · rw [AlgHom.comp_apply, twist_yT, map_mul, twist_yT, ha, mul_assoc, mul_comm b a, hab, mul_one,
      AlgHom.id_apply]

theorem twist_tinv_pow (a b : TorusRing t) (hab : a * b = 1) (i : ℕ) :
    twist t a b hab (tinv t ^ i) = tinv t ^ i := by rw [map_pow, twist_tinv]

theorem twist_tT_pow (a b : TorusRing t) (hab : a * b = 1) (i : ℕ) :
    twist t a b hab (tT t ^ i) = tT t ^ i := by rw [map_pow, twist_tT]

variable (t)

def twistEquiv (i : ℕ) : TorusRing t ≃ₐ[W] TorusRing t :=
  AlgEquiv.ofAlgHom (twist t (tinv t ^ i) (tT t ^ i) (tinv_pow_mul_tT_pow t i))
    (twist t (tT t ^ i) (tinv t ^ i) (tT_pow_mul_tinv_pow t i))
    (twist_comp_twist _ _ _ (twist_tinv_pow _ _ _ i) (twist_tT_pow _ _ _ i))
    (twist_comp_twist _ _ _ (twist_tT_pow _ _ _ i) (twist_tinv_pow _ _ _ i))

theorem twistEquiv_xT (i : ℕ) : twistEquiv t i (xT t) = xT t * tinv t ^ i := twist_xT _ _ _

theorem twistEquiv_yT (i : ℕ) : twistEquiv t i (yT t) = yT t * tT t ^ i := twist_yT _ _ _

def torusChart (i : ℕ) : CrossingQuotient W t →ₐ[W] TorusRing t :=
  (twistEquiv t i).toAlgHom.comp (IsScalarTower.toAlgHom W (CrossingQuotient W t) (TorusRing t))

def torusOverlap (i : ℕ) : OverlapRing t →ₐ[W] TorusRing t :=
  (twistEquiv t i).toAlgHom.comp (IsScalarTower.toAlgHom W (OverlapRing t) (TorusRing t))

theorem torusChart_U (i : ℕ) : torusChart t i (U t) = xT t * tinv t ^ i := twistEquiv_xT t i

theorem torusChart_V (i : ℕ) : torusChart t i (V t) = yT t * tT t ^ i := twistEquiv_yT t i

theorem torusOverlap_algebraMap (i : ℕ) (c : CrossingQuotient W t) :
    torusOverlap t i (algebraMap _ _ c) = torusChart t i c := by
  change twistEquiv t i (algebraMap (OverlapRing t) (TorusRing t) (algebraMap _ _ c)) =
    twistEquiv t i (algebraMap _ _ c)
  rw [← IsScalarTower.algebraMap_apply]

theorem torusOverlap_comp_toAlgHom (i : ℕ) :
    (torusOverlap t i).comp (IsScalarTower.toAlgHom W (CrossingQuotient W t) (OverlapRing t)) =
      torusChart t i :=
  AlgHom.ext (torusOverlap_algebraMap t i)

theorem algHom_ext_chart {s : W} {A : Type*} [CommRing A] [Algebra W A]
    {f g : CrossingQuotient W s →ₐ[W] A}
    (hx : f (U s) = g (U s)) (hy : f (V s) = g (V s)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j
  · exact hx
  · exact hy

theorem eq_of_mul_eq_one_of_mul_eq_one {A : Type*} [CommRing A] {a b c : A}
    (hb : a * b = 1) (hc : c * a = 1) : b = c := by
  calc b = (c * a) * b := by rw [hc, one_mul]
    _ = c * (a * b) := by ring
    _ = c := by rw [hb, mul_one]

theorem torusOverlap_comp_transitionUp (i : ℕ) :
    (torusOverlap t i).comp (transitionUp t) = torusChart t (i + 1) := by
  apply algHom_ext_chart
  · rw [AlgHom.comp_apply, transitionUp_U, torusChart_U]

    have h1 : torusOverlap t i (algebraMap _ _ (V t)) *
        torusOverlap t i (IsLocalization.Away.invSelf (V t)) = 1 := by
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    rw [torusOverlap_algebraMap, torusChart_V] at h1
    apply eq_of_mul_eq_one_of_mul_eq_one h1
    have h2 := xT_mul_yT t
    have h3 := tinv_mul_tT t
    have h4 := tinv_pow_mul_tT_pow t i
    linear_combination (tinv t ^ (i + 1) * tT t ^ i) * h2 + (tinv t * tT t) * h4 + h3
  · rw [AlgHom.comp_apply, transitionUp_V, map_mul, AlgHom.commutes, torusOverlap_algebraMap,
      torusChart_V, torusChart_V, pow_succ]
    change tT t * (yT t * tT t ^ i) = yT t * (tT t ^ i * tT t)
    ring

section transition

def transitionUpAway : Localization.Away (U t) →+* OverlapRing t :=
  IsLocalization.Away.lift (S := Localization.Away (U t)) (U t) (g := (transitionUp t).toRingHom)
    (by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, transitionUp_U]
      exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (V t)))

def transitionDownAway : OverlapRing t →+* Localization.Away (U t) :=
  IsLocalization.Away.lift (S := OverlapRing t) (V t) (g := (transitionDown t).toRingHom)
    (by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, transitionDown_V]
      exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (U t)))

theorem transitionUpAway_algebraMap (c : CrossingQuotient W t) :
    transitionUpAway t (algebraMap _ _ c) = transitionUp t c :=
  IsLocalization.Away.lift_eq (S := Localization.Away (U t)) (U t) _ c

theorem transitionDownAway_algebraMap (c : CrossingQuotient W t) :
    transitionDownAway t (algebraMap _ _ c) = transitionDown t c :=
  IsLocalization.Away.lift_eq (S := OverlapRing t) (V t) _ c

theorem transitionUpAway_comp_algebraMap :
    (transitionUpAway t).comp (algebraMap (CrossingQuotient W t) (Localization.Away (U t))) =
      (transitionUp t).toRingHom :=
  IsLocalization.Away.lift_comp (S := Localization.Away (U t)) (U t) _

theorem mk_C_eq_algebraMap (s w : W) : mk s (C w) = algebraMap W (CrossingQuotient W s) w := by
  change mk s (algebraMap W (MvPolynomial (Fin 2) W) w) = _
  exact AlgHom.commutes _ w

theorem transitionDownAway_comp_transitionUpAway :
    (transitionDownAway t).comp (transitionUpAway t) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (U t))
  rw [RingHom.comp_assoc, transitionUpAway_comp_algebraMap, RingHom.id_comp]
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    change transitionDownAway t (transitionUp t (mk t (C w))) = algebraMap _ _ (mk t (C w))
    rw [mk_C_eq_algebraMap, AlgHom.commutes, IsScalarTower.algebraMap_apply W (CrossingQuotient W t)
      (OverlapRing t), transitionDownAway_algebraMap, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  · intro j
    fin_cases j
    · change transitionDownAway t (transitionUp t (U t)) = algebraMap _ _ (U t)
      rw [transitionUp_U]
      have h1 : transitionDownAway t (algebraMap _ _ (V t)) *
          transitionDownAway t (IsLocalization.Away.invSelf (V t)) = 1 := by
        rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
      rw [transitionDownAway_algebraMap, transitionDown_V] at h1
      exact eq_of_mul_eq_one_of_mul_eq_one h1 (IsLocalization.Away.mul_invSelf (U t))
    · change transitionDownAway t (transitionUp t (V t)) = algebraMap _ _ (V t)
      rw [transitionUp_V, map_mul, IsScalarTower.algebraMap_apply W (CrossingQuotient W t)
        (OverlapRing t), transitionDownAway_algebraMap, transitionDownAway_algebraMap,
        AlgHom.commutes, transitionDown_V, IsScalarTower.algebraMap_apply W (CrossingQuotient W t)
        (Localization.Away (U t)), ← U_mul_V, map_mul, mul_comm (algebraMap _ _ (U t)), mul_assoc,
        IsLocalization.Away.mul_invSelf, mul_one]

theorem transitionUpAway_comp_transitionDownAway :
    (transitionUpAway t).comp (transitionDownAway t) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (V t))
  rw [RingHom.comp_assoc, transitionDownAway, IsLocalization.Away.lift_comp, RingHom.id_comp]
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    change transitionUpAway t (transitionDown t (mk t (C w))) = algebraMap _ _ (mk t (C w))
    rw [mk_C_eq_algebraMap, AlgHom.commutes, IsScalarTower.algebraMap_apply W (CrossingQuotient W t)
      (Localization.Away (U t)), transitionUpAway_algebraMap, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  · intro j
    fin_cases j
    · change transitionUpAway t (transitionDown t (U t)) = algebraMap _ _ (U t)
      rw [transitionDown_U, map_mul, IsScalarTower.algebraMap_apply W (CrossingQuotient W t)
        (Localization.Away (U t)), transitionUpAway_algebraMap, transitionUpAway_algebraMap,
        AlgHom.commutes, transitionUp_U, IsScalarTower.algebraMap_apply W (CrossingQuotient W t)
        (OverlapRing t), ← U_mul_V, map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
    · change transitionUpAway t (transitionDown t (V t)) = algebraMap _ _ (V t)
      rw [transitionDown_V]
      have h1 : transitionUpAway t (algebraMap _ _ (U t)) *
          transitionUpAway t (IsLocalization.Away.invSelf (U t)) = 1 := by
        rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
      rw [transitionUpAway_algebraMap, transitionUp_U] at h1
      exact eq_of_mul_eq_one_of_mul_eq_one h1 (IsLocalization.Away.mul_invSelf (V t))

def transitionEquiv : Localization.Away (U t) ≃+* OverlapRing t :=
  RingEquiv.ofRingHom (transitionUpAway t) (transitionDownAway t)
    (transitionUpAway_comp_transitionDownAway t) (transitionDownAway_comp_transitionUpAway t)

theorem toRingHom_transitionEquiv_comp :
    (transitionEquiv t).toRingHom.comp
        (algebraMap (CrossingQuotient W t) (Localization.Away (U t))) =
      (transitionUp t).toRingHom :=
  transitionUpAway_comp_algebraMap t

end transition

section spectra

abbrev crossingScheme (s : W) : Scheme.{u} := Spec (CommRingCat.of (CrossingQuotient W s))

abbrev chartScheme : Scheme.{u} := crossingScheme t

abbrev overlapScheme : Scheme.{u} := Spec (CommRingCat.of (OverlapRing t))

abbrev torusScheme : Scheme.{u} := Spec (CommRingCat.of (TorusRing t))

abbrev overlapToChartLeft : overlapScheme t ⟶ chartScheme t :=
  Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient W t) (OverlapRing t)))

abbrev overlapToChartRight : overlapScheme t ⟶ chartScheme t :=
  Spec.map (CommRingCat.ofHom (transitionUp t).toRingHom)

abbrev torusToChart (i : ℕ) : torusScheme t ⟶ chartScheme t :=
  Spec.map (CommRingCat.ofHom (torusChart t i).toRingHom)

abbrev torusToOverlap (i : ℕ) : torusScheme t ⟶ overlapScheme t :=
  Spec.map (CommRingCat.ofHom (torusOverlap t i).toRingHom)

instance isOpenImmersion_overlapToChartRight : IsOpenImmersion (overlapToChartRight t) := by
  have H : IsIso (CommRingCat.ofHom (transitionEquiv t).toRingHom) :=
    inferInstanceAs (IsIso (transitionEquiv t).toCommRingCatIso.hom)
  rw [overlapToChartRight, ← toRingHom_transitionEquiv_comp, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

theorem isIso_ofHom_twistEquiv (i : ℕ) :
    IsIso (CommRingCat.ofHom (twistEquiv t i).toAlgHom.toRingHom) :=
  inferInstanceAs (IsIso (twistEquiv t i).toRingEquiv.toCommRingCatIso.hom)

theorem torusToChart_eq (i : ℕ) : torusToChart t i =
    Spec.map (CommRingCat.ofHom (twistEquiv t i).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient W t) (TorusRing t))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem torusToOverlap_eq (i : ℕ) : torusToOverlap t i =
    Spec.map (CommRingCat.ofHom (twistEquiv t i).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (OverlapRing t) (TorusRing t))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

instance isOpenImmersion_torusToChart (i : ℕ) : IsOpenImmersion (torusToChart t i) := by
  have := isIso_ofHom_twistEquiv t i
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient W t) (TorusRing t)))) :=
    IsOpenImmersion.of_isLocalization (algebraMap W (CrossingQuotient W t) t)
  rw [torusToChart_eq]
  infer_instance

instance isOpenImmersion_torusToOverlap (i : ℕ) : IsOpenImmersion (torusToOverlap t i) := by
  have := isIso_ofHom_twistEquiv t i
  rw [torusToOverlap_eq]
  infer_instance

theorem torusToOverlap_overlapToChartLeft (i : ℕ) :
    torusToOverlap t i ≫ overlapToChartLeft t = torusToChart t i := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
    (congrArg AlgHom.toRingHom (torusOverlap_comp_toAlgHom t i))

theorem torusToOverlap_overlapToChartRight (i : ℕ) :
    torusToOverlap t i ≫ overlapToChartRight t = torusToChart t (i + 1) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
    (congrArg AlgHom.toRingHom (torusOverlap_comp_transitionUp t i))

theorem V_notMem_of_mem_range_overlapToChartLeft {P : chartScheme t}
    (hP : P ∈ Set.range (overlapToChartLeft t)) : V t ∉ P.asIdeal := by
  obtain ⟨Q, rfl⟩ := hP
  intro h
  have hu : IsUnit (algebraMap (CrossingQuotient W t) (OverlapRing t) (V t)) :=
    IsLocalization.Away.algebraMap_isUnit (V t)
  exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

theorem U_notMem_of_mem_range_overlapToChartRight {P : chartScheme t}
    (hP : P ∈ Set.range (overlapToChartRight t)) : U t ∉ P.asIdeal := by
  obtain ⟨Q, rfl⟩ := hP
  intro h
  have hu : IsUnit ((transitionUp t).toRingHom (U t)) := by
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, transitionUp_U]
    exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (V t))
  exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

theorem mem_range_torusToChart {P : chartScheme t} (hU : U t ∉ P.asIdeal) (hV : V t ∉ P.asIdeal)
    (i : ℕ) : P ∈ Set.range (torusToChart t i) := by
  have := isIso_ofHom_twistEquiv t i
  rw [torusToChart_eq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (Scheme.Hom.surjective _), Set.image_univ]
  change P ∈ Set.range (PrimeSpectrum.comap (algebraMap (CrossingQuotient W t) (TorusRing t)))
  rw [PrimeSpectrum.localization_away_comap_range (TorusRing t)
    (algebraMap W (CrossingQuotient W t) t)]
  change algebraMap W (CrossingQuotient W t) t ∉ P.asIdeal
  rw [← U_mul_V]
  exact fun h => (P.isPrime.mem_or_mem h).elim hU hV

end spectra

inductive GlueIndex (e : ℕ) : Type
  | chart (i : Fin e) : GlueIndex e
  | overlap (i : Fin e) (h : (i : ℕ) + 1 < e) : GlueIndex e
  | torus (h : 0 < e) : GlueIndex e

namespace GlueIndex

variable {e : ℕ}

protected def le : GlueIndex e → GlueIndex e → Prop
  | torus _, _ => True
  | overlap i _, overlap j _ => i = j
  | overlap i _, chart j => j = i ∨ (j : ℕ) = i + 1
  | chart i, chart j => i = j
  | overlap _ _, torus _ => False
  | chart _, torus _ => False
  | chart _, overlap _ _ => False

instance : LE (GlueIndex e) := ⟨GlueIndex.le⟩

@[simp] theorem torus_le (h : 0 < e) (b : GlueIndex e) : torus h ≤ b ↔ True := Iff.rfl
@[simp] theorem overlap_le_overlap (i j : Fin e) (h : (i : ℕ) + 1 < e) (h' : (j : ℕ) + 1 < e) :
    overlap i h ≤ overlap j h' ↔ i = j := Iff.rfl
@[simp] theorem overlap_le_chart (i j : Fin e) (h : (i : ℕ) + 1 < e) :
    overlap i h ≤ chart j ↔ j = i ∨ (j : ℕ) = i + 1 := Iff.rfl
@[simp] theorem chart_le_chart (i j : Fin e) : chart i ≤ chart j ↔ i = j := Iff.rfl
@[simp] theorem overlap_le_torus (i : Fin e) (h : (i : ℕ) + 1 < e) (h' : 0 < e) :
    overlap i h ≤ torus h' ↔ False := Iff.rfl
@[simp] theorem chart_le_torus (i : Fin e) (h' : 0 < e) : chart i ≤ torus h' ↔ False := Iff.rfl
@[simp] theorem chart_le_overlap (i j : Fin e) (h : (j : ℕ) + 1 < e) :
    chart i ≤ overlap j h ↔ False := Iff.rfl

instance : Preorder (GlueIndex e) where
  le_refl a := by cases a <;> simp
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;>
      simp only [torus_le, overlap_le_overlap, overlap_le_chart, chart_le_chart, overlap_le_torus,
        chart_le_torus, chart_le_overlap] at hab hbc ⊢ <;> subst_vars <;> simp_all

end GlueIndex

open GlueIndex

section diagram

variable (e : ℕ)

def glueObj : GlueIndex e → Scheme.{u}
  | .chart _ => chartScheme t
  | .overlap _ _ => overlapScheme t
  | .torus _ => torusScheme t

def glueMap : ∀ a b : GlueIndex e, a ≤ b → (glueObj t e a ⟶ glueObj t e b)
  | .torus _, .torus _, _ => 𝟙 _
  | .torus _, .overlap i _, _ => torusToOverlap t i
  | .torus _, .chart j, _ => torusToChart t j
  | .overlap _ _, .overlap _ _, _ => 𝟙 _
  | .overlap i _, .chart j, _ =>
      if (j : ℕ) = i then overlapToChartLeft t else overlapToChartRight t
  | .chart _, .chart _, _ => 𝟙 _
  | .overlap _ _, .torus _, h => False.elim h
  | .chart _, .torus _, h => False.elim h
  | .chart _, .overlap _ _, h => False.elim h

@[simp] theorem glueMap_torus_torus (h h' : 0 < e) (hle) :
    glueMap t e (torus h) (torus h') hle = 𝟙 _ := rfl
@[simp] theorem glueMap_torus_overlap (h : 0 < e) (i : Fin e) (hi) (hle) :
    glueMap t e (torus h) (overlap i hi) hle = torusToOverlap t i := rfl
@[simp] theorem glueMap_torus_chart (h : 0 < e) (j : Fin e) (hle) :
    glueMap t e (torus h) (chart j) hle = torusToChart t j := rfl
@[simp] theorem glueMap_overlap_overlap (i j : Fin e) (hi hj) (hle) :
    glueMap t e (overlap i hi) (overlap j hj) hle = 𝟙 (overlapScheme t) := rfl
@[simp] theorem glueMap_chart_chart (i j : Fin e) (hle) :
    glueMap t e (chart i) (chart j) hle = 𝟙 (chartScheme t) := rfl
theorem glueMap_overlap_chart_self (i : Fin e) (hi) (hle) :
    glueMap t e (overlap i hi) (chart i) hle = overlapToChartLeft t := if_pos rfl
theorem glueMap_overlap_chart_succ (i : Fin e) (hi) (hle) :
    glueMap t e (overlap i hi) (chart ⟨(i : ℕ) + 1, hi⟩) hle = overlapToChartRight t :=
  if_neg (Nat.succ_ne_self _)
theorem glueMap_overlap_chart_of_eq {i j : Fin e} (hi) (hle) (h : (j : ℕ) = i) :
    glueMap t e (overlap i hi) (chart j) hle = overlapToChartLeft t := if_pos h
theorem glueMap_overlap_chart_of_ne {i j : Fin e} (hi) (hle) (h : (j : ℕ) ≠ i) :
    glueMap t e (overlap i hi) (chart j) hle = overlapToChartRight t := if_neg h

theorem glueMap_id (a : GlueIndex e) : glueMap t e a a le_rfl = 𝟙 _ := by
  cases a <;> rfl

theorem glueMap_comp (a b c : GlueIndex e) (hab : a ≤ b) (hbc : b ≤ c) :
    glueMap t e a c (hab.trans hbc) = glueMap t e a b hab ≫ glueMap t e b c hbc := by
  cases a <;> cases b <;> cases c <;>
    simp only [torus_le, overlap_le_overlap, overlap_le_chart, chart_le_chart, overlap_le_torus,
      chart_le_torus, chart_le_overlap] at hab hbc
  all_goals (try subst_vars)
  case torus.overlap.chart =>
    rename_i he i hi hab0 j hbc0
    rcases hbc with rfl | hj
    · rw [glueMap_torus_chart, glueMap_torus_overlap, glueMap_overlap_chart_self]
      exact (torusToOverlap_overlapToChartLeft t j).symm
    · rw [glueMap_torus_chart, glueMap_torus_overlap, glueMap_overlap_chart_of_ne t e hi hbc0
        (by omega), hj]
      exact (torusToOverlap_overlapToChartRight t i).symm
  all_goals rfl

def glueDiagram : GlueIndex e ⥤ Scheme.{u} where
  obj := glueObj t e
  map f := glueMap t e _ _ f.le
  map_id a := glueMap_id t e a
  map_comp f g := glueMap_comp t e _ _ _ f.le g.le

@[simp] theorem glueDiagram_obj (a : GlueIndex e) : (glueDiagram t e).obj a = glueObj t e a := rfl

theorem glueDiagram_map {a b : GlueIndex e} (f : a ⟶ b) :
    (glueDiagram t e).map f = glueMap t e a b f.le := rfl

instance isOpenImmersion_glueMap (a b : GlueIndex e) (hab : a ≤ b) :
    IsOpenImmersion (glueMap t e a b hab) := by
  cases a <;> cases b <;>
    simp only [torus_le, overlap_le_overlap, overlap_le_chart, chart_le_chart, overlap_le_torus,
      chart_le_torus, chart_le_overlap] at hab
  case overlap.chart =>
    rename_i i hi j hab0
    by_cases h : (j : ℕ) = i
    · rw [glueMap_overlap_chart_of_eq t e hi _ h]
      exact inferInstanceAs (IsOpenImmersion (overlapToChartLeft t))
    · rw [glueMap_overlap_chart_of_ne t e hi _ h]
      exact inferInstanceAs (IsOpenImmersion (overlapToChartRight t))
  case torus.torus => exact inferInstanceAs (IsOpenImmersion (𝟙 (torusScheme t)))
  case torus.overlap h i hi hab0 => exact inferInstanceAs (IsOpenImmersion (torusToOverlap t i))
  case torus.chart h j hab0 => exact inferInstanceAs (IsOpenImmersion (torusToChart t j))
  case overlap.overlap => exact inferInstanceAs (IsOpenImmersion (𝟙 (overlapScheme t)))
  case chart.chart => exact inferInstanceAs (IsOpenImmersion (𝟙 (chartScheme t)))

instance isOpenImmersion_glueDiagram_map {a b : GlueIndex e} (f : a ⟶ b) :
    IsOpenImmersion ((glueDiagram t e).map f) :=
  isOpenImmersion_glueMap t e a b f.le

end diagram

section locallyDirected

variable (e : ℕ)

theorem exists_of_mem_range_map {J : Type*} [Category J] [Quiver.IsThin J] (F : J ⥤ Scheme.{u})
    [∀ {i j : J} (f : i ⟶ j), IsOpenImmersion (F.map f)]
    {i j k : J} (fi : i ⟶ k) (fj : j ⟶ k) (xi : F.obj i) (xj : F.obj j)
    (h : F.map fi xi = F.map fj xj) (l : J) (fli : l ⟶ i) (flj : l ⟶ j)
    (hz : F.map fi xi ∈ Set.range (F.map (fli ≫ fi))) :
    ∃ (l : J) (fli : l ⟶ i) (flj : l ⟶ j) (x : F.obj l), F.map fli x = xi ∧ F.map flj x = xj := by
  obtain ⟨z, hz⟩ := hz
  refine ⟨l, fli, flj, z, ?_, ?_⟩
  · apply (F.map fi).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hz]
  · apply (F.map fj).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, Subsingleton.elim (flj ≫ fj) (fli ≫ fi), hz, h]

variable {e}

theorem glue_cond_of_hom {a b c : GlueIndex e} (fa : a ⟶ c) (fb : b ⟶ c) (hab : a ⟶ b)
    (xa : (glueDiagram t e).obj a) (xb : (glueDiagram t e).obj b)
    (h : (glueDiagram t e).map fa xa = (glueDiagram t e).map fb xb) :
    ∃ (l : GlueIndex e) (fla : l ⟶ a) (flb : l ⟶ b) (x : (glueDiagram t e).obj l),
      (glueDiagram t e).map fla x = xa ∧ (glueDiagram t e).map flb x = xb :=
  exists_of_mem_range_map (glueDiagram t e) fa fb xa xb h a (𝟙 a) hab
    ⟨xa, by rw [Category.id_comp]⟩

theorem glue_cond_of_hom' {a b c : GlueIndex e} (fa : a ⟶ c) (fb : b ⟶ c) (hba : b ⟶ a)
    (xa : (glueDiagram t e).obj a) (xb : (glueDiagram t e).obj b)
    (h : (glueDiagram t e).map fa xa = (glueDiagram t e).map fb xb) :
    ∃ (l : GlueIndex e) (fla : l ⟶ a) (flb : l ⟶ b) (x : (glueDiagram t e).obj l),
      (glueDiagram t e).map fla x = xa ∧ (glueDiagram t e).map flb x = xb := by
  obtain ⟨l, flb, fla, x, hxb, hxa⟩ := glue_cond_of_hom t fb fa hba xb xa h.symm
  exact ⟨l, fla, flb, x, hxa, hxb⟩

theorem glue_cond {a b c : GlueIndex e} (fa : a ⟶ c) (fb : b ⟶ c)
    (xa : (glueDiagram t e).obj a) (xb : (glueDiagram t e).obj b)
    (h : (glueDiagram t e).map fa xa = (glueDiagram t e).map fb xb) :
    ∃ (l : GlueIndex e) (fla : l ⟶ a) (flb : l ⟶ b) (x : (glueDiagram t e).obj l),
      (glueDiagram t e).map fla x = xa ∧ (glueDiagram t e).map flb x = xb := by
  have hac := fa.le
  have hbc := fb.le
  cases c with
  | torus hc =>
    cases a <;> cases b <;> first
      | simp only [overlap_le_torus, chart_le_torus] at hac
      | simp only [overlap_le_torus, chart_le_torus] at hbc
      | exact glue_cond_of_hom t fa fb (homOfLE trivial) xa xb h
  | overlap k hk =>
    cases a with
    | chart _ => simp only [chart_le_overlap] at hac
    | torus _ => exact glue_cond_of_hom t fa fb (homOfLE trivial) xa xb h
    | overlap i hi =>
      cases b with
      | chart _ => simp only [chart_le_overlap] at hbc
      | torus _ => exact glue_cond_of_hom' t fa fb (homOfLE trivial) xa xb h
      | overlap j hj =>
        simp only [overlap_le_overlap] at hac hbc
        subst hac; subst hbc
        exact glue_cond_of_hom t fa fb (homOfLE (by simp)) xa xb h
  | chart k =>
    cases a with
    | torus _ => exact glue_cond_of_hom t fa fb (homOfLE trivial) xa xb h
    | chart i =>
      simp only [chart_le_chart] at hac
      subst hac
      exact glue_cond_of_hom' t fa fb fb xa xb h
    | overlap i hi =>
      cases b with
      | torus _ => exact glue_cond_of_hom' t fa fb (homOfLE trivial) xa xb h
      | chart j =>
        simp only [chart_le_chart] at hbc
        subst hbc
        exact glue_cond_of_hom t fa fb fa xa xb h
      | overlap j hj =>
        by_cases hij : i = j
        · subst hij
          exact glue_cond_of_hom t fa fb (homOfLE (by simp)) xa xb h
        · simp only [overlap_le_chart] at hac hbc
          have hUV : U t ∉ ((glueDiagram t e).map fa xa).asIdeal ∧
              V t ∉ ((glueDiagram t e).map fa xa).asIdeal := by
            rcases hac with hk | hk <;> rcases hbc with hk' | hk'
            · exact absurd (hk.symm.trans hk') hij
            · refine ⟨?_, ?_⟩
              · rw [h]
                refine U_notMem_of_mem_range_overlapToChartRight t ⟨xb, ?_⟩
                rw [show (glueDiagram t e).map fb = overlapToChartRight t from
                  glueMap_overlap_chart_of_ne t e hj fb.le (by omega)]
                rfl
              · refine V_notMem_of_mem_range_overlapToChartLeft t ⟨xa, ?_⟩
                rw [show (glueDiagram t e).map fa = overlapToChartLeft t from
                  glueMap_overlap_chart_of_eq t e hi fa.le (by rw [hk])]
                rfl
            · refine ⟨?_, ?_⟩
              · refine U_notMem_of_mem_range_overlapToChartRight t ⟨xa, ?_⟩
                rw [show (glueDiagram t e).map fa = overlapToChartRight t from
                  glueMap_overlap_chart_of_ne t e hi fa.le (by omega)]
                rfl
              · rw [h]
                refine V_notMem_of_mem_range_overlapToChartLeft t ⟨xb, ?_⟩
                rw [show (glueDiagram t e).map fb = overlapToChartLeft t from
                  glueMap_overlap_chart_of_eq t e hj fb.le (by rw [hk'])]
                rfl
            · exact absurd (Fin.ext (by omega)) hij
          exact exists_of_mem_range_map (glueDiagram t e) fa fb xa xb h (torus k.pos)
            (homOfLE trivial) (homOfLE trivial) (mem_range_torusToChart t hUV.1 hUV.2 k)

instance isLocallyDirected_glueDiagram : (glueDiagram t e ⋙ Scheme.forget).IsLocallyDirected where
  cond fa fb xa xb h := glue_cond t fa fb xa xb h

end locallyDirected

section scheme

variable (e : ℕ)

def Resolution : Scheme.{u} := colimit (glueDiagram t e)

namespace Resolution

def ι (i : Fin e) : chartScheme t ⟶ Resolution t e := colimit.ι (glueDiagram t e) (chart i)

def ιOverlap (i : Fin e) (hi : (i : ℕ) + 1 < e) : overlapScheme t ⟶ Resolution t e :=
  colimit.ι (glueDiagram t e) (overlap i hi)

def ιTorus (h : 0 < e) : torusScheme t ⟶ Resolution t e := colimit.ι (glueDiagram t e) (torus h)

instance isOpenImmersion_ι (i : Fin e) : IsOpenImmersion (ι t e i) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (glueDiagram t e) (chart i)))

instance isOpenImmersion_ιOverlap (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    IsOpenImmersion (ιOverlap t e i hi) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (glueDiagram t e) (overlap i hi)))

instance isOpenImmersion_ιTorus (h : 0 < e) : IsOpenImmersion (ιTorus t e h) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (glueDiagram t e) (torus h)))

@[reassoc]
theorem overlapToChartLeft_ι (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    overlapToChartLeft t ≫ ι t e i = ιOverlap t e i hi := by
  rw [← glueMap_overlap_chart_self t e i hi (by simp)]
  exact colimit.w (glueDiagram t e) (homOfLE (by simp) : overlap i hi ⟶ chart i)

@[reassoc]
theorem overlapToChartRight_ι (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    overlapToChartRight t ≫ ι t e ⟨(i : ℕ) + 1, hi⟩ = ιOverlap t e i hi := by
  rw [← glueMap_overlap_chart_succ t e i hi (by simp)]
  exact colimit.w (glueDiagram t e) (homOfLE (by simp) : overlap i hi ⟶ chart ⟨(i : ℕ) + 1, hi⟩)

@[reassoc]
theorem torusToChart_ι (i : Fin e) :
    torusToChart t i ≫ ι t e i = ιTorus t e i.pos :=
  colimit.w (glueDiagram t e) (homOfLE trivial : torus i.pos ⟶ chart i)

@[reassoc]
theorem torusToOverlap_ιOverlap (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    torusToOverlap t i ≫ ιOverlap t e i hi = ιTorus t e i.pos :=
  colimit.w (glueDiagram t e) (homOfLE trivial : torus i.pos ⟶ overlap i hi)

theorem glue_condition (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    overlapToChartLeft t ≫ ι t e i = overlapToChartRight t ≫ ι t e ⟨(i : ℕ) + 1, hi⟩ := by
  rw [overlapToChartLeft_ι, overlapToChartRight_ι]

theorem exists_ι_apply_eq (x : Resolution t e) : ∃ (i : Fin e) (y : chartScheme t), ι t e i y = x := by
  obtain ⟨a, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (glueDiagram t e) x
  cases a with
  | chart i => exact ⟨i, y, hy⟩
  | overlap i hi =>
    refine ⟨i, overlapToChartLeft t y, ?_⟩
    rw [← Scheme.Hom.comp_apply, overlapToChartLeft_ι]
    exact hy
  | torus h =>
    refine ⟨⟨0, h⟩, torusToChart t ((⟨0, h⟩ : Fin e) : ℕ) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, torusToChart_ι]
    exact hy

theorem iSup_opensRange_ι : ⨆ i, (ι t e i).opensRange = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨i, y, rfl⟩ := exists_ι_apply_eq t e x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, rfl⟩

def openCover : (Resolution t e).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin e) (fun _ => chartScheme t) (ι t e) (exists_ι_apply_eq t e)

@[simp] theorem openCover_I₀ : (openCover t e).I₀ = Fin e := rfl
@[simp] theorem openCover_X (i : Fin e) : (openCover t e).X i = chartScheme t := rfl
@[simp] theorem openCover_f (i : Fin e) : (openCover t e).f i = ι t e i := rfl

instance (i : (openCover t e).I₀) : IsAffine ((openCover t e).X i) :=
  inferInstanceAs (IsAffine (chartScheme t))

theorem ι_apply_eq_iff {i j : Fin e} (x y : chartScheme t) :
    ι t e i x = ι t e j y ↔ ∃ (a : GlueIndex e) (hi : a ≤ chart i) (hj : a ≤ chart j)
      (z : glueObj t e a), glueMap t e a (chart i) hi z = x ∧ glueMap t e a (chart j) hj z = y := by
  constructor
  · intro h
    obtain ⟨a, fi, fj, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (glueDiagram t e)).mp h
    exact ⟨a, fi.le, fj.le, z, h1, h2⟩
  · rintro ⟨a, hi, hj, z, h1, h2⟩
    exact (Scheme.IsLocallyDirected.ι_eq_ι_iff (glueDiagram t e)).mpr ⟨a, homOfLE hi, homOfLE hj, z, h1, h2⟩

abbrev chartToCrossing (i : Fin e) : chartScheme t ⟶ crossingScheme (t ^ e) :=
  Spec.map (CommRingCat.ofHom (resolutionChart t e i).toRingHom)

def crossingCoconeApp : ∀ a : GlueIndex e, (glueObj t e a ⟶ crossingScheme (t ^ e))
  | .chart j => chartToCrossing t e j
  | .overlap i _ => overlapToChartLeft t ≫ chartToCrossing t e i
  | .torus h => torusToChart t (0 : ℕ) ≫ chartToCrossing t e ⟨0, h⟩

theorem overlapToChartRight_chartToCrossing (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    overlapToChartRight t ≫ chartToCrossing t e ⟨(i : ℕ) + 1, hi⟩ =
      overlapToChartLeft t ≫ chartToCrossing t e i := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  refine congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (congrArg AlgHom.toRingHom
    (?_ : (transitionUp t).comp (resolutionChart t e ⟨i + 1, hi⟩) =
      (IsScalarTower.toAlgHom W (CrossingQuotient W t) (OverlapRing t)).comp (resolutionChart t e i)))
  apply algHom_ext_chart
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, resolutionChart_U, resolutionChart_U, map_mul,
      map_mul, AlgHom.commutes, AlgHom.commutes, transitionUp_U]
    rw [pow_succ, map_mul, IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (OverlapRing t) t,
      ← U_mul_V, map_mul, mul_assoc, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
    rfl
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, resolutionChart_V, resolutionChart_V, map_mul,
      map_mul, AlgHom.commutes, AlgHom.commutes, transitionUp_V]
    rw [← mul_assoc, ← map_mul, ← pow_succ,
      show e - 1 - ((i : ℕ) + 1) + 1 = e - 1 - (i : ℕ) by omega]
    rfl

theorem torusChart_comp_resolutionChart (i : Fin e) :
    (torusChart t i).comp (resolutionChart t e i) =
      (torusChart t 0).comp (resolutionChart t e ⟨0, i.pos⟩) := by
  apply algHom_ext_chart
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, resolutionChart_U, resolutionChart_U, map_mul, map_mul,
      AlgHom.commutes, AlgHom.commutes, torusChart_U, torusChart_U, map_pow, map_pow]
    change tT t ^ (i : ℕ) * (xT t * tinv t ^ (i : ℕ)) = tT t ^ 0 * (xT t * tinv t ^ 0)
    rw [mul_left_comm, tT_pow_mul_tinv_pow, pow_zero, pow_zero, one_mul, mul_one]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, resolutionChart_V, resolutionChart_V, map_mul, map_mul,
      AlgHom.commutes, AlgHom.commutes, torusChart_V, torusChart_V, map_pow, map_pow]
    change tT t ^ (e - 1 - (i : ℕ)) * (yT t * tT t ^ (i : ℕ)) = tT t ^ (e - 1 - 0) * (yT t * tT t ^ 0)
    rw [mul_left_comm, ← pow_add, show e - 1 - (i : ℕ) + i = e - 1 - 0 by have := i.2; omega,
      pow_zero, mul_one, mul_comm]

theorem torusToChart_chartToCrossing (i : Fin e) :
    torusToChart t i ≫ chartToCrossing t e i = torusToChart t (0 : ℕ) ≫ chartToCrossing t e ⟨0, i.pos⟩ := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
    (congrArg AlgHom.toRingHom (torusChart_comp_resolutionChart t e i))

theorem glueMap_crossingCoconeApp (a b : GlueIndex e) (hab : a ≤ b) :
    glueMap t e a b hab ≫ crossingCoconeApp t e b = crossingCoconeApp t e a := by
  cases a <;> cases b <;>
    simp only [torus_le, overlap_le_overlap, overlap_le_chart, chart_le_chart, overlap_le_torus,
      chart_le_torus, chart_le_overlap] at hab
  case torus.torus => exact Category.id_comp _
  case torus.overlap h i hi hab0 =>
    change torusToOverlap t i ≫ overlapToChartLeft t ≫ chartToCrossing t e i = torusToChart t (0 : ℕ) ≫ _
    rw [← Category.assoc, torusToOverlap_overlapToChartLeft, torusToChart_chartToCrossing]
  case torus.chart h j hab0 => exact torusToChart_chartToCrossing t e j
  case overlap.overlap => subst hab; exact Category.id_comp _
  case overlap.chart i hi j hab0 =>
    rcases hab with rfl | hj
    · rw [glueMap_overlap_chart_self]; rfl
    · obtain rfl : j = ⟨(i : ℕ) + 1, hi⟩ := Fin.ext hj
      rw [glueMap_overlap_chart_succ]
      exact overlapToChartRight_chartToCrossing t e i hi
  case chart.chart => subst hab; exact Category.id_comp _

def crossingCocone : Cocone (glueDiagram t e) where
  pt := crossingScheme (t ^ e)
  ι := { app := crossingCoconeApp t e
         naturality := fun a b f =>
           (glueMap_crossingCoconeApp t e a b f.le).trans (Category.comp_id _).symm }

def toCrossing : Resolution t e ⟶ crossingScheme (t ^ e) := colimit.desc (glueDiagram t e) (crossingCocone t e)

@[reassoc (attr := simp)]
theorem ι_toCrossing (i : Fin e) : ι t e i ≫ toCrossing t e = chartToCrossing t e i :=
  colimit.ι_desc (crossingCocone t e) (chart i)

@[reassoc]
theorem ιTorus_toCrossing (h : 0 < e) :
    ιTorus t e h ≫ toCrossing t e = torusToChart t (0 : ℕ) ≫ chartToCrossing t e ⟨0, h⟩ :=
  colimit.ι_desc (crossingCocone t e) (torus h)

def toSpec : Resolution t e ⟶ Spec (CommRingCat.of W) :=
  toCrossing t e ≫ Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W (t ^ e))))

@[reassoc (attr := simp)]
theorem ι_toSpec (i : Fin e) :
    ι t e i ≫ toSpec t e = Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W t))) := by
  rw [toSpec, ι_toCrossing_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (resolutionChart t e i).comp_algebraMap

theorem hom_ext {X : Scheme.{u}} {f g : Resolution t e ⟶ X} (h : ∀ i, ι t e i ≫ f = ι t e i ≫ g) :
    f = g := by
  apply colimit.hom_ext
  intro a
  cases a with
  | chart i => exact h i
  | overlap i hi =>
    change ιOverlap t e i hi ≫ f = ιOverlap t e i hi ≫ g
    rw [← overlapToChartLeft_ι, Category.assoc, Category.assoc, h i]
  | torus h0 =>
    change ιTorus t e h0 ≫ f = ιTorus t e h0 ≫ g
    rw [← torusToChart_ι t e ⟨0, h0⟩, Category.assoc, Category.assoc, h]

end Resolution

end scheme

end CrossingQuotient

end MvPolynomial

end


