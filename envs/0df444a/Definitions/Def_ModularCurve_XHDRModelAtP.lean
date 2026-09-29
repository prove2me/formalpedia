-- Prove2me | Definitions.Def_ModularCurve_XHDRModelAtP
-- name    : ModularCurve_XHDRModelAtP
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/48275845-47c9-58db-a4e0-e43ae2733490
-- title:
--   Deligne–Rapoport model of XH​(M) at p: property bundle
-- statement:
--   Fix a prime $p$, an integer $M\ge 1$ with $p\mid M$, a subgroup $H\le(\mathbb Z/M)^\times$, and write $R:=$ [`GaloisRep.ratLocalizedAt p`](../def/GaloisRep_Flat.html#L8), the subring of $\mathbb Q$ of rationals whose denominator is coprime to $p$. For a subgroup $\Gamma\le\mathrm{SL}_2(\mathbb Z)$, the carrier `X p Γ hj` is the two-chart integral model `TwoChartIntegralModel` of the $q$-expansion function field $F(\Gamma):=$ `qExpFunctionFieldC ℚ Γ` $\subseteq\mathbb Q((q))$ with respect to the element $j$: the pushout of $\operatorname{Spec}$ of the integral closure of $R[j]$ in $F(\Gamma)$ and $\operatorname{Spec}$ of the integral closure of $R[j^{-1}]$ in $F(\Gamma)$ along the localisation $\operatorname{Spec}$ of the integral closure of $R[j,j^{-1}]$, together with its structure morphism `toBase` to $\operatorname{Spec} R$; here $j$ is `jqModC ℚ`, viewed in $F(\Gamma)$ through the hypothesis `hj` that it lies in the level-$\top$ field, and it is nonzero. Auxiliary declarations name the two chart algebras and their open immersions, the fibre $\mathtt{X}\times_{\operatorname{Spec}R}\operatorname{Spec}\kappa$ along a ring map $R\to\kappa$, the induced section of that fibre coming from a section of `toBase`, the induced map of fibres coming from a morphism over $\operatorname{Spec}R$, and the packaging of an automorphism over $\operatorname{Spec}R$. Levels $\Gamma_M:=\Gamma_H(M)$ and $\Gamma_N:=\Gamma_{H'}(M/p)$ are used, $H'$ being the image of $H$ in $(\mathbb Z/(M/p))^\times$.
--
--   The structure `XHDRModelAtP p M H hpM hj` is a property bundle asserting that this model is the Deligne–Rapoport model of $X_H(M)$ at $p$. Its fields fall into the following groups. (i) Geometry over $R$: `toBase` for $\Gamma_M$ is proper, flat and locally of finite presentation, the total space is integral, and every affine open has integrally closed ring of sections; for $\Gamma_N$ the structure morphism is proper and smooth of relative dimension $1$. (ii) Generic fibre: a `CurveModel` $\mathcal M$ over $\overline{\mathbb Q}$ with function field `xHFunctionFieldBar M H`, an isomorphism $\mathcal M.C\cong \mathtt X\times_R\overline{\mathbb Q}$ over $\operatorname{Spec}\overline{\mathbb Q}$, equivariance of the resulting bijection between $\overline{\mathbb Q}$-points and places for the action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ through `arithmeticGalois`, and a pinning identifying each function on the finite chart with the coefficient embedding of its $q$-expansion; furthermore the fibre over $\mathbb Q$ is smooth of relative dimension $1$ and geometrically integral. (iii) Cusps, $w$ and diamonds: two sections $\varepsilon_\infty,\varepsilon_0$ of `toBase`, where $\varepsilon_\infty$ factors through the chart at infinity by the $R$-algebra retraction sending a function to the constant coefficient of its $q$-expansion; an automorphism $w$ over $\operatorname{Spec}R$ with $\varepsilon_\infty\circ w=\varepsilon_0$; automorphisms $\langle d\rangle$ over $\operatorname{Spec}R$ for $d\in(\mathbb Z/M)^\times$, multiplicative in $d$, trivial for $d\in H$, commuting with $w$, acting on geometric points through `diamondAutHBar`, with $w^2=\langle d\rangle$ whenever $dp\equiv1$ in $\mathbb Z/(M/p)$. (iv) Degeneracy: a morphism $\pi$ to the $\Gamma_N$-model over $\operatorname{Spec}R$ compatible with chart inclusions that are the identity on $q$-expansions, diamonds $\langle d\rangle_0$ at the lower level, and the relation $\langle d\rangle$ followed by $\pi$ equals $\pi$ followed by $\langle d\bmod M/p\rangle_0$. (v) A largest open `smoothLocus` on which the model is smooth of relative dimension $1$, containing the images of both sections. (vi) Special fibre: for every valuation subring $A$ of $\overline{\mathbb Q}$ lying over $p$ with algebraically closed residue field $\kappa$ of characteristic $p$ and every $\rho:R\to A$ lifting $R\to\overline{\mathbb Q}$, the fibre over $\kappa$ is reduced; a `CurveModel` over $\kappa$ with function field `qExpFunctionFieldC κ Γ_N` isomorphic to the $\Gamma_N$-fibre, pinned against $q$-expansions; two closed immersions of that fibre into the $\Gamma_M$-fibre over $\kappa$, jointly surjective with distinct images, the first a section of $\pi$ on fibres and the second obtained from the first by $w$, both composites with $\pi$ inducing on places the Frobenius `qExpFrobeniusPlaceModL`; the sections $\varepsilon_\infty,\varepsilon_0$ land on the first and second component respectively; diamond equivariance of the two immersions; and the scheme-theoretic intersection of the two components is reduced and in bijection with the supersingular places `ssPlacesQExp κ Γ_N p`, the two points of a crossing being pinned to a supersingular place and its Frobenius image. The helper declarations `placeOn0`, `placeOn1` name those two places and `nodePair_mem` records that the pair lies in `ssNodePairsQExp κ Γ_N p`; `πw` is $w$ followed by $\pi$, again a morphism over $\operatorname{Spec}R$.
--
--   **Relation to Mathlib.** Mathlib has no integral models of modular curves; the carrier `TwoChartIntegralModel`, the notion `CurveModel` of a smooth proper model of a function field with its place-point dictionary, and the present property bundle are the project's own, stated on top of Mathlib's scheme-theoretic vocabulary (`IsProper`, `Flat`, `SmoothOfRelativeDimension`, `IsClosedImmersion`, `IsReduced`, pullbacks, `Scheme.functionField`).
--
--   **Where it is used.** The bundle records the geometry of $X_H(M)$ at a prime $p$ dividing the level — two copies of the level-$M/p$ curve crossing at the supersingular points, interchanged by $w_p$, with $\pi$ the identity on one component and Frobenius on the other — in the form used for the mod $p$ comparison of cusp forms, differentials and Jacobians at level divisible by $p$. This is the geometric input for the level-lowering and multiplicity-one arguments in the route from the Frey curve to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_XHDRModelAtP.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open scoped MatrixGroups

namespace ModularCurve

namespace XHDRLevel

abbrev R (p : ℕ) : Type := ↥(GaloisRep.ratLocalizedAt p)

theorem jqModC_rat_ne_zero : jqModC ℚ ≠ 0 := fun h =>
  IgusaScheme.jFull_ne_zero 1 (Subtype.ext h)

def jAt (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ↥(qExpFunctionFieldC ℚ Γ) :=
  ⟨jqModC ℚ, qExpFunctionFieldC_mono ℚ le_top hj⟩

@[simp] theorem coe_jAt (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    (jAt Γ hj : LaurentSeries ℚ) = jqModC ℚ := rfl

instance fact_jAt_ne_zero (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Fact (jAt Γ hj ≠ 0) :=
  ⟨fun h => jqModC_rat_ne_zero (by simpa using congrArg Subtype.val h)⟩

variable (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

abbrev X : Scheme.{0} := TwoChartIntegralModel (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)

abbrev toBase : X p Γ hj ⟶ Spec (CommRingCat.of (R p)) :=
  TwoChartIntegralModel.toBase (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)

abbrev chartAlgFin := TwoChartIntegralModel.chartAlgFin (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)
abbrev chartAlgInf := TwoChartIntegralModel.chartAlgInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)
abbrev ιFin := TwoChartIntegralModel.ιFin (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)
abbrev ιInf := TwoChartIntegralModel.ιInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)
abbrev jChartFin : ↥(chartAlgFin p Γ hj) := TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)

variable {p Γ hj}

abbrev fibre {κ : Type} [CommRing κ] (toκ : R p →+* κ) : Scheme.{0} :=
  pullback (toBase p Γ hj) (Spec.map (CommRingCat.ofHom toκ))

def sectionFibre (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p Γ hj))
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) : Spec (CommRingCat.of κ) ⟶ fibre (Γ := Γ) (hj := hj) toκ :=
  pullback.lift (Spec.map (CommRingCat.ofHom toκ) ≫ ε.1) (𝟙 _)
    (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp])

def fibreMap {Γ' : Subgroup SL(2, ℤ)} (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj))
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) : fibre (Γ := Γ) (hj := hj) toκ ⟶ fibre (Γ := Γ') (hj := hj) toκ :=
  pullback.map _ _ _ _ φ.1 (𝟙 _) (𝟙 _) (by rw [φ.2, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

def overOfIso (w : X p Γ hj ≅ X p Γ hj) (hw : w.hom ≫ toBase p Γ hj = toBase p Γ hj) :
    SchemeHomOver (toBase p Γ hj) (toBase p Γ hj) := ⟨w.hom, hw⟩

end XHDRLevel

open XHDRLevel

section

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

abbrev XHDRLevel.ΓN : Subgroup SL(2, ℤ) := CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)

abbrev XHDRLevel.ΓM : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H

structure XHDRModelAtP where

  [isProper : IsProper (toBase p (ΓM M H) hj)]
  [flat : Flat (toBase p (ΓM M H) hj)]
  [isIntegral : IsIntegral (X p (ΓM M H) hj)]
  [lfp : LocallyOfFinitePresentation (toBase p (ΓM M H) hj)]

  normal : ∀ U : (X p (ΓM M H) hj).Opens, IsAffineOpen U → IsIntegrallyClosed Γ(X p (ΓM M H) hj, U)

  [isProper0 : IsProper (toBase p (ΓN p M H hpM) hj)]
  [smooth0 : SmoothOfRelativeDimension 1 (toBase p (ΓN p M H hpM) hj)]

  Meta : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)
  eeta : Meta.C ⟶ pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  [eeta_iso : IsIso eeta]
  heeta : eeta ≫ pullback.snd _ _ = Meta.toBase

  hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta.C // s ≫ Meta.toBase = 𝟙 _}),
      x'.1 ≫ eeta ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ eeta ≫ pullback.fst _ _ →
      Meta.pointEquivPlace x' = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) g • Meta.pointEquivPlace x

  [Meta_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))]
  Meta_pin : ∀ a : ↥(chartAlgFin p (ΓM M H) hj),
    ((Meta.ffEquiv.symm
        (Meta.C.germToFunctionField
          ((eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
            ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
          (((eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
              ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
            (((ιFin p (ΓM M H) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv a))))
        : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)

  smooth_generic : SmoothOfRelativeDimension 1
    (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))
  geomIntegral_generic : GeometricallyIntegral
    (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))

  εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj)
  εzero : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj)

  rhoInf : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] R p
  rhoInf_spec : ∀ b : ↥(chartAlgInf p (ΓM M H) hj),
    ((rhoInf b : R p) : ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ).coeff 0
  εinf_chart : εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ ιInf p (ΓM M H) hj

  w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj
  w_over : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj
  w_sections : εinf.1 ≫ w.hom = εzero.1

  dia : (ZMod M)ˣ → (X p (ΓM M H) hj ≅ X p (ΓM M H) hj)
  dia_over : ∀ d, (dia d).hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj
  dia_mul : ∀ d d', (dia (d * d')).hom = (dia d).hom ≫ (dia d').hom
  dia_mem : ∀ d, d ∈ H → dia d = Iso.refl _

  dia_generic : ∀ (d : (ZMod M)ˣ)
      (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta.C // s ≫ Meta.toBase = 𝟙 _}),
      x'.1 ≫ eeta ≫ pullback.fst _ _ = x.1 ≫ eeta ≫ pullback.fst _ _ ≫ (dia d).hom →
      Meta.pointEquivPlace x' = SemilinearAut.ofAlgAut (diamondAutHBar M H d) • Meta.pointEquivPlace x

  w_dia : ∀ d, w.hom ≫ (dia d).hom = (dia d).hom ≫ w.hom

  w_sq : ∀ d : (ZMod M)ˣ,
    ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 →
      w.hom ≫ w.hom = (dia d).hom

  π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj)
  iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj)
  iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
    ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)
  pi_chart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj

  iotaInf : ↥(chartAlgInf p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj)
  iotaInf_spec : ∀ b, (((iotaInf b : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
    ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)
  pi_chartInf : ιInf p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj

  dia0 : (ZMod (M / p))ˣ → (X p (ΓN p M H hpM) hj ≅ X p (ΓN p M H hpM) hj)
  dia0_over : ∀ d, (dia0 d).hom ≫ toBase p (ΓN p M H hpM) hj = toBase p (ΓN p M H hpM) hj

  pi_dia : ∀ d : (ZMod M)ˣ, (dia d).hom ≫ π.1 = π.1 ≫ (dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).hom

  smoothLocus : (X p (ΓM M H) hj).Opens
  [smoothLocus_relDim : SmoothOfRelativeDimension 1 (smoothLocus.ι ≫ toBase p (ΓM M H) hj)]
  smoothLocus_maximal : ∀ U : (X p (ΓM M H) hj).Opens, Smooth (U.ι ≫ toBase p (ΓM M H) hj) → U ≤ smoothLocus
  εinf_mem_smoothLocus : Set.range εinf.1.base ⊆ (smoothLocus : Set (X p (ΓM M H) hj))
  εzero_mem_smoothLocus : Set.range εzero.1.base ⊆ (smoothLocus : Set (X p (ΓM M H) hj))

  fibre_reduced : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    IsReduced (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))

  Mfib : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    CurveModel (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))
  efib : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    (Mfib A hA ρ hρ).C ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)
  efib_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)), IsIso (efib A hA ρ hρ)
  hefib : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    efib A hA ρ hρ ≫ pullback.snd _ _ = (Mfib A hA ρ hρ).toBase

  [Mfib_chart_nonempty : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    Nonempty (Scheme.Opens.toScheme ((efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)))]
  Mfib_pin : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A),
    coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) →
    (((Mfib A hA ρ hρ).ffEquiv.symm
        ((Mfib A hA ρ hρ).C.germToFunctionField
          ((efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ
            ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))
          (((efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app
              ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
            (((ιFin p (ΓN p M H hpM) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓN p M H hpM) hj))).inv b))))
        : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
      coeffMap (IsLocalRing.residue ↥A) y

  comp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
  comp_over : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (i : Fin 2),
    comp A hA ρ hρ i ≫ pullback.snd _ _ = pullback.snd _ _
  comp_isClosedImmersion : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (i : Fin 2),
    IsClosedImmersion (comp A hA ρ hρ i)
  comp_jointly_surjective : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (y : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), y ∈ Set.range (comp A hA ρ hρ 0).base ∨ y ∈ Set.range (comp A hA ρ hρ 1).base
  range_comp_ne : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    Set.range (comp A hA ρ hρ 0).base ≠ Set.range (comp A hA ρ hρ 1).base

  comp_pi : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    comp A hA ρ hρ 0 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) = 𝟙 _

  comp1_pi_place : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (P : closedPoints (Mfib A hA ρ hρ).C),
    ∃ h : (inv (efib A hA ρ hρ)).base ((efib A hA ρ hρ ≫ comp A hA ρ hρ 1 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ)).base P.1) ∈ closedPoints (Mfib A hA ρ hρ).C,
      (Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ = qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p ((Mfib A hA ρ hρ).placeOfPoint P)

  comp_w : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    comp A hA ρ hρ 0 ≫ fibreMap (overOfIso w w_over) ((IsLocalRing.residue ↥A).comp ρ) = comp A hA ρ hρ 1

  pi_w_comp0_place : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (P : closedPoints (Mfib A hA ρ hρ).C),
    ∃ h : (inv (efib A hA ρ hρ)).base ((efib A hA ρ hρ ≫ comp A hA ρ hρ 0 ≫ fibreMap (overOfIso w w_over) ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ)).base P.1) ∈
        closedPoints (Mfib A hA ρ hρ).C,
      (Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ = qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p ((Mfib A hA ρ hρ).placeOfPoint P)

  comp_dia : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (i : Fin 2) (d : (ZMod M)ˣ),
    comp A hA ρ hρ i ≫ fibreMap (overOfIso (dia d) (dia_over d)) ((IsLocalRing.residue ↥A).comp ρ) =
      fibreMap (overOfIso (dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)) (dia0_over _)) ((IsLocalRing.residue ↥A).comp ρ) ≫ comp A hA ρ hρ i

  εinf_mem_comp0 : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    Set.range (sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ Set.range (comp A hA ρ hρ 0).base
  εzero_mem_comp1 : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    Set.range (sectionFibre εzero ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ Set.range (comp A hA ρ hρ 1).base

  crossing_reduced : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    IsReduced (pullback (comp A hA ρ hρ 0) (comp A hA ρ hρ 1))
  nodeEquiv : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    ↥(pullback (comp A hA ρ hρ 0) (comp A hA ρ hρ 1)) ≃ ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p)

  node_pin : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (n : ↥(pullback (comp A hA ρ hρ 0) (comp A hA ρ hρ 1))),
    (∃ h : (inv (efib A hA ρ hρ)).base ((pullback.snd (comp A hA ρ hρ 0) (comp A hA ρ hρ 1)).base n) ∈ closedPoints (Mfib A hA ρ hρ).C,
        (Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          ((nodeEquiv A hA ρ hρ n : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p)) : Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ∧
    (∃ h : (inv (efib A hA ρ hρ)).base ((pullback.fst (comp A hA ρ hρ 0) (comp A hA ρ hρ 1)).base n) ∈ closedPoints (Mfib A hA ρ hρ).C,
        (Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p
            ((nodeEquiv A hA ρ hρ n : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p)) : Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))))

attribute [instance] XHDRModelAtP.eeta_iso XHDRModelAtP.smoothLocus_relDim
  XHDRModelAtP.efib_iso XHDRModelAtP.Mfib_chart_nonempty XHDRModelAtP.Meta_chart_nonempty

end

namespace XHDRModelAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)

abbrev placeOn0 (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) : Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) :=
  qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p (𝔛.nodeEquiv A hA ρ hρ n : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p))

abbrev placeOn1 (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) : Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) :=
  (𝔛.nodeEquiv A hA ρ hρ n : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p))

theorem nodePair_mem (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) :
    (𝔛.placeOn0 A hA ρ hρ n, 𝔛.placeOn1 A hA ρ hρ n) ∈ ssNodePairsQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p :=
  frob_mk_mem_ssNodePairsQExp (𝔛.nodeEquiv A hA ρ hρ n).2

def πw : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj) :=
  ⟨𝔛.w.hom ≫ 𝔛.π.1, by rw [Category.assoc, 𝔛.π.2, 𝔛.w_over]⟩

@[simp] theorem πw_val : 𝔛.πw.1 = 𝔛.w.hom ≫ 𝔛.π.1 := rfl

end XHDRModelAtP

end ModularCurve

end


