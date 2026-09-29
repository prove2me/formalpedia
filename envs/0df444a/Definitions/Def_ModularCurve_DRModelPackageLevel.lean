-- Prove2me | Definitions.Def_ModularCurve_DRModelPackageLevel
-- name    : ModularCurve_DRModelPackageLevel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/f897753d-ab1d-518f-a6ca-ccc303ac1d1a
-- title:
--   Deligne–Rapoport model package for X0​(N0​q) at q
-- statement:
--   Fix $N_0\ge 1$ and a prime $q$, and write $R=$ [`GaloisRep.ratLocalizedAt q`](../def/GaloisRep_Flat.html#L8), the subring of $\mathbb{Q}$ of fractions whose denominator is coprime to $q$. The abbreviations set up the arena: `X` is the Igusa scheme of level $N_0q$ over $R$ (the scheme obtained by gluing $\operatorname{Spec}$ of the integral closures of $R[j]$ and $R[j^{-1}]$ inside the full modular function field of level $N_0q$), `toBase` its structure map to $\operatorname{Spec} R$, and `X0`, `toBase0` the same at level $N_0$; `fibre`/`fibre0` are the base changes of these along a ring map $R\to\kappa$, while `sectionFibre`, `fibreMap`, `fibreMap0` and `sectionFibreOver` transport a section of `toBase`, an endomorphism of `X` over $R$, a morphism `X ⟶ X0` over $R$, and a section over $\operatorname{Spec}$ of $R\to A$ for a local ring $A$, into the corresponding fibres.
--
--   The structure `DRModelPackageLevel N₀ q hqN`, for $q\nmid N_0$, is a property bundle carrying, as named fields on this fixed scheme, the Deligne–Rapoport description of $X_0(N_0q)$ over $R$. Its fields assert: (i) `toBase` is proper, flat and locally of finite presentation, `X` is integral, and sections over affine opens are integrally closed; (ii) a `CurveModel` `Meta` of the geometric modular function field over $\overline{\mathbb{Q}}$ together with an isomorphism `eeta` onto the geometric generic fibre, compatible with the base maps, Galois-equivariant on $\overline{\mathbb{Q}}$-points for the action `arithmeticGalois`, and pinned so that chart elements read off as their $q$-expansions under `coeffEmb`; smoothness of relative dimension $1$ and geometric integrality of the generic fibre over $\mathbb{Q}$; (iii) two sections $\varepsilon_\infty,\varepsilon_0$ of `toBase`, with $\varepsilon_\infty$ pinned as $\operatorname{Spec}$ of the constant-$q$-coefficient retraction `rhoInf` of the pole chart, an involutive automorphism `w` of `X` over $R$ with $\varepsilon_\infty\circ w=\varepsilon_0$ and with chart description given by an algebra automorphism `theta` inducing `atkinLehnerInvolutionFull N₀ q`, and a degeneracy morphism $\pi$ over $R$ described on both charts by $q$-expansion-preserving inclusions `iota0`, `iotaInf` of chart algebras; (iv) a largest open `smoothLocus` smooth of relative dimension $1$ over $R$, containing the images of both sections; (v) for every algebraically closed field $\kappa$ of characteristic $q$ and every ring map $R\to\kappa$: the fibre is reduced; a `CurveModel` `Mfib` over $\kappa$ of `modularFunctionFieldC κ N₀` isomorphic to `fibre0` via `efib`, pinned so that the $j$-chart generator reads as `jGeomGen κ N₀` and an element with $q$-expansion `qExpand ℚ N₀ jq` as `jNGeomGen κ N₀`; two closed immersions `comp κ toκ 0`, `comp κ toκ 1` of `fibre0` into the fibre over $\kappa$, jointly surjective with distinct images, the first a section of the $\pi$-fibre map, the second inducing on places the translation by `arithFrobC q κ N₀`, with `comp 1` the `w`-transform of `comp 0`, and with $\varepsilon_\infty$, $\varepsilon_0$ landing in the first and second component respectively; and the scheme-theoretic intersection of the two components reduced, with a bijection `nodeEquiv` from its points to the places in `ssPlaces q N₀ κ`, the two projections of a node going to the corresponding place and to its Frobenius translate. Two further fields record that the image of $\varepsilon_\infty$ in `fibre0`, followed by the two components, gives back $\varepsilon_\infty$ and $\varepsilon_0$. The derived declarations give the width `placeWidthChar q N₀` of the place attached to a node, the composite of `w` with $\pi$ as a morphism over $R$, and the abbreviation `εinf0` for the pushforward of $\varepsilon_\infty$ to `fibre0`.
--
--   **Relation to Mathlib.** Mathlib has no modular curves or integral models of them; the Igusa scheme, `CurveModel`, the place and width notions and this bundle are the project's own. The fields are phrased with Mathlib's scheme-morphism properties (`IsProper`, `Flat`, `LocallyOfFinitePresentation`, `SmoothOfRelativeDimension`, `GeometricallyIntegral`, `IsClosedImmersion`, `IsReduced`, `IsIntegrallyClosed`) and with limits and colimits in the category of schemes.
--
--   **Where it is used.** The package is the integral-model input for the geometry of $J_0(N_0q)$ at $q$: the two components of the special fibre, the degeneracy map $\pi$, the Atkin–Lehner involution $w_q$ and the supersingular crossing points with their widths are what the Eichler–Shimura and level-change arguments at $q$ are read off from, hence they feed Ribet's level lowering and the local analysis at $q$ in the modularity lifting step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_DRModelPackageLevel.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve.IgusaScheme

namespace ModularCurve

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]

theorem DRModelPackageLevel.neZero_mul : NeZero (N₀ * q) :=
  ⟨Nat.mul_ne_zero (NeZero.ne N₀) (Fact.out : q.Prime).ne_zero⟩

attribute [local instance] DRModelPackageLevel.neZero_mul

namespace DRLevel

abbrev R : Type := ↥(GaloisRep.ratLocalizedAt q)

abbrev X : Scheme.{0} := IgusaScheme (N₀ * q) q
abbrev toBase : X N₀ q ⟶ Spec (CommRingCat.of (R q)) := IgusaScheme.igusaTo (N₀ * q) q

abbrev X0 : Scheme.{0} := IgusaScheme N₀ q
abbrev toBase0 : X0 N₀ q ⟶ Spec (CommRingCat.of (R q)) := IgusaScheme.igusaTo N₀ q

variable {N₀ q}

abbrev fibre {κ : Type} [CommRing κ] (toκ : R q →+* κ) : Scheme.{0} :=
  pullback (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))

abbrev fibre0 {κ : Type} [CommRing κ] (toκ : R q →+* κ) : Scheme.{0} :=
  pullback (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))

def sectionFibre (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q))
    {κ : Type} [CommRing κ] (toκ : R q →+* κ) : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) toκ :=
  pullback.lift (Spec.map (CommRingCat.ofHom toκ) ≫ ε.1) (𝟙 _)
    (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp])

def fibreMap (φ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q)
    {κ : Type} [CommRing κ] (toκ : R q →+* κ) : fibre (N₀ := N₀) toκ ⟶ fibre (N₀ := N₀) toκ :=
  pullback.map _ _ _ _ φ (𝟙 _) (𝟙 _) (by rw [hφ, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

def fibreMap0 (π : SchemeHomOver (toBase N₀ q) (toBase0 N₀ q))
    {κ : Type} [CommRing κ] (toκ : R q →+* κ) : fibre (N₀ := N₀) toκ ⟶ fibre0 (N₀ := N₀) toκ :=
  pullback.map _ _ _ _ π.1 (𝟙 _) (𝟙 _) (by rw [π.2, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

def sectionFibreOver {A : Type} [CommRing A] [IsLocalRing A]
    (ρ : R q →+* A) (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ q)) :
    Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue A).comp ρ) :=
  pullback.lift (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s.1) (𝟙 _) (by
    rw [Category.assoc, s.2, Category.id_comp, ← Spec.map_comp, CommRingCat.ofHom_comp])

end DRLevel

open DRLevel

structure DRModelPackageLevel (hqN : ¬ q ∣ N₀) where

  [isProper : IsProper (toBase N₀ q)]
  [flat : Flat (toBase N₀ q)]
  [isIntegral : IsIntegral (X N₀ q)]
  [lfp : LocallyOfFinitePresentation (toBase N₀ q)]

  normal : ∀ U : (X N₀ q).Opens, IsAffineOpen U → IsIntegrallyClosed Γ(X N₀ q, U)

  Meta : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * q))
  eeta : Meta.C ⟶ pullback (toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) (AlgebraicClosure ℚ))))
  [eeta_iso : IsIso eeta]
  heeta : eeta ≫ pullback.snd _ _ = Meta.toBase

  hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta.C // s ≫ Meta.toBase = 𝟙 _}),
      x'.1 ≫ eeta ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ eeta ≫ pullback.fst _ _ →
      Meta.pointEquivPlace x' = arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * q)) g • Meta.pointEquivPlace x

  [Meta_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eeta ≫ pullback.fst (toBase N₀ q)
      (Spec.map (CommRingCat.ofHom (algebraMap (R q) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))]
  Meta_pin : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
    ((Meta.ffEquiv.symm
        (Meta.C.germToFunctionField
          ((eeta ≫ pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
            ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
          (((eeta ≫ pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) (AlgebraicClosure ℚ))))).app
              ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom
            (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))))
        : ↥(modularFunctionFieldBar (N₀ * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ)

  smooth_generic : SmoothOfRelativeDimension 1 (pullback.snd (toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) ℚ))))
  geomIntegral_generic : GeometricallyIntegral (pullback.snd (toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) ℚ))))

  εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q)
  εzero : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q)

  rhoInf : ↥(IgusaScheme.chartAlgInf (N₀ * q) q) →ₐ[R q] R q
  rhoInf_spec : ∀ b : ↥(IgusaScheme.chartAlgInf (N₀ * q) q),
    ((rhoInf b : R q) : ℚ) = ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ).coeff 0
  εinf_chart : εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ IgusaScheme.ιInf (N₀ * q) q

  w : X N₀ q ≅ X N₀ q
  w_over : w.hom ≫ toBase N₀ q = toBase N₀ q
  w_invol : w.hom ≫ w.hom = 𝟙 _
  w_sections : εinf.1 ≫ w.hom = εzero.1

  theta : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ≃ₐ[R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)
  theta_spec : ∀ b, ((theta b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) =
    atkinLehnerInvolutionFull N₀ q (b : ↥(modularFunctionFieldFull (N₀ * q)))
  w_chart : IgusaScheme.ιFin (N₀ * q) q ≫ w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q

  π : SchemeHomOver (toBase N₀ q) (toBase0 N₀ q)
  iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)
  iota0_spec : ∀ b, (((iota0 b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
    ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ)
  pi_chart : IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ IgusaScheme.ιFin N₀ q

  smoothLocus : (X N₀ q).Opens
  [smoothLocus_relDim : SmoothOfRelativeDimension 1 (smoothLocus.ι ≫ toBase N₀ q)]
  smoothLocus_maximal : ∀ U : (X N₀ q).Opens, Smooth (U.ι ≫ toBase N₀ q) → U ≤ smoothLocus
  εinf_mem_smoothLocus : Set.range εinf.1.base ⊆ (smoothLocus : Set (X N₀ q))
  εzero_mem_smoothLocus : Set.range εzero.1.base ⊆ (smoothLocus : Set (X N₀ q))

  fibre_reduced : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    IsReduced (fibre (N₀ := N₀) toκ)

  Mfib : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    CurveModel κ ↥(modularFunctionFieldC κ N₀)
  efib : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    (Mfib κ toκ).C ⟶ fibre0 (N₀ := N₀) toκ
  efib_iso : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ), IsIso (efib κ toκ)
  hefib : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    efib κ toκ ≫ pullback.snd _ _ = (Mfib κ toκ).toBase

  [Mfib_chart_nonempty : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    Nonempty (Scheme.Opens.toScheme ((efib κ toκ ≫ pullback.fst (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ
      ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
  Mfib_pin : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ)
    (b : ↥(IgusaScheme.chartAlgFin N₀ q)),
    let readb : ↥(modularFunctionFieldC κ N₀) :=
      (Mfib κ toκ).ffEquiv.symm
        ((Mfib κ toκ).C.germToFunctionField
          ((efib κ toκ ≫ pullback.fst (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
          (((efib κ toκ ≫ pullback.fst (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
            (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
    ((b = IgusaScheme.jChartFin N₀ q → readb = jGeomGen κ N₀) ∧
      (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb = jNGeomGen κ N₀))

  comp : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    Fin 2 → (fibre0 (N₀ := N₀) toκ ⟶ fibre (N₀ := N₀) toκ)
  comp_over : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ) (i : Fin 2),
    comp κ toκ i ≫ pullback.snd _ _ = pullback.snd _ _
  comp_isClosedImmersion : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ) (i : Fin 2),
    IsClosedImmersion (comp κ toκ i)
  comp_jointly_surjective : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ)
    (y : fibre (N₀ := N₀) toκ), y ∈ Set.range (comp κ toκ 0).base ∨ y ∈ Set.range (comp κ toκ 1).base
  range_comp_ne : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    Set.range (comp κ toκ 0).base ≠ Set.range (comp κ toκ 1).base

  comp_pi : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    comp κ toκ 0 ≫ fibreMap0 π toκ = 𝟙 _

  comp1_pi_place : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ)
    (P : closedPoints (Mfib κ toκ).C),
    ∃ h : (inv (efib κ toκ)).base ((efib κ toκ ≫ comp κ toκ 1 ≫ fibreMap0 π toκ).base P.1) ∈ closedPoints (Mfib κ toκ).C,
      (Mfib κ toκ).placeOfPoint ⟨_, h⟩ = arithFrobC q κ N₀ • (Mfib κ toκ).placeOfPoint P

  comp_w : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    comp κ toκ 0 ≫ fibreMap w.hom w_over toκ = comp κ toκ 1

  εinf_mem_comp0 : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    Set.range (sectionFibre εinf toκ).base ⊆ Set.range (comp κ toκ 0).base
  εzero_mem_comp1 : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    Set.range (sectionFibre εzero toκ).base ⊆ Set.range (comp κ toκ 1).base

  crossing_reduced : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    IsReduced (pullback (comp κ toκ 0) (comp κ toκ 1))
  nodeEquiv : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    ↥(pullback (comp κ toκ 0) (comp κ toκ 1)) ≃ ↥(ssPlaces q N₀ κ)

  node_pin : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ)
    (n : ↥(pullback (comp κ toκ 0) (comp κ toκ 1))),
    (∃ h : (inv (efib κ toκ)).base ((pullback.fst (comp κ toκ 0) (comp κ toκ 1)).base n) ∈ closedPoints (Mfib κ toκ).C,
        (Mfib κ toκ).placeOfPoint ⟨_, h⟩ = ((nodeEquiv κ toκ n : ↥(ssPlaces q N₀ κ)) : Place κ ↥(modularFunctionFieldC κ N₀))) ∧
    (∃ h : (inv (efib κ toκ)).base ((pullback.snd (comp κ toκ 0) (comp κ toκ 1)).base n) ∈ closedPoints (Mfib κ toκ).C,
        (Mfib κ toκ).placeOfPoint ⟨_, h⟩ =
          arithFrobC q κ N₀ • ((nodeEquiv κ toκ n : ↥(ssPlaces q N₀ κ)) : Place κ ↥(modularFunctionFieldC κ N₀)))

  iotaInf : ↥(IgusaScheme.chartAlgInf N₀ q) →ₐ[R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q)
  iotaInf_spec : ∀ b, (((iotaInf b : ↥(IgusaScheme.chartAlgInf (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
    ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ)
  pi_chartInf : IgusaScheme.ιInf (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫ IgusaScheme.ιInf N₀ q

  εinf0_comp0 : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    (sectionFibre εinf toκ ≫ fibreMap0 π toκ) ≫ comp κ toκ 0 = sectionFibre εinf toκ

  εinf0_comp1 : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ),
    (sectionFibre εinf toκ ≫ fibreMap0 π toκ) ≫ comp κ toκ 1 = sectionFibre εzero toκ

attribute [instance] DRModelPackageLevel.eeta_iso DRModelPackageLevel.smoothLocus_relDim
  DRModelPackageLevel.efib_iso DRModelPackageLevel.Mfib_chart_nonempty

namespace DRModelPackageLevel

variable {N₀ q} {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)

abbrev width {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ)
    (n : ↥(pullback (𝔛.comp κ toκ 0) (𝔛.comp κ toκ 1))) : ℕ :=
  placeWidthChar q N₀ ((𝔛.nodeEquiv κ toκ n : ↥(ssPlaces q N₀ κ)) : Place κ ↥(modularFunctionFieldC κ N₀))

def πw : SchemeHomOver (toBase N₀ q) (toBase0 N₀ q) :=
  ⟨𝔛.w.hom ≫ 𝔛.π.1, by rw [Category.assoc, 𝔛.π.2, 𝔛.w_over]⟩

@[simp] theorem πw_val : 𝔛.πw.1 = 𝔛.w.hom ≫ 𝔛.π.1 := rfl

abbrev εinf0 {κ : Type} [CommRing κ] (toκ : R q →+* κ) :=
  sectionFibre 𝔛.εinf toκ ≫ fibreMap0 𝔛.π toκ

end DRModelPackageLevel

end ModularCurve

end


