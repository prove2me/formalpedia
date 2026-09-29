-- Prove2me | Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
-- name    : ModularCurve_JZeroNeronObjectAtP_LevelModel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/a9f0302a-5db8-5e6f-931e-355d47ba5a79
-- title:
--   Level model: Igusa curve, Picard representability, point dictionaries
-- statement:
--   Fix $N_0\ge 1$, a prime $p$ and a valuation subring $A$ of $\overline{\mathbf Q}$. The structure `LevelModel N₀ p A` is the data of a model of $J_0(N_0)$ over $\mathbf Z_{(p)}$ (written here as `baseRing p`, the rationals with denominator coprime to $p$) presented as a representing object for the relative Picard functor of the Igusa scheme. Its fields are: a ring map $\rho$ from $\mathbf Z_{(p)}$ to $A$ whose composite with the inclusion $A\hookrightarrow\overline{\mathbf Q}$ is the structure map; the assumption that `IgusaScheme.igusaTo N₀ p` (the Igusa scheme, glued from the two charts of integral elements over $\mathbf Z_{(p)}[j]$ and $\mathbf Z_{(p)}[j^{-1}]$ inside the full modular function field) is proper; a $\mathbf Z_{(p)}$-algebra map $\varphi_\infty$ on the $j^{-1}$-chart whose value on $x$ is the $0$-th Laurent coefficient of the $q$-expansion of $x$, and a section $\varepsilon_0$ of the Igusa scheme over $\mathbf Z_{(p)}$ which is $\operatorname{Spec}\varphi_\infty$ followed by the inclusion of that chart, i.e. the cusp $\infty$; a pointed $\mathbf Z_{(p)}$-scheme $D_0$ (carrier `D₀.P`, structure morphism `D₀.toBase`, zero section `D₀.zeroSection`) together with `rep`, the datum of a Poincaré bundle on $D_0$ making $D_0$ represent the subfunctor of $\varepsilon_0$-rigidified invertible modules on the Igusa scheme which are fibrewise algebraically equivalent to zero (the condition `algEquivZeroCut`: over every algebraically closed field point of the base there is a geometrically integral finite-type parameter scheme interpolating between the trivial bundle and the given one); an Abel–Jacobi morphism $\mathrm{aj}_0$ over $\mathbf Z_{(p)}$ carrying $\varepsilon_0$ to the zero section, whose defining property `haj₀` is that for every field-valued point $x$ of the Igusa scheme the pullback of the Poincaré bundle along $x$ followed by $\mathrm{aj}_0$ is isomorphic to $\mathcal O(\Gamma_x)\otimes\mathcal I_{\varepsilon_0}$, the tensor product of the dual ideal module of the relative effective Cartier divisor of $x$ with the ideal module of the divisor of $\varepsilon_0$; two dictionaries `pts` and `ptsSp`, bijections of $J_0(N_0)$ with the $\overline{\mathbf Q}$-points of $D_0$ over the generic point, and of the degree-zero class group of the level-$N_0$ function field over the residue field of $A$ with the points of $D_0$ over $\operatorname{Spec}$ of the residue map composed with $\rho$; and finally a smooth proper curve model `Meta₀` of $\overline{\mathbf Q}(X_0(N_0))$ over $\overline{\mathbf Q}$ together with an isomorphism $\eta_0$ onto the geometric generic fibre of the Igusa scheme compatible with the structure morphisms, normalised by `Meta₀_pin` (elements of the $j$-chart are read in the function field by their $q$-expansions, coefficients embedded into $\overline{\mathbf Q}$) and by `pts_aj` (for points $x$ and $s$ of the model with $s$ sitting over the cusp $\varepsilon_0$, the class of the degree-zero divisor $[x]-[s]$ corresponds under `pts` to $x$ followed by $\eta_0$ and $\mathrm{aj}_0$).
--
--   The accompanying declarations extract from such a model the structure morphism `σA` of the place, the induced map `toκ` to the residue field, the identity `barPt_σA` expressing that `σA` pulled back along $\operatorname{Spec}(A\hookrightarrow\overline{\mathbf Q})$ is the geometric generic point, the relative group law `law` on $D_0$ obtained from the representability datum for the group-theoretic form of the algebraic-equivalence-zero condition, and `toLevelData`, which forgets everything except the place, the scheme $D_0$ with that group law and the two dictionaries, producing a `LevelData N₀ p A`.
--
--   **Relation to Mathlib.** Mathlib has no relative Picard functor, Jacobian or Néron model of a curve; the notions assembled here — rigidified line bundles and their classes, representability of the algebraic-equivalence-zero subfunctor, relative effective Cartier divisors and their ideal and line bundle modules, curve models with their place dictionaries, and the Igusa scheme itself — are the project's own, built on Mathlib's schemes and sheaves of modules.
--
--   **Where it is used.** This is the level-$N_0$ input for the construction of the Néron model of $J_0(N_0p)$ at $p$: because $D_0$ represents the relative Picard functor, the two degeneracy maps $X_0(N_0p)\rightrightarrows X_0(N_0)$ and the components of the special fibre of the Deligne–Rapoport model give rise to morphisms into $D_0$, which enter the analysis of the $p$-adic behaviour of $J_0(N_0p)$ used in Ribet's level-lowering and Mazur's principle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroNeronObjectAtP_LevelModel.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing AlgebraicGeometry.RelPicard

noncomputable section

namespace ModularCurve.JZeroNeronObjectAtP

structure LevelModel (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) where

  ρ : baseRing p →+* ↥A

  hρ : A.subtype.comp ρ = algebraMap (baseRing p) (AlgebraicClosure ℚ)

  [proper₀ : IsProper (IgusaScheme.igusaTo N₀ p)]

  φinf : ↥(IgusaScheme.chartAlgInf N₀ p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p)
  φinf_spec : ∀ x : ↥(IgusaScheme.chartAlgInf N₀ p),
    ((φinf x : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) =
      ((x : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ).coeff 0

  ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) (IgusaScheme.igusaTo N₀ p)

  ε₀_chart : ε₀.1 = Spec.map (CommRingCat.ofHom φinf.toRingHom) ≫ IgusaScheme.ιInf N₀ p

  D₀ : RelativePic0Designation (baseRing p) (IgusaScheme.igusaTo N₀ p)

  rep : RepresentsRelSubPic (IgusaScheme.igusaTo N₀ p) ε₀ (algEquivZeroCut (IgusaScheme.igusaTo N₀ p) ε₀) D₀

  aj₀ : SchemeHomOver (IgusaScheme.igusaTo N₀ p) D₀.toBase

  haj₀ε : ε₀.1 ≫ aj₀.1 = D₀.zeroSection

  haj₀ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ base p)
      (x : SchemeHomOver t (IgusaScheme.igusaTo N₀ p)),
    Nonempty ((rep.poincare.pullbackAlong
        ⟨x.1 ≫ aj₀.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj₀.2).trans x.2)⟩).L ≅
      (RelEffCartierDiv.ofPoint (IgusaScheme.igusaTo N₀ p) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (IgusaScheme.igusaTo N₀ p) (t ≫ ε₀.1)
          ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε₀.2).trans (Category.comp_id t)))).idealModule)

  pts : JZero N₀ ≃ SchemeHomOver (genPt p) D₀.toBase

  ptsSp : JZeroC (ResidueField ↥A) N₀ ≃ SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase

  Meta₀ : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N₀)
  eeta₀ : Meta₀.C ⟶ pullback (IgusaScheme.igusaTo N₀ p) (genPt p)
  [eeta₀_iso : IsIso eeta₀]
  heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase

  [Meta₀_chart_nonempty : Nonempty (Scheme.Opens.toScheme
      ((eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ p) ''ᵁ ⊤)))]

  Meta₀_pin : ∀ a : ↥(IgusaScheme.chartAlgFin N₀ p),
    ((Meta₀.ffEquiv.symm
        (Meta₀.C.germToFunctionField
          ((eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ p) ''ᵁ ⊤))
          (((eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p)).app ((IgusaScheme.ιFin N₀ p) ''ᵁ ⊤)).hom
            (((IgusaScheme.ιFin N₀ p).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ p))).inv a))))
        : ↥(modularFunctionFieldBar N₀)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ)

  pts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
    s.1 ≫ eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) = genPt p ≫ ε₀.1 →
    ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N₀),
      (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N₀)) =
        Finsupp.single (Meta₀.pointEquivPlace x) 1 - Finsupp.single (Meta₀.pointEquivPlace s) 1 ∧
      (pts (Pic0.mk Dv)).1 = x.1 ≫ eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) ≫ aj₀.1

namespace LevelModel

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

attribute [instance] LevelModel.eeta₀_iso LevelModel.Meta₀_chart_nonempty

abbrev σA (M : LevelModel N₀ p A) : Spec (CommRingCat.of ↥A) ⟶ base p := Spec.map (CommRingCat.ofHom M.ρ)

abbrev toκ (M : LevelModel N₀ p A) : baseRing p →+* ResidueField ↥A := (residue ↥A).comp M.ρ

theorem barPt_σA (M : LevelModel N₀ p A) : barPt A ≫ M.σA = genPt p := by
  simp only [barPt, genPt, σA, ← Spec.map_comp, ← CommRingCat.ofHom_comp, M.hρ]

abbrev law (M : LevelModel N₀ p A) : RelativeGroupLaw (baseRing p) M.D₀.toBase :=
  RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (IgusaScheme.igusaTo N₀ p) M.ε₀) M.rep

def toLevelData (M : LevelModel N₀ p A) : LevelData N₀ p A where
  σA := M.σA
  hσA := M.barPt_σA
  X := M.D₀.P
  f := M.D₀.toBase
  L := M.law
  pts := M.pts
  ptsSp := M.ptsSp

end LevelModel

end ModularCurve.JZeroNeronObjectAtP

end


