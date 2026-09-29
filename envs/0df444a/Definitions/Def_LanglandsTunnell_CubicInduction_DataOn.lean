-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
-- name    : LanglandsTunnell_CubicInduction_DataOn
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/ff7d3094-25bd-56c6-b273-b16a9f8fa435
-- title:
--   Cubic induction data and the predicate on a place set
-- statement:
--   Over a number field $K$ whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, the structure `CubicInductionData` bundles, with no laws attached, the six pieces of data of a cubic induction form: a function `form` on $\mathrm{GL}_3$ of the adèles of $\mathbb{Q}$, a global Whittaker function `whittaker` on the same group, a family `whittakerLoc` of functions on $\mathrm{GL}_3(\mathbb{Q}_v)$ indexed by the finite places $v$, an archimedean Whittaker function on $\mathrm{GL}_3$ of the infinite adèle ring, a character `centralChar` of the idèles, and a dual Whittaker function. `CubicInductionForm.toData` forgets the laws of a `CubicInductionForm`. The Prop-valued structure `IsCubicInductionDataOn K pins ψ μ S X` then reasserts those laws of unbundled data $X$, with a set $S$ of finite places replacing the bad places of $(K,\mu)$: left invariance of `form` under $\mathrm{GL}_3(\mathbb{Q})$; transformation under central idèles by `centralChar`, which is trivial on principal idèles; vanishing of the two integrals of `form` over the unipotent radicals $P_{21}$, $P_{12}$ against `pins.ν`; the identification of `whittaker` with the triple integral $\iiint \mathrm{form}(u(x,y,z)g)\psi(-(x+y))$; the $\psi$-Whittaker law $W(u(x,y,z)g)=\psi(x+y)W(g)$ globally, locally for each `psiLoc ψ v`, and for $\psi^{-1}$ in the dual case; the summation of `whittaker` over mirabolic translates to `form` (and likewise for the dual of `form`, $g\mapsto \mathrm{form}({}^{t}g^{-1})$); factorisation of `whittaker` into the archimedean factor times a finite product of local factors over any finite $T\supseteq S$ with integral components off $T$; at places outside $S$, the induced spherical Hecke-eigen clause with eigenvalues built from `inducedCoeff K μ`, and, if moreover $v$ is unramified in $K$, right invariance under the congruence set `congruenceK1` of level `inducedLevelAt K μ v`; local Whittaker multiplicity one; moderate growth of `form`; $K$-finiteness of the archimedean factor; and the integral finiteness conditions `HasIotaMoments` and `HasWhittakerHalfPlane` over $\mathrm{GL}_2$ fundamental domains, with their duals.
--
--   Three comparisons follow. The data of any `CubicInductionForm` satisfy the predicate for every $S$ containing all bad places. Conversely, data satisfying the predicate for $S$ the set of bad places, together with the level invariance at every place unramified in $K$ — a hypothesis needed because the structure demands that clause at all unramified places, not only outside $S$ — arise as `toData` of a form. Finally, for the pins `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, the existence of a cubic induction form with non-zero `form` yields data with non-zero `form` satisfying the predicate for the bad places of $(K,\mu)$.
--
--   **Relation to Mathlib.** Mathlib supplies the adèle ring, general linear groups over a commutative ring, additive characters and Haar-theoretic infrastructure; automorphic forms on $\mathrm{GL}_3$, Whittaker functions and their local–global factorisation are the project's own notions.
--
--   **Where it is used.** These data package the $\mathrm{GL}_3$ automorphic object produced by induction from a cubic extension, in the form used for the Langlands–Tunnell step: the unbundled version allows the place set governing factorisation, sphericity and level to be enlarged or specialised while the laws are transported, before a converse theorem is applied to descend to $\mathrm{GL}_2$. In the route to Fermat's Last Theorem this is what makes the mod-$3$ representation attached to a Frey curve automorphic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_DataOn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm

noncomputable section

namespace LanglandsTunnell.CubicInduction

structure CubicInductionData where

  form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ

  whittaker : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ

  whittakerLoc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ

  whittakerArch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ

  centralChar : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ

  dualWhittaker : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ

def CubicInductionForm.toData {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (D : CubicInductionForm K pins ψ μ) : CubicInductionData where
  form := D.form
  whittaker := D.whittaker
  whittakerLoc := D.whittakerLoc
  whittakerArch := D.whittakerArch
  centralChar := D.centralChar
  dualWhittaker := D.dualWhittaker

structure IsCubicInductionDataOn (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (S : Set (HeightOneSpectrum (𝓞 ℚ))) (X : CubicInductionData) : Prop where
  automorphic : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
    X.form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = X.form g
  central : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
    X.form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (X.centralChar z : ℂ) * X.form g
  centralChar_ideleClass : IsIdeleClassChar (𝓞 ℚ) ℚ X.centralChar
  cuspidalP21 : IsCuspidalAlongP21 pins X.form
  cuspidalP12 : IsCuspidalAlongP12 pins X.form
  whittaker_eq : ∀ g, X.whittaker g = whittaker3 pins ψ X.form g
  whittaker_law : IsGL3PsiWhittakerFn ψ X.whittaker
  expansion : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    HasSum (fun i : MirabolicIndex ℚ => X.whittaker (mirabolicTranslate i * g)) (X.form g)
  whittakerLoc_law : ∀ v, IsGL3PsiWhittakerFn (psiLoc ψ v) (X.whittakerLoc v)
  factorizable : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))),
    (∀ v, v ∈ S → v ∈ T) →
    (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
    X.whittaker g = X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) *
      ∏ v ∈ T, X.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v g)
  spherical : ∀ v, v ∉ S →
    IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) (X.whittakerLoc v)
  levelInvariant : ∀ v, v ∉ S → ¬ IsRamifiedIn K v →
    ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, X.whittakerLoc v (g * k) = X.whittakerLoc v g
  multOne : ∀ v, HasWhittakerMultOne (psiLoc ψ v) (X.whittakerLoc v)
  moderateGrowth : IsModerateGrowth3 ℚ X.form
  kFinite : IsKFinite X.whittakerArch
  iotaMoments : HasIotaMoments X.form
  whittakerHalfPlane : HasWhittakerHalfPlane X.whittaker
  dualWhittaker_eq : ∀ g, X.dualWhittaker g = whittaker3 pins ψ⁻¹ (dualForm X.form) g
  dualWhittaker_law : IsGL3PsiWhittakerFn ψ⁻¹ X.dualWhittaker
  dual_expansion : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    HasSum (fun i : MirabolicIndex ℚ => X.dualWhittaker (mirabolicTranslate i * g)) (dualForm X.form g)
  dual_iotaMoments : HasIotaMoments (dualForm X.form)
  dual_whittakerHalfPlane : HasWhittakerHalfPlane X.dualWhittaker

theorem CubicInductionForm.isCubicInductionDataOn {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (D : CubicInductionForm K pins ψ μ)
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) (hS : ∀ v, IsBadPlace K μ v → v ∈ S) :
    IsCubicInductionDataOn K pins ψ μ S D.toData :=
  { automorphic := D.automorphic, central := D.central, centralChar_ideleClass := D.centralChar_ideleClass,
    cuspidalP21 := D.cuspidalP21, cuspidalP12 := D.cuspidalP12, whittaker_eq := D.whittaker_eq,
    whittaker_law := D.whittaker_law, expansion := D.expansion, whittakerLoc_law := D.whittakerLoc_law,
    factorizable := fun g T hT hg => D.factorizable g T (fun v hv => hT v (hS v hv)) hg,
    spherical := fun v hv => D.spherical v (fun hb => hv (hS v hb)),
    levelInvariant := fun v _ hram => D.levelInvariant v hram, multOne := D.multOne,
    moderateGrowth := D.moderateGrowth, kFinite := D.kFinite, iotaMoments := D.iotaMoments,
    whittakerHalfPlane := D.whittakerHalfPlane, dualWhittaker_eq := D.dualWhittaker_eq,
    dualWhittaker_law := D.dualWhittaker_law, dual_expansion := D.dual_expansion,
    dual_iotaMoments := D.dual_iotaMoments, dual_whittakerHalfPlane := D.dual_whittakerHalfPlane }

theorem IsCubicInductionDataOn.exists_cubicInductionForm_toData_eq {K : Type} [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {Y : CubicInductionData}
    (hY : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} Y)
    (hlevel : ∀ v, ¬ IsRamifiedIn K v →
      ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, Y.whittakerLoc v (g * k) = Y.whittakerLoc v g) :
    ∃ D : CubicInductionForm K pins ψ μ, D.toData = Y :=
  ⟨{ form := Y.form, whittaker := Y.whittaker, whittakerLoc := Y.whittakerLoc,
     whittakerArch := Y.whittakerArch, centralChar := Y.centralChar, dualWhittaker := Y.dualWhittaker,
     automorphic := hY.automorphic, central := hY.central, centralChar_ideleClass := hY.centralChar_ideleClass,
     cuspidalP21 := hY.cuspidalP21, cuspidalP12 := hY.cuspidalP12, whittaker_eq := hY.whittaker_eq,
     whittaker_law := hY.whittaker_law, expansion := hY.expansion, whittakerLoc_law := hY.whittakerLoc_law,
     factorizable := fun g T hT hg => hY.factorizable g T (fun v hv => hT v hv) hg,
     spherical := fun v hv => hY.spherical v hv, levelInvariant := hlevel, multOne := hY.multOne,
     moderateGrowth := hY.moderateGrowth, kFinite := hY.kFinite, iotaMoments := hY.iotaMoments,
     whittakerHalfPlane := hY.whittakerHalfPlane, dualWhittaker_eq := hY.dualWhittaker_eq,
     dualWhittaker_law := hY.dualWhittaker_law, dual_expansion := hY.dual_expansion,
     dual_iotaMoments := hY.dual_iotaMoments, dual_whittakerHalfPlane := hY.dual_whittakerHalfPlane }, rfl⟩

theorem exists_isCubicInductionDataOn_productionPinsOf_of_exists_form_ne_zero
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (h : ∃ Φ : CubicInductionForm K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ, Φ.form ≠ 0) :
    ∃ X : CubicInductionData,
      IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X ∧
        X.form ≠ 0 := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨Φ.toData, Φ.isCubicInductionDataOn _ (fun _ hv => hv), hΦ⟩

end LanglandsTunnell.CubicInduction

end


