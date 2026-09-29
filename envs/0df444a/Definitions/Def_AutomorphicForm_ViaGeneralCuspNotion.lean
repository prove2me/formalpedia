-- Prove2me | Definitions.Def_AutomorphicForm_ViaGeneralCuspNotion
-- name    : AutomorphicForm_ViaGeneralCuspNotion
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/05fdd5ac-5b90-5cf0-8171-6301e1862c95
-- title:
--   General-pins cuspidality notion for Z[−2​]-valued eigensystems
-- statement:
--   The module defines [`AutomorphicForm.viaGeneralCuspNotion`](../def/AutomorphicForm_ViaGeneralCuspNotion.html#L12), a bundled cuspidality notion for Hecke eigensystems with coefficients in $\mathbb{Z}[\sqrt{-2}]$: for a number field $F$ and $\Phi$ a `HeckeEigensystem F (ℤ√(-2))`, the predicate `viaGeneralCuspNotion.IsCusp F Φ` is the conjunction of two clauses. The first asks for a realization $R$ of the complexified eigensystem — $\Phi$ pushed along the ring homomorphism `iotaZsqrtdNegTwo` sending $\sqrt{-2}\mapsto \sqrt2\,i$, then put into the raw central normalisation `toRawCentral`, which rescales the second family of eigenvalues by $(\mathrm{N}v)^{-1}$ — as a `SmoothCuspRealizationAt` at the carrier pins `productionPinsGeneral F`, subject to three conditions on that one $R$: `IsGenuineCuspRealizationAt`, which unfolds to continuity of the underlying function `R.toFun` on $\mathrm{GL}_2$ of the adeles; at every real infinite place $w$ of $F$, the archimedean transformation law `HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun`; and, at every real place, `IsArchHolomorphicAt`, i.e. for every adelic $g$ the function $z\mapsto (\operatorname{Im} z)^{-1}\,R.\mathrm{toFun}\bigl(g\cdot \iota_w\bigl(\begin{smallmatrix} y & x\\ 0 & 1\end{smallmatrix}\bigr)\bigr)$ is differentiable on the upper half-plane. The second clause asks for a finite set $S$ of height-one primes of $\mathcal{O}_F$ outside which $\Phi.b\,v$ equals the image in $\mathbb{Z}[\sqrt{-2}]$ of $\chi_{-3}(\mathrm{N}v)$.
--
--   The accompanying results are: `viaGeneralCuspNotion_isCusp_iff`, the definitional unfolding of the predicate; `isArithGenuineCuspRealizableVia_of_viaGeneralCuspNotion`, which extracts from it the realizability statement `IsArithGenuineCuspRealizableVia F (productionPinsGeneral F) iotaZsqrtdNegTwo Φ`; `not_ae_eq_zero_of_isGenuineCuspRealizationAt`, asserting for complex-valued $\Phi$ that a continuous realization at `productionPinsGeneral F` is not almost everywhere zero for the Haar measure of those pins, by positivity of Haar measure on nonempty open sets together with the nonvanishing field `R.exists_ne_zero`; and `viaCompactCuspNotion_isCusp_of_viaGeneralCuspNotion`, which, when the class number of $F$ is odd, deduces `viaCompactCuspNotion.IsCusp F Φ`, the two pin bundles then coinciding since the class-representative Siegel covering collapses to the single centre-cut Siegel set. In that last implication the continuity component is discarded, the compact notion not requiring it.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient ingredients (adele and finite adele rings, $\mathrm{GL}_2$ as `Matrix.GeneralLinearGroup`, Haar measure, the upper half-plane and manifold differentiability, class groups), but has no notion of adelic automorphic form or of cuspidality; the cuspidality notions, carrier pins and realization structures used here are the project's own.
--
--   **Where it is used.** These are the cuspidality conditions imposed on the $\mathbb{Z}[\sqrt{-2}]$-valued Hecke eigensystems handled by the project, formulated over an arbitrary number field by replacing the single centre-cut Siegel set by a union of translates indexed by ideal classes modulo squares, and normalised away from finitely many primes by the quadratic character $\chi_{-3}$. The comparison with the odd-class-number version lets statements proved for the compact pins be transported to the general setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ViaGeneralCuspNotion.lean

import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField EisensteinWeightOne CongruenceSubgroup

noncomputable section

namespace AutomorphicForm

def viaGeneralCuspNotion : CuspidalityNotion (ℤ√(-2)) where
  IsCusp := fun F _i1 _i2 Φ =>
    (∃ R : SmoothCuspRealizationAt F (productionPinsGeneral F)
        ((Φ.map iotaZsqrtdNegTwo).toRawCentral),
      IsGenuineCuspRealizationAt F (productionPinsGeneral F)
          ((Φ.map iotaZsqrtdNegTwo).toRawCentral) R ∧
      (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
        HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun) ∧
      (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
        IsArchHolomorphicAt w hw R.toFun)) ∧
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
      Φ.b v = ((chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))

theorem viaGeneralCuspNotion_isCusp_iff {F : Type} [Field F] [NumberField F]
    (Φ : HeckeEigensystem F (ℤ√(-2))) :
    viaGeneralCuspNotion.IsCusp F Φ ↔
      (∃ R : SmoothCuspRealizationAt F (productionPinsGeneral F)
          ((Φ.map iotaZsqrtdNegTwo).toRawCentral),
        IsGenuineCuspRealizationAt F (productionPinsGeneral F)
            ((Φ.map iotaZsqrtdNegTwo).toRawCentral) R ∧
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
          HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun) ∧
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
          IsArchHolomorphicAt w hw R.toFun)) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
        Φ.b v = ((chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))) :=
  Iff.rfl

theorem isArithGenuineCuspRealizableVia_of_viaGeneralCuspNotion {F : Type} [Field F]
    [NumberField F] (Φ : HeckeEigensystem F (ℤ√(-2)))
    (h : viaGeneralCuspNotion.IsCusp F Φ) :
    IsArithGenuineCuspRealizableVia F (productionPinsGeneral F) iotaZsqrtdNegTwo Φ :=
  ⟨h.1.choose, h.1.choose_spec.1⟩

open MeasureTheory in

theorem not_ae_eq_zero_of_isGenuineCuspRealizationAt {F : Type} [Field F] [NumberField F]
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F (productionPinsGeneral F) Φ)
    (hR : IsGenuineCuspRealizationAt F (productionPinsGeneral F) Φ R) :
    ¬ (∀ᵐ g ∂(productionPinsGeneral F).μ, R.toFun g = 0) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := (productionPinsGeneral F).mS
  haveI : Measure.IsHaarMeasure (productionPinsGeneral F).μ :=
    isHaarMeasure_productionPinsOf_μ F _ _ _ _
  intro hae
  obtain ⟨g, hg⟩ := R.exists_ne_zero
  exact hg (congrFun (Measure.eq_of_ae_eq hae hR continuous_const) g)

theorem viaCompactCuspNotion_isCusp_of_viaGeneralCuspNotion {F : Type} [Field F]
    [NumberField F] (hodd : Odd (classNumber F)) (Φ : HeckeEigensystem F (ℤ√(-2)))
    (h : viaGeneralCuspNotion.IsCusp F Φ) :
    viaCompactCuspNotion.IsCusp F Φ := by
  obtain ⟨hR, hS⟩ := h
  rw [productionPinsGeneral_eq_compact_of_odd F hodd] at hR
  obtain ⟨R, _, harch, hhol⟩ := hR
  exact ⟨⟨R, harch, hhol⟩, hS⟩

end AutomorphicForm

end


