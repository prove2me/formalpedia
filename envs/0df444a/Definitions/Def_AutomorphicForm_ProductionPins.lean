-- Prove2me | Definitions.Def_AutomorphicForm_ProductionPins
-- name    : AutomorphicForm_ProductionPins
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/d8455bd3-2af1-5f41-b813-41eb524a3320
-- title:
--   Explicit carrier data for adelic GL2​ automorphic forms
-- statement:
--   For a number field $F$, the project's structure [`AutomorphicForm.CarrierPins F`](../def/AutomorphicForm_CarrierPins.html#L10) bundles eight ambient data for automorphic forms on $G=\mathrm{GL}_2(\mathbb{A}_F)$ (written `AdelicGL2 (𝓞 F) F`): a measurable space `mS` and a measure `μ` on $G$, a set $D\subseteq G$, a subgroup $Z$ of the idele group $(\mathbb{A}_F)^\times$, a family $U$ of subgroups of $G$ indexed by ideals of $\mathcal O_F$, a family `gen` of elements of $G$ indexed by the finite places, and a measurable space `nS` and measure `ν` on $\mathbb{A}_F$. The definition `productionPins F` fills every slot by applying the constructor `productionPinsOf`: `mS` and `nS` are the Borel $\sigma$-algebras `glBorel (Fin 2) (𝓞 F) F` and `adeleBorel (𝓞 F) F`; `μ` is `adelicGLHaar (Fin 2) (𝓞 F) F` (Mathlib's `Measure.haar` for that Borel structure); $Z$ is the whole idele group $\top$; $U(N)=$ `levelOne (𝓞 F) F N` and $\mathrm{gen}(v)=$ `heckeGen (𝓞 F) F v`, the project's level subgroups and Hecke elements; $D$ is the centre-cut Siegel set `centreCutSiegelSet F (1/2) 1 (1/2) 2`, i.e. the set of $g$ whose finite part is integral and which satisfy, at every infinite place $w$, $1/2\le\mathrm{localHeight}$, $\mathrm{xWindowSq}\le 1$ and $\mathrm{archDetNorm}_w(g)\in[1/2,2]$, where $\mathrm{localHeight}(h)=\|\det h\|/(\|h_{10}\|^2+\|h_{11}\|^2)$; and $\nu$ is the adelic additive Haar measure conditioned on the box `adelicBox F` (the product of a fundamental domain for the lattice of integers at the infinite places with the integral finite adeles).
--
--   Eight `rfl` lemmas record these projections. The remaining results are the guards: `μ` is a Haar measure, `ν` is a probability measure (the box having positive finite adelic measure), $D$ is measurable, and $0<\mu(D)<\infty$, the parameter point $(1/2,1,1/2,2)$ meeting both the strict inequalities used for positivity and the positivity used for finiteness. No fundamental-domain or covering property of $D$, and no normalisation of $\mu$, is asserted.
--
--   **Relation to Mathlib.** `CarrierPins` and the Siegel set, level and Hecke data are the project's own; the measures are Mathlib's `Measure.haar` and `Measure.addHaar` for the Borel $\sigma$-algebras on $\mathrm{GL}_2(\mathbb{A}_F)$ and $\mathbb{A}_F$, with `ν` obtained by Mathlib's conditioning `ProbabilityTheory.cond`.
--
--   **Where it is used.** These explicit data are the ambient input against which the project's automorphic and cuspidal predicates on $\mathrm{GL}_2(\mathbb{A}_F)$ are formulated, in particular the square-integrability clause taken over the domain $D$; the module supplies one concrete choice valid for every number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ProductionPins.lean

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_SiegelVolume

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.SiegelVolume

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def productionPins : CarrierPins F :=
  productionPinsOf F
    (centreCutSiegelSet F (1/2 : ℝ) 1 (1/2) 2)
    (fun N => levelOne (𝓞 F) F N)
    (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

@[simp] theorem productionPins_mS :
    (productionPins F).mS = glBorel (Fin 2) (𝓞 F) F := rfl

@[simp] theorem productionPins_μ :
    (productionPins F).μ = adelicGLHaar (Fin 2) (𝓞 F) F := rfl

@[simp] theorem productionPins_D :
    (productionPins F).D = centreCutSiegelSet F (1/2 : ℝ) 1 (1/2) 2 := rfl

@[simp] theorem productionPins_Z :
    (productionPins F).Z = (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) := rfl

@[simp] theorem productionPins_U (N : Ideal (𝓞 F)) :
    (productionPins F).U N = levelOne (𝓞 F) F N := rfl

@[simp] theorem productionPins_gen (v : HeightOneSpectrum (𝓞 F)) :
    (productionPins F).gen v = heckeGen (𝓞 F) F v := rfl

@[simp] theorem productionPins_nS :
    (productionPins F).nS = adeleBorel (𝓞 F) F := rfl

@[simp] theorem productionPins_ν :
    (productionPins F).ν =
      @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F) :=
  rfl

theorem isHaarMeasure_productionPins_μ :
    @Measure.IsHaarMeasure _ _ _ (productionPins F).mS (productionPins F).μ :=
  isHaarMeasure_productionPinsOf_μ F _ _ _ _

theorem isProbabilityMeasure_productionPins_ν :
    @IsProbabilityMeasure _ (productionPins F).nS (productionPins F).ν :=
  isProbabilityMeasure_productionPinsOf_ν F _ _ _ _
    (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne

theorem measurableSet_productionPins_D :
    @MeasurableSet _ (productionPins F).mS (productionPins F).D := by
  letI := glBorel (Fin 2) (𝓞 F) F
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  exact measurableSet_centreCutSiegelSet (F := F) (1/2) 1 (1/2) 2

theorem productionPins_μ_D_pos_lt_top :
    (letI := (productionPins F).mS;
      0 < (productionPins F).μ (productionPins F).D ∧
        (productionPins F).μ (productionPins F).D < ⊤) :=
  adelicGLHaar_centreCutSiegelSet_pos_lt_top (F := F)
    (by norm_num) (by norm_num) one_ne_zero (by norm_num) (by norm_num) (by norm_num)

theorem productionPins_μ_D_pos :
    (letI := (productionPins F).mS; 0 < (productionPins F).μ (productionPins F).D) :=
  (productionPins_μ_D_pos_lt_top F).1

theorem productionPins_μ_D_lt_top :
    (letI := (productionPins F).mS; (productionPins F).μ (productionPins F).D < ⊤) :=
  (productionPins_μ_D_pos_lt_top F).2

end AutomorphicForm

end


