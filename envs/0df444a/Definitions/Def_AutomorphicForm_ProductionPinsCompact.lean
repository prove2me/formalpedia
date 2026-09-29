-- Prove2me | Definitions.Def_AutomorphicForm_ProductionPinsCompact
-- name    : AutomorphicForm_ProductionPinsCompact
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/34bf7574-5d02-5694-9733-b1a18a9b3ad8
-- title:
--   Production carrier pins with archimedean-trivial level subgroups
-- statement:
--   For a number field $F$ this module defines `productionPinsCompact F : CarrierPins F`, a package of the data on which the project's automorphy predicates are evaluated. `CarrierPins F` is a structure bundling a measurable space `mS` and a measure `μ` on $\mathrm{GL}_2(\mathbb{A}_F)$, a set `D` in that group, a subgroup `Z` of the idele units, a map `U` from ideals of $\mathcal{O}_F$ to subgroups of $\mathrm{GL}_2(\mathbb{A}_F)$, a map `gen` from finite places to group elements, and a measurable space `nS` with a measure `ν` on $\mathbb{A}_F$. The instance is obtained from `productionPinsOf`, so `mS` and `nS` are the Borel structures, `μ` is the Haar measure `adelicGLHaar`, `Z` is the full group $\top$, and `ν` is the additive Haar measure on $\mathbb{A}_F$ conditioned (via `ProbabilityTheory.cond`) on the fundamental box `adelicBox F`; the chosen slots are `D` the centre-cut Siegel set with parameters $(1/2,1,1/2,2)$, `gen v` the Hecke element $\mathrm{diag}(\pi_v,1)$ at $v$ and $1$ elsewhere, and `U N = levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F`. Since `levelOne N` constrains only the finite component — the finite part of $g$ and of $g^{-1}$ must have integral entries, lower-left entry in the $N$-ball and lower-right entry congruent to $1$ — it contains the whole archimedean factor; intersecting with `finiteAdelicGL2Subgroup F`, the kernel of the archimedean projection `glArch`, cuts this out, leaving exactly the elements with archimedean part $1$ and finite part in `finiteLevelOne N`. This is the only slot in which `productionPinsCompact F` differs from `productionPins F`. The accompanying lemmas record the eight slot values by `rfl`, the two membership consequences ($\mathrm{glFin}\,u \in$ `finiteLevelOne N`, $\mathrm{glArch}\,u = 1$), the identity `U N = (productionPins F).U N ⊓ finiteAdelicGL2Subgroup F` with the resulting inclusion, and the transfer of the measure-theoretic facts: `μ` is Haar, `ν` is a probability measure, `D` is measurable and $0 < \mu(D) < \infty$.
--
--   **Relation to Mathlib.** `CarrierPins`, `productionPinsOf`, `levelOne`, `heckeGen` and `finiteAdelicGL2Subgroup` are the project's own notions; the measures in the slots are Mathlib's `Measure.haar` and `Measure.addHaar` on the Borel structures, the latter conditioned with Mathlib's `ProbabilityTheory.cond`.
--
--   **Where it is used.** These pins supply the data at which the project's predicates `IsSmoothAutomorphicFnAt` and `IsSmoothCuspAutomorphicFnAt` are instantiated: square-integrability is imposed on the centre-cut Siegel set `D`, cuspidality through the constant-term integral against the probability measure `ν`, and smoothness through invariance under the level subgroups `U N`, which here lie in the finite part of the group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ProductionPinsCompact.lean

import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.SiegelVolume

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def productionPinsCompact : CarrierPins F :=
  productionPinsOf F
    (centreCutSiegelSet F (1/2 : ℝ) 1 (1/2) 2)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

@[simp] theorem productionPinsCompact_mS :
    (productionPinsCompact F).mS = glBorel (Fin 2) (𝓞 F) F := rfl

@[simp] theorem productionPinsCompact_μ :
    (productionPinsCompact F).μ = adelicGLHaar (Fin 2) (𝓞 F) F := rfl

@[simp] theorem productionPinsCompact_D :
    (productionPinsCompact F).D = centreCutSiegelSet F (1/2 : ℝ) 1 (1/2) 2 := rfl

@[simp] theorem productionPinsCompact_Z :
    (productionPinsCompact F).Z = (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) := rfl

@[simp] theorem productionPinsCompact_U (N : Ideal (𝓞 F)) :
    (productionPinsCompact F).U N = levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := rfl

@[simp] theorem productionPinsCompact_gen (v : HeightOneSpectrum (𝓞 F)) :
    (productionPinsCompact F).gen v = heckeGen (𝓞 F) F v := rfl

@[simp] theorem productionPinsCompact_nS :
    (productionPinsCompact F).nS = adeleBorel (𝓞 F) F := rfl

@[simp] theorem productionPinsCompact_ν :
    (productionPinsCompact F).ν =
      @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F) :=
  rfl

theorem productionPinsCompact_μ_eq_productionPins_μ :
    (productionPinsCompact F).μ = (productionPins F).μ := rfl

theorem productionPinsCompact_D_eq_productionPins_D :
    (productionPinsCompact F).D = (productionPins F).D := rfl

theorem productionPinsCompact_ν_eq_productionPins_ν :
    (productionPinsCompact F).ν = (productionPins F).ν := rfl

theorem glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U (N : Ideal (𝓞 F))
    {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ (productionPinsCompact F).U N) :
    glFin (𝓞 F) F u ∈ finiteLevelOne (𝓞 F) F N :=
  hu.1

theorem glArch_eq_one_of_mem_productionPinsCompact_U (N : Ideal (𝓞 F))
    {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ (productionPinsCompact F).U N) :
    glArch (𝓞 F) F u = 1 :=
  hu.2

theorem productionPinsCompact_U_eq_productionPins_U_inf (N : Ideal (𝓞 F)) :
    (productionPinsCompact F).U N = (productionPins F).U N ⊓ finiteAdelicGL2Subgroup F := rfl

theorem productionPinsCompact_U_le_productionPins_U (N : Ideal (𝓞 F)) :
    (productionPinsCompact F).U N ≤ (productionPins F).U N := inf_le_left

theorem isHaarMeasure_productionPinsCompact_μ :
    @Measure.IsHaarMeasure _ _ _ (productionPinsCompact F).mS (productionPinsCompact F).μ :=
  isHaarMeasure_productionPins_μ F

theorem isProbabilityMeasure_productionPinsCompact_ν :
    @IsProbabilityMeasure _ (productionPinsCompact F).nS (productionPinsCompact F).ν :=
  isProbabilityMeasure_productionPins_ν F

theorem measurableSet_productionPinsCompact_D :
    @MeasurableSet _ (productionPinsCompact F).mS (productionPinsCompact F).D :=
  measurableSet_productionPins_D F

theorem productionPinsCompact_μ_D_pos_lt_top :
    (letI := (productionPinsCompact F).mS;
      0 < (productionPinsCompact F).μ (productionPinsCompact F).D ∧
        (productionPinsCompact F).μ (productionPinsCompact F).D < ⊤) :=
  productionPins_μ_D_pos_lt_top F

end AutomorphicForm

end


