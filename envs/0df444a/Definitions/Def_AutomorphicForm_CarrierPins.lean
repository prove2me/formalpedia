-- Prove2me | Definitions.Def_AutomorphicForm_CarrierPins
-- name    : AutomorphicForm_CarrierPins
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/dff42e7f-1175-5373-a9d7-53e7a015c5ec
-- title:
--   Carrier pins: ambient data for adelic GL2​ automorphic forms
-- statement:
--   For a number field $F$ with ring of integers $\mathcal{O}_F$, adele ring $\mathbb{A}_F$ and $G =$ `AdelicGL2 (𝓞 F) F`, the structure [`AutomorphicForm.CarrierPins F`](../def/AutomorphicForm_CarrierPins.html#L10) bundles eight pieces of ambient data that the analytic clauses in a definition of an adelic automorphic form on $\mathrm{GL}_2$ quantify over implicitly: a measurable space structure `mS` on $G$ and a measure `μ` on $(G,\mathrm{mS})$; a subset `D ⊆ G` (the intended integration domain); a subgroup `Z ≤ (AdeleRing (𝓞 F) F)ˣ`; a map `U` from ideals of $\mathcal{O}_F$ to subgroups of $G$ (intended level subgroups); a map `gen` from the height-one spectrum of $\mathcal{O}_F$ to elements of $G$ (intended Hecke generators); and a measurable space structure `nS` on $\mathbb{A}_F$ together with a measure `ν` on it. The structure carries no axioms whatsoever: the fields are arbitrary, so any predicate stated over a `CarrierPins F` is a predicate on the chosen bundle, not on genuinely automorphic data.
--
--   The definition `productionPinsOf F D U gen B` fills five of the eight slots with canonical values and leaves three as arguments: `mS := glBorel (Fin 2) (𝓞 F) F`, `μ := adelicGLHaar (Fin 2) (𝓞 F) F`, `Z := ⊤` (the full unit group of $\mathbb{A}_F$), `nS := adeleBorel (𝓞 F) F`, and `ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) B`, the conditioning of the adelic additive Haar measure on a given subset $B \subseteq \mathbb{A}_F$; the fields `D`, `U`, `gen` are the corresponding arguments verbatim. Eight `rfl` lemmas record these projections. Two further lemmas state that the filled `μ` is a Haar measure on $G$ for the filled $\sigma$-algebra, and that the filled `ν` is a probability measure provided $\mathrm{adelicAddHaar}(B)$ is neither $0$ nor $\infty$. Nothing here asserts what the domain $D$, the level subgroups $U$ or the Hecke generators `gen` should be.
--
--   **Relation to Mathlib.** Mathlib has no notion of adelic automorphic form on $\mathrm{GL}_2$ or of such a bundle of ambient data; `CarrierPins` is the project's own. Its measure-theoretic slots are filled by the project's `glBorel`, `adelicGLHaar`, `adeleBorel`, `adelicAddHaar`, and by Mathlib's `ProbabilityTheory.cond`, `Measure.IsHaarMeasure` and `IsProbabilityMeasure`.
--
--   **Where it is used.** The bundle is the common argument of the project's space-level predicates for automorphic and cuspidal functions on $\mathrm{GL}_2(\mathbb{A}_F)$ and of its notions of realisability for Hecke eigensystems, which enter the route from modular forms to the Galois representations used in the Frey-curve argument; statements about genuine automorphic forms are the instances at `productionPinsOf`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_CarrierPins.lean

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField NumberField.AdelicHaar MeasureTheory

noncomputable section

namespace AutomorphicForm

structure CarrierPins (F : Type*) [Field F] [NumberField F] where
  mS : MeasurableSpace (AdelicGL2 (𝓞 F) F)
  μ : @Measure (AdelicGL2 (𝓞 F) F) mS
  D : Set (AdelicGL2 (𝓞 F) F)
  Z : Subgroup (AdeleRing (𝓞 F) F)ˣ
  U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)
  gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F
  nS : MeasurableSpace (AdeleRing (𝓞 F) F)
  ν : @Measure (AdeleRing (𝓞 F) F) nS

def productionPinsOf (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    CarrierPins F where
  mS := glBorel (Fin 2) (𝓞 F) F
  μ := adelicGLHaar (Fin 2) (𝓞 F) F
  D := D
  Z := ⊤
  U := U
  gen := gen
  nS := adeleBorel (𝓞 F) F
  ν := @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) B

theorem productionPinsOf_mS (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).mS = glBorel (Fin 2) (𝓞 F) F := rfl

theorem productionPinsOf_μ (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).μ = adelicGLHaar (Fin 2) (𝓞 F) F := rfl

theorem productionPinsOf_Z (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).Z = ⊤ := rfl

theorem productionPinsOf_nS (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).nS = adeleBorel (𝓞 F) F := rfl

theorem productionPinsOf_D (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).D = D := rfl

theorem productionPinsOf_U (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).U = U := rfl

theorem productionPinsOf_gen (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).gen = gen := rfl

theorem productionPinsOf_ν (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).ν
      = @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) B := rfl

theorem isHaarMeasure_productionPinsOf_μ (F : Type) [Field F] [NumberField F] (D U gen B) :
    @Measure.IsHaarMeasure _ _ _ (productionPinsOf F D U gen B).mS
      (productionPinsOf F D U gen B).μ :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

theorem isProbabilityMeasure_productionPinsOf_ν (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (hB0 : adelicAddHaar (𝓞 F) F B ≠ 0) (hBtop : adelicAddHaar (𝓞 F) F B ≠ ⊤) :
    @IsProbabilityMeasure _ (productionPinsOf F D U gen B).nS
      (productionPinsOf F D U gen B).ν := by
  letI := adeleBorel (𝓞 F) F
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite hB0 hBtop

end AutomorphicForm

end


