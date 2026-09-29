-- Prove2me | Definitions.Def_AutomorphicForm_WindowedSiegelTopology
-- name    : AutomorphicForm_WindowedSiegelTopology
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/cc22c4c3-aea4-58dc-ad59-d6b50e5b024d
-- title:
--   Continuity and measurability of integrally windowed Siegel sets
-- statement:
--   This module proves topological and measure-theoretic facts about the windowed Siegel set apparatus introduced in the imported module `AutomorphicForm_WindowedSiegelSet`; it introduces no new definitions. The notions it manipulates are the project's own: over a normed field $K$, `topNormSq` and `rowNormSq` of a matrix are $\|g_{00}\|^2+\|g_{01}\|^2$ and $\|g_{10}\|^2+\|g_{11}\|^2$, `localHeight` is $\|\det g\|/\mathrm{rowNormSq}(g)$ (legitimate since `rowNormSq_pos` gives positivity on $\mathrm{GL}_2$), and `xWindowSq` is $\mathrm{topNormSq}(g)/\mathrm{rowNormSq}(g)-\mathrm{localHeight}(g)^2$. The continuity lemmas `continuous_entry`, `continuous_topNormSq_gl`, `continuous_rowNormSq_gl`, `continuous_det_gl`, `continuous_localHeight` and `continuous_xWindowSq` assert continuity of these functions on $\mathrm{GL}_2(K)$ for an arbitrary normed field $K$; `continuous_archHeight` asserts continuity of `archHeight F` for a number field $F$, proved as a finite product over the infinite places of powers of `localHeight` composed with the archimedean component maps.
--
--   The three main statements concern `integralWindowedSiegelSet F c u`, which is by definition the set of $g$ in `AdelicGL2 (𝓞 F) F` whose finite part `glFin` lies in `AdelicLevel.finiteIntegralGL2`, with $c \le \mathrm{archHeight}\,F$ of its archimedean part, and with $\mathrm{xWindowSq} \le u^2$ at every infinite place. First, if $c < 1$ and $u \neq 0$ then the identity lies in the interior of this set, the proof using openness of the integral level subgroup, continuity of the component homomorphisms, $\mathrm{archHeight}(1)=1$ and $\mathrm{xWindowSq}(1)=0$. Secondly, for any measurable space structure on `AdelicGL2 (𝓞 F) F` that is the Borel structure of its topology, and for all real $c,u$, the set is measurable. Thirdly, `exists_isOpen_subset_integralWindowedSiegelSet` packages the interior point as the existence of a nonempty open subset contained in the Siegel set. No statement here asserts any measure value, finiteness, or a covering property of the Siegel set.
--
--   **Relation to Mathlib.** The continuity proofs rest on Mathlib's `Units.continuous_val` together with `matrix_elem` and `matrix_det`; the windowed Siegel set and its height and window functionals are the project's own notions, Mathlib having no adelic Siegel sets.
--
--   **Where it is used.** These lemmas are the interface through which measure statements about the windowed Siegel set in $\mathrm{GL}_2$ of the adeles are obtained in the automorphic part of the development: measurability for integration arguments, and the interior point for positivity of the measure of the set and of its image under the open quotient map to the projective group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_WindowedSiegelTopology.lean

import Definitions.Def_AutomorphicForm_WindowedSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField MeasureTheory Matrix

noncomputable section

namespace AutomorphicForm

namespace WindowedSiegel

variable (F : Type) [Field F] [NumberField F]

section Continuity

variable {K : Type*} [NormedField K]

theorem continuous_entry (i j : Fin 2) :
    Continuous fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) i j :=
  Units.continuous_val.matrix_elem i j

theorem continuous_topNormSq_gl :
    Continuous fun g : GL (Fin 2) K => topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold topNormSq
  exact ((continuous_entry 0 0).norm.pow 2).add ((continuous_entry 0 1).norm.pow 2)

theorem continuous_rowNormSq_gl :
    Continuous fun g : GL (Fin 2) K => rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold rowNormSq
  exact ((continuous_entry 1 0).norm.pow 2).add ((continuous_entry 1 1).norm.pow 2)

theorem continuous_det_gl :
    Continuous fun g : GL (Fin 2) K => ((g : Matrix (Fin 2) (Fin 2) K)).det :=
  Units.continuous_val.matrix_det

theorem continuous_localHeight : Continuous (localHeight (K := K)) := by
  unfold localHeight
  exact continuous_det_gl.norm.div continuous_rowNormSq_gl fun g => (rowNormSq_pos g).ne'

theorem continuous_xWindowSq : Continuous (xWindowSq (K := K)) := by
  unfold xWindowSq
  exact (continuous_topNormSq_gl.div continuous_rowNormSq_gl fun g => (rowNormSq_pos g).ne').sub
    (continuous_localHeight.pow 2)

end Continuity

theorem continuous_archHeight : Continuous (archHeight F) := by
  unfold archHeight
  exact continuous_finsetProd _ fun v _ =>
    (continuous_localHeight.comp (AdelicLevel.continuous_archComponent F v)).pow _

theorem one_mem_interior_integralWindowedSiegelSet {c u : ℝ} (hc : c < 1) (hu : u ≠ 0) :
    (1 : AdelicGL2 (𝓞 F) F) ∈ interior (integralWindowedSiegelSet F c u) := by
  have htop : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := by simp
  have hKf : IsOpen {g : AdelicGL2 (𝓞 F) F |
      AdelicLevel.glFin (𝓞 F) F g ∈ AdelicLevel.finiteIntegralGL2 (𝓞 F) F} :=
    (AdelicLevel.isOpen_finiteLevelZero (𝓞 F) F htop).preimage
      (AdelicLevel.continuous_glFin (𝓞 F) F)
  have hArch : IsOpen {g : AdelicGL2 (𝓞 F) F |
      c < archHeight F (AdelicLevel.glArch (𝓞 F) F g)} :=
    isOpen_lt continuous_const
      ((continuous_archHeight F).comp (AdelicLevel.continuous_glArch (𝓞 F) F))
  have hWin : IsOpen {g : AdelicGL2 (𝓞 F) F | ∀ v : InfinitePlace F,
      xWindowSq (AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F g)) < u ^ 2} := by
    have hset : {g : AdelicGL2 (𝓞 F) F | ∀ v : InfinitePlace F,
        xWindowSq (AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F g)) < u ^ 2}
        = ⋂ v : InfinitePlace F, {g : AdelicGL2 (𝓞 F) F |
            xWindowSq (AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F g)) < u ^ 2} := by
      ext g
      simp [Set.mem_iInter]
    rw [hset]
    exact isOpen_iInter_of_finite fun v =>
      isOpen_lt (continuous_xWindowSq.comp ((AdelicLevel.continuous_archComponent F v).comp
        (AdelicLevel.continuous_glArch (𝓞 F) F))) continuous_const
  rw [mem_interior]
  refine ⟨{g : AdelicGL2 (𝓞 F) F |
        AdelicLevel.glFin (𝓞 F) F g ∈ AdelicLevel.finiteIntegralGL2 (𝓞 F) F}
      ∩ {g | c < archHeight F (AdelicLevel.glArch (𝓞 F) F g)}
      ∩ {g | ∀ v : InfinitePlace F,
          xWindowSq (AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F g)) < u ^ 2},
    fun g hg => ⟨hg.1.1, hg.1.2.le, fun v => (hg.2 v).le⟩,
    (hKf.inter hArch).inter hWin, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · show AdelicLevel.glFin (𝓞 F) F 1 ∈ AdelicLevel.finiteIntegralGL2 (𝓞 F) F
    rw [map_one]
    exact (AdelicLevel.finiteIntegralGL2 (𝓞 F) F).one_mem
  · show c < archHeight F (AdelicLevel.glArch (𝓞 F) F 1)
    rw [map_one, archHeight_one]
    exact hc
  · intro v
    show xWindowSq (AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F 1)) < u ^ 2
    rw [map_one, map_one, xWindowSq_one]
    positivity

theorem measurableSet_integralWindowedSiegelSet {mS : MeasurableSpace (AdelicGL2 (𝓞 F) F)}
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (c u : ℝ) :
    MeasurableSet (integralWindowedSiegelSet F c u) := by
  have htop : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := by simp
  have h : integralWindowedSiegelSet F c u
      = {g : AdelicGL2 (𝓞 F) F |
            AdelicLevel.glFin (𝓞 F) F g ∈ AdelicLevel.finiteIntegralGL2 (𝓞 F) F}
        ∩ ({g : AdelicGL2 (𝓞 F) F | c ≤ archHeight F (AdelicLevel.glArch (𝓞 F) F g)}
        ∩ {g : AdelicGL2 (𝓞 F) F | ∀ v : InfinitePlace F,
            xWindowSq (AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F g)) ≤ u ^ 2}) :=
    rfl
  rw [h]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact ((AdelicLevel.isOpen_finiteLevelZero (𝓞 F) F htop).preimage
      (AdelicLevel.continuous_glFin (𝓞 F) F)).measurableSet
  · exact (isClosed_le continuous_const
      ((continuous_archHeight F).comp (AdelicLevel.continuous_glArch (𝓞 F) F))).measurableSet
  · have hset : {g : AdelicGL2 (𝓞 F) F | ∀ v : InfinitePlace F,
        xWindowSq (AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F g)) ≤ u ^ 2}
        = ⋂ v : InfinitePlace F, {g : AdelicGL2 (𝓞 F) F |
            xWindowSq (AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F g)) ≤ u ^ 2} := by
      ext g
      simp [Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter fun v =>
      (isClosed_le (continuous_xWindowSq.comp ((AdelicLevel.continuous_archComponent F v).comp
        (AdelicLevel.continuous_glArch (𝓞 F) F))) continuous_const).measurableSet

theorem exists_isOpen_subset_integralWindowedSiegelSet {c u : ℝ} (hc : c < 1) (hu : u ≠ 0) :
    ∃ U : Set (AdelicGL2 (𝓞 F) F), IsOpen U ∧ U.Nonempty ∧
      U ⊆ integralWindowedSiegelSet F c u :=
  ⟨interior (integralWindowedSiegelSet F c u), isOpen_interior,
    ⟨1, one_mem_interior_integralWindowedSiegelSet F hc hu⟩, interior_subset⟩

end WindowedSiegel

end AutomorphicForm

end


