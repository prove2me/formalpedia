-- Prove2me | solution 1 for AutomorphicForm.cosetSum_rightConv_of_isLevelSphericalOfType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b997b8eb-2b05-5ee6-a27b-b35f38fae024

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchSpherical
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_cosetSum_rightConv_of_isLevelSphericalOfType

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped BigOperators

namespace Ws1
namespace F3cH

variable (F : Type) [Field F] [NumberField F]

private theorem eq_of_glArch_eq_of_glFin_eq {a b : AdelicGL2 (𝓞 F) F}
    (h1 : glArch (𝓞 F) F a = glArch (𝓞 F) F b) (h2 : glFin (𝓞 F) F a = glFin (𝓞 F) F b) : a = b := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have e1 := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h1
  have e2 := congrArg
    (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h2
  simp only [glArch_apply, glFin_apply] at e1 e2
  exact Prod.ext e1 e2

private theorem mul_comm_of_glFin_eq_one_of_glArch_eq_one {a r : AdelicGL2 (𝓞 F) F}
    (ha : glFin (𝓞 F) F a = 1) (hr : glArch (𝓞 F) F r = 1) : r * a = a * r := by
  apply eq_of_glArch_eq_of_glFin_eq F
  · rw [map_mul, map_mul, hr, one_mul, mul_one]
  · rw [map_mul, map_mul, ha, one_mul, mul_one]

private theorem sum_apply_mul_mul_reps_eq {G : Type*} [Group G] (U : Subgroup G) (g : G) {n : ℕ}
    (reps : Fin n → G)
    (hreps : ∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u')
    (hcov : ∀ x : G, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u)
    (hinj : ∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j)
    (φ : G → ℂ) (hφU : ∀ x : G, ∀ u ∈ U, φ (x * u) = φ x) (x : G) {u : G} (hu : u ∈ U) :
    ∑ i, φ (x * u * reps i) = ∑ i, φ (x * reps i) := by
  have hmem : ∀ i, ∃ u₁ ∈ U, ∃ u' ∈ U, u * reps i = u₁ * g * u' := by
    intro i
    obtain ⟨u₁, hu₁, u', hu', hi⟩ := hreps i
    exact ⟨u * u₁, mul_mem hu hu₁, u', hu', by rw [hi, ← mul_assoc, ← mul_assoc]⟩
  choose σ w hw hσ using fun i => hcov (u * reps i) (hmem i)
  have hσinj : Function.Injective σ := by
    intro i j hij
    apply hinj
    have e1 : (reps i)⁻¹ * reps j = (u * reps i)⁻¹ * (u * reps j) := by group
    rw [e1, hσ i, hσ j, hij]
    have e2 : (reps (σ j) * w i)⁻¹ * (reps (σ j) * w j) = (w i)⁻¹ * w j := by group
    rw [e2]
    exact mul_mem (inv_mem (hw i)) (hw j)
  have hσbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hσinj
  calc ∑ i, φ (x * u * reps i) = ∑ i, φ (x * reps (σ i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, hσ i, ← mul_assoc, hφU _ _ (hw i)]
    _ = ∑ i, φ (x * reps i) :=
        Fintype.sum_bijective σ hσbij (fun i => φ (x * reps (σ i))) (fun j => φ (x * reps j)) fun _ => rfl

end Ws1.F3cH

open Ws1.F3cH in
theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F tys ((productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f)
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F)
    (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (hreps : ∀ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, reps i = u * g * u')
    (hcov : ∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = u * g * u') →
      ∃ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = reps i * u)
    (hinj : ∀ i j, (reps i)⁻¹ * reps j ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N → i = j)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφU : φ ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N) :
    (fun x => ∑ i, rightConv F φ f (x * reps i)) = rightConv F (fun x => ∑ i, φ (x * reps i)) f := by
  classical
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

  set U : Subgroup (AdelicGL2 (𝓞 F) F) := levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F with hUdef
  change IsLevelSphericalOfType F tys U f at hf
  change ∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u' at hreps
  change ∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u at hcov
  change ∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j at hinj
  have hφU' : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x := fun x u hu => hφU x u hu
  set Uf : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := finiteLevelOne (𝓞 F) F N with hUfdef
  have hfinU : ∀ k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F), k ∈ Uf → AdelicDock.finEmbed (𝓞 F) F k ∈ U := by
    intro k hk
    refine ⟨?_, ?_⟩
    · show AdelicDock.finEmbed (𝓞 F) F k ∈ levelOne (𝓞 F) F N
      rw [mem_levelOne_iff, AdelicDock.glFin_finEmbed]; exact hk
    · show AdelicDock.finEmbed (𝓞 F) F k ∈ finiteAdelicGL2Subgroup F
      rw [mem_finiteAdelicGL2Subgroup_iff, AdelicDock.glArch_finEmbed]
  have hUimg : (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) = (Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
    ext k
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact mem_levelOne_iff.mp hg.1
    · intro hk
      exact ⟨AdelicDock.finEmbed (𝓞 F) F k, hfinU k hk, AdelicDock.glFin_finEmbed (𝓞 F) F k⟩
  have hUfo : IsOpen (Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := isOpen_finiteLevelOne (𝓞 F) F hN
  have hUfc : IsCompact (Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := isCompact_finiteLevelOne (𝓞 F) F N
  have hUfcl : IsClosed (Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := isClosed_finiteLevelOne (𝓞 F) F N

  obtain ⟨fa, hfaT, -, -, hfeq⟩ := hf
  rw [hUimg] at hfeq
  set ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ :=
    (Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))).indicator fun _ => (1 : ℂ) with hffdef
  have hff : IsFinTestFactor F ff := by
    refine ⟨?_, HasCompactSupport.intro hUfc fun y hy => Set.indicator_of_notMem hy _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ (Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
    · exact ⟨_, hUfo, hx, fun x' hx' => by rw [hffdef, Set.indicator_of_mem hx', Set.indicator_of_mem hx]⟩
    · exact ⟨_, hUfcl.isOpen_compl, hx, fun x' hx' => by
        rw [hffdef, Set.indicator_of_notMem (show x' ∉ (Uf : Set _) from hx'), Set.indicator_of_notMem hx]⟩
  have hfF : IsFactorizableTestFn F f := ⟨fa, ff, hfaT, hff, hfeq⟩
  obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hfF

  have hUfin : ∀ u ∈ U, glArch (𝓞 F) F u = 1 := fun u hu => (mem_finiteAdelicGL2Subgroup_iff F u).mp hu.2
  have hgfin : glArch (𝓞 F) F g = 1 := (mem_finiteAdelicGL2Subgroup_iff F g).mp hg
  have hrepfin : ∀ i, glArch (𝓞 F) F (reps i) = 1 := by
    intro i
    obtain ⟨u, hu, u', hu', hi⟩ := hreps i
    rw [hi, map_mul, map_mul, hUfin u hu, hUfin u' hu', hgfin, one_mul, one_mul]

  have hdec : ∀ y : AdelicGL2 (𝓞 F) F, f y ≠ 0 →
      ∃ a u : AdelicGL2 (𝓞 F) F, u ∈ U ∧ glFin (𝓞 F) F a = 1 ∧ y = a * u := by
    intro y hy
    have h1 : ff (glFin (𝓞 F) F y) ≠ 0 := fun h => hy (by rw [hfeq y, h, mul_zero])
    have h2 : glFin (𝓞 F) F y ∈ (Uf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
      by_contra h
      exact h1 (Set.indicator_of_notMem h _)
    refine ⟨y * (AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y))⁻¹, AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y),
      hfinU _ h2, ?_, ?_⟩
    · rw [map_mul, map_inv, AdelicDock.glFin_finEmbed, mul_inv_cancel]
    · rw [inv_mul_cancel_right]

  have hint : ∀ z : AdelicGL2 (𝓞 F) F, Integrable (fun y => φ (z * y) * f y) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro z
    have hc : Continuous (fun y => φ (z * y) * f y) := (hφ.comp (continuous_const.mul continuous_id)).mul hfc
    exact hc.integrable_of_hasCompactSupport hfs.mul_left

  funext x
  simp only [rightConv_apply]
  rw [← integral_finsetSum _ (fun i _ => hint (x * reps i))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  by_cases hy : f y = 0
  · simp [hy]
  · rw [← Finset.sum_mul]
    congr 1
    obtain ⟨a, u, hu, ha, rfl⟩ := hdec y hy
    calc ∑ i, φ (x * reps i * (a * u)) = ∑ i, φ (x * a * reps i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show x * reps i * (a * u) = (x * (reps i * a)) * u by simp only [mul_assoc], hφU' _ _ hu,
            mul_comm_of_glFin_eq_one_of_glArch_eq_one F ha (hrepfin i), mul_assoc]
      _ = ∑ i, φ (x * a * u * reps i) :=
          (sum_apply_mul_mul_reps_eq U g reps hreps hcov hinj φ hφU' (x * a) hu).symm
      _ = ∑ i, φ (x * (a * u) * reps i) := by simp only [mul_assoc]

end S_AutomorphicForm_cosetSum_rightConv_of_isLevelSphericalOfType
end P2MW
export P2MW.S_AutomorphicForm_cosetSum_rightConv_of_isLevelSphericalOfType (solution)
