-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/21f00405-944b-5630-9fb6-95e57f99e5f1

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N ∧ x = a * k)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ)
    (hφU : φ ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N) :
    rightConv F φ f ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys := by
  classical
  refine Submodule.mem_inf.mpr ⟨?_, AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite F tys φ hφc f hf hbf⟩

  have hcomm : ∀ a u : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 → u ∈ finiteAdelicGL2Subgroup F → u * a = a * u := by
    intro a u ha hu
    have hu' := (mem_finiteAdelicGL2Subgroup_iff F u).mp hu
    refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
    · have h := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j)
        (show glArch (𝓞 F) F (u * a) = glArch (𝓞 F) F (a * u) by rw [map_mul, map_mul, hu', one_mul, mul_one])
      simpa only [glArch_apply] using h
    · have h := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)
        (show glFin (𝓞 F) F (u * a) = glFin (𝓞 F) F (a * u) by rw [map_mul, map_mul, ha, one_mul, mul_one])
      simpa only [glFin_apply] using h
  intro x u hu
  have huKf : u ∈ finiteAdelicGL2Subgroup F := (Subgroup.mem_inf.mp hu).2
  simp only [rightConv_apply]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  by_cases hy : f y = 0
  · simp only [hy, mul_zero]
  · obtain ⟨a, k, ha, hk, rfl⟩ := hfs y hy
    show φ (x * u * (a * k)) * f (a * k) = φ (x * (a * k)) * f (a * k)
    congr 1
    have e1 : x * u * (a * k) = x * a * u * k := by
      rw [mul_assoc x u, ← mul_assoc u a k, hcomm a u ha huKf, mul_assoc, mul_assoc, mul_assoc]
    rw [e1, hφU (x * a * u) k hk, hφU (x * a) u hu, ← mul_assoc, hφU (x * a) k hk]

end S_AutomorphicForm_CuspidalConstituent_rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite (solution)
