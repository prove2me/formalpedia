-- Prove2me | solution 1 for AutomorphicForm.iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0ddc0359-08f4-5ead-a494-9fe9534fb875

import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Definitions.Def_AutomorphicForm_IwasawaShellIndex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent.AutomorphicForm IsDedekindDomain"
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace AutomorphicForm p2m_export "AutomorphicForm" "rationalCentreUnipotent AdelicGL2 globalPoints centralScalar iwasawaShellIndex iwasawaShellIndex_centralScalar_mul iwasawaShellIndex_unipotentGL2_mul" end AutomorphicForm
p2m_open_scoped "AutomorphicForm" in

theorem AutomorphicForm.globalPoints_scalar_eq_centralScalar (K : Type) [Field K] [NumberField K] (a : Kˣ) :
    globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a) =
      centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (a : K)) i j) =
    (Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : AdelicGL2 (𝓞 K) K) (hx : x ∈ rationalCentreUnipotent K) (g : AdelicGL2 (𝓞 K) K) :
    iwasawaShellIndex K v (x * g) = iwasawaShellIndex K v g := by
  revert g
  rw [rationalCentreUnipotent, Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∀ g, iwasawaShellIndex K v (x * g) = iwasawaShellIndex K v g)
    ?_ ?_ ?_ ?_ hx
  · intro x hx g
    rcases hx with hx | hx
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
      rw [MonoidHom.comp_apply, globalPoints_scalar_eq_centralScalar, iwasawaShellIndex_centralScalar_mul]
    · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
      exact iwasawaShellIndex_unipotentGL2_mul v g (Multiplicative.toAdd y)
  · intro g; rw [one_mul]
  · intro x y _ _ hx hy g
    rw [mul_assoc, hx, hy]
  · intro x _ hx g
    have := hx (x⁻¹ * g)
    rw [mul_inv_cancel_left] at this
    exact this.symm

end S_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent
end P2MW
export P2MW.S_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent (solution)
