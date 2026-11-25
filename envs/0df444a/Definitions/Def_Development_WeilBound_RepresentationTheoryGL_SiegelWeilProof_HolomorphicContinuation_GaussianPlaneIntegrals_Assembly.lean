-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_Assembly
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_Assembly
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:04:39.536804+00:00
-- url     : https://prove2.me/theorems/577f1a60-c7e7-58ac-be69-cba5d260f250
-- title:
--   Assembly
-- statement:
--   Definitions and structural lemmas for Assembly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/Assembly.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_pair_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_Tf_deg
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_Tf_mem
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_continuous_blk
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_eval_Tf
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_integrable_eval_act

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder Matrix
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmT
open AsmA
attribute [local irreducible] Tf
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
variable (ι A B) in

def invSub : Submodule ℂ (PV ι A B) where
  carrier := {q | IsInv q}
  add_mem' := fun {a b} ha hb u hu => by rw [map_add, ha u hu, hb u hu]
  zero_mem' := fun u _ => map_zero _
  smul_mem' := fun c q hq u hu => by rw [map_smul, hq u hu]
variable (ι A B) in

def Vd (d : ℕ) : Submodule ℂ (PV ι A B) := restrictTotalDegree ((ι × A) ⊕ (ι × B)) ℂ d ⊓ invSub ι A B
instance (d : ℕ) : FiniteDimensional ℂ (Vd ι A B d) := Submodule.finiteDimensional_of_le inf_le_left
theorem integrable_eval_act_blk_toMK (hA : Avg) (z : (ι × A) ⊕ (ι × B) → ℂ) (q : PV ι A B) :
    Integrable (fun k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true) =>
      eval (act (blk (Formalism.REAL.toMK k)) ((blk (Formalism.REAL.toMK k)).map star) z) q)
      (Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) :=
  integrable_eval_act hA _ _ continuous_blk (continuous_blk.matrix_map continuous_star) z q
theorem Tf_add (hA : Avg) (q1 q2 : PV ι A B) : Tf hA (q1 + q2) = Tf hA q1 + Tf hA q2 :=
  MvPolynomial.funext fun z => by
    rw [map_add, eval_Tf, eval_Tf, eval_Tf, ← integral_add (integrable_eval_act_blk_toMK hA z q1) (integrable_eval_act_blk_toMK hA z q2)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [map_add]
theorem Tf_smul (hA : Avg) (c : ℂ) (q : PV ι A B) : Tf hA (c • q) = c • Tf hA q :=
  MvPolynomial.funext fun z => by
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, eval_Tf, eval_Tf,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [map_mul, eval_C]
theorem Tf_memVd (hS : Stable) (hA : Avg) {d : ℕ} {q : PV ι A B} (hq : q ∈ Vd ι A B d) :
    Tf hA q ∈ Vd ι A B d := by
  rw [Vd, Submodule.mem_inf] at hq ⊢
  refine ⟨(mem_restrictTotalDegree _ _ _).mpr ((Tf_deg hA q).trans ((mem_restrictTotalDegree _ _ _).mp hq.1)), ?_⟩
  show IsInv (Tf hA q)
  exact pair_inv (Tf_mem hS hA q)
def Tlin (hS : Stable) (hA : Avg) (d : ℕ) : Vd ι A B d →ₗ[ℂ] Vd ι A B d where
  toFun q := ⟨Tf hA q, Tf_memVd hS hA q.2⟩
  map_add' q1 q2 := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    exact Tf_add hA (q1 : PV ι A B) (q2 : PV ι A B)
  map_smul' c q := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    exact Tf_smul hA c (q : PV ι A B)
def Mk (k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true)) : Matrix ι ι ℂ :=
  (blk (ι := ι) (A := A) (B := B) (Formalism.REAL.toMK k)).transpose * (blk (Formalism.REAL.toMK k)).map star
end PositivityTheory.Rg.Sw.FFTSteps.AsmT
namespace PositivityTheory.Rg.Sw.FFTSteps
open AsmT
end PositivityTheory.Rg.Sw.FFTSteps


