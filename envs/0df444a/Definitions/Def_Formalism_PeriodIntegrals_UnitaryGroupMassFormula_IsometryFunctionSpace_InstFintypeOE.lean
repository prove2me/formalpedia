-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_InstFintypeOE
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_InstFintypeOE
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:03.805808+00:00
-- url     : https://prove2.me/theorems/406dc249-caa1-41cb-ab10-6a498fd02406
-- title:
--   Inst Fintype OE
-- statement:
--   Definitions and structural lemmas for Inst Fintype OE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/InstFintypeOE.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoFunV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj
import Theorems.Thm_PI_IsoFunVW_finite_oe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MvPolynomial
noncomputable section
namespace PI.IsoFunVW
open PI.IsoFunV
noncomputable instance instFintypeOE (m n : ℕ) : Fintype (Fin m ↪o Fin n) :=
  @Fintype.ofFinite _ (finite_oe m n)
noncomputable instance instFintypeCC {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) : Fintype (ColChoice N nu) := by
  unfold ColChoice; infer_instance
def linW {σ : Type} (w : (σ →₀ ℕ) → ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun P := ∑ α ∈ P.support, coeff α P * w α
  map_add' P Q := by
    classical
    have key : ∀ (R : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ)), R.support ⊆ S →
        ∑ α ∈ R.support, coeff α R * w α = ∑ α ∈ S, coeff α R * w α := by
      intro R S hS
      refine Finset.sum_subset hS (fun α _ hα => ?_)
      rw [MvPolynomial.mem_support_iff, not_not] at hα
      simp [hα]
    rw [key (P + Q) (P.support ∪ Q.support) support_add,
      key P (P.support ∪ Q.support) subset_union_left,
      key Q (P.support ∪ Q.support) subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [coeff_add, add_mul]
  map_smul' c P := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine (Finset.sum_subset support_smul (fun α _ hα => ?_)).trans ?_
    · rw [MvPolynomial.mem_support_iff, not_not] at hα
      simp [hα]
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [coeff_smul, smul_eq_mul, mul_assoc]
def wTh {T : Type} [Fintype T] {N N' : ℕ} (Θ : VC T N N' → ℂ) (α : Mono T N N') : ℂ :=
  (α.prod fun _ n => (n.factorial : ℂ)) * taylor Θ α
def yfr {Lt T : Type} (tp : Lt → T) {N N' : ℕ} (s : T → ℂ) (x : Lt → Fin N → ℕ → ℂ) :
    Lt → Fin N' → ℕ → MvPolynomial (Idx T N N') ℂ :=
  fun z a j => ∑ b : Fin N, C (s (tp z)) * X ((tp z, a, b) : Idx T N N') * C (x z b j)
theorem AOp_eq {Lt T : Type} [Fintype Lt] [DecidableEq Lt] [Fintype T] (tp : Lt → T) {N N' : ℕ}
    (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ) (φ : LaC N nu) (I : ColChoice N' nu) :
    AOp tp nu s Θ φ I = ∑ J : ColChoice N nu, applyAt0 (PIJ tp nu s I J) Θ * φ J := by
  rw [AOp, finsum_eq_sum_of_fintype]
def AOpLin {Lt T : Type} [Fintype Lt] [DecidableEq Lt] [Fintype T] (tp : Lt → T) {N N' : ℕ}
    (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ) : LaC N nu →ₗ[ℂ] LaC N' nu where
  toFun φ := AOp tp nu s Θ φ
  map_add' φ ψ := by
    funext I
    simp only [AOp_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c φ := by
    funext I
    simp only [AOp_eq, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    ring
end PI.IsoFunVW
end


