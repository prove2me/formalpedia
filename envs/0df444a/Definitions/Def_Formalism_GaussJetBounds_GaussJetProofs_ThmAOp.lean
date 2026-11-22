-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
-- name    : Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:43.62189+00:00
-- url     : https://prove2.me/theorems/34aecc08-33f2-4aee-a721-3d9c38dcefc4
-- title:
--   Thm AOp
-- statement:
--   Definitions and structural lemmas for Thm AOp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAOp.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPolynomial
def opInt (K : Type u) [NormedField K] [IsUltrametricDist K] (σ : Type) :
    Subring (MvPolynomial σ K) where
  carrier := {P | ∀ κ, ‖coeff κ P‖ ≤ 1}
  mul_mem' := by
    intro P Q hP hQ κ
    classical
    rw [coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hP _) (norm_nonneg _) (hQ _)
  one_mem' := by
    intro κ
    classical
    rw [coeff_one]
    split_ifs <;> simp
  add_mem' := by
    intro P Q hP hQ κ
    rw [coeff_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hP _) (hQ _))
  zero_mem' := by
    intro κ
    simp
  neg_mem' := by
    intro P hP κ
    rw [coeff_neg, norm_neg]
    exact hP κ
def opA {K : Type u} [Field K] {d N0 : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (s : ZMod d) (i k : Fin N0) : K :=
  if s ∈ TT ∧ i.val = 0 then (if k = i then 1 else 0)
  else if s ∈ TT ∧ k.val = 0 then 0 else T s i k
def rowDeg {d N0 N1 : ℕ} (s : ZMod d) (k : Fin N0) (κ : ZV d N0 N1 →₀ ℕ) : ℕ :=
  ∑ b : Fin N1, κ (s, k, b)
end Formalism.DworkPowerSeriesWeights


