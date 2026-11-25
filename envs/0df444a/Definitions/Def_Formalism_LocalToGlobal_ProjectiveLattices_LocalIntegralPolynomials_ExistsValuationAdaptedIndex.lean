-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:17:55.926443+00:00
-- url     : https://prove2.me/theorems/438ed823-9e74-4573-aabd-8505cb7cd75d
-- title:
--   Exists Valuation Adapted Index
-- statement:
--   Definitions and structural lemmas for Exists Valuation Adapted Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/ExistsValuationAdaptedIndex.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.LocAlg
open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
variable {Ω : Type} [Field Ω] {D N : ℕ}
def yv (jc : Fin (N + 1)) (x : Fin N → Ω) : Fin (N + 1) → Ω :=
  Fin.insertNth (α := fun _ => Ω) jc 1 x
def tj (jc j0 : Fin (N + 1)) (x : Fin N → Ω) : SVar D N → OmS Ω D N :=
  Sum.elim (fun _ => sImg jc x (0, j0)) (fun p => sImg jc x (p.1, j0.succAbove p.2))
def qj (jc j0 : Fin (N + 1)) (x : Fin N → Ω) (p : TVar D N) : MvPolynomial (SVar D N) Ω :=
  Fin.insertNth (α := fun _ => MvPolynomial (SVar D N) Ω) j0
    (if p.1 = 0 then X (Sum.inl ())
      else -∑ k, C (yv jc x (j0.succAbove k) / yv jc x j0) * X (Sum.inr (p.1, k)))
    (fun k => X (Sum.inr (p.1, k))) p.2
variable {jc j0 : Fin (N + 1)} {x : Fin N → Ω}
def intPoly (σ : Type) (W : Subring Ω) : Subring (MvPolynomial σ Ω) where
  carrier := {P | ∀ e, P.coeff e ∈ W}
  mul_mem' := by
    intro P Q hP hQ e
    classical
    rw [coeff_mul]
    exact sum_mem fun d _ => W.mul_mem (hP _) (hQ _)
  one_mem' := by
    intro e
    classical
    rw [coeff_one]
    split_ifs
    exacts [W.one_mem, W.zero_mem]
  add_mem' := by
    intro P Q hP hQ e
    rw [coeff_add]
    exact W.add_mem (hP e) (hQ e)
  zero_mem' := by
    intro e
    rw [coeff_zero]
    exact W.zero_mem
  neg_mem' := by
    intro P hP e
    rw [coeff_neg]
    exact W.neg_mem (hP e)
end Formalism.L2.Pj.LocAlg


