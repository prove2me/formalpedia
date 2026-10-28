-- Prove2me | solution 2 for AlgMechDesign.Rounding.rounding_mechanism_truthful_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:36.245764+00:00
-- url     : https://prove2.me/submissions/53ac807a-4c1d-485e-8831-004b197329b4

import Mathlib
import Definitions.Def_AlgMechDesign_Rounding_Model
import Definitions.Def_AlgMechDesign_Rounding_Mechanism
import Theorems.Thm_AlgMechDesign_Rounding_rounds_like_truth_approx
import Theorems.Thm_AlgMechDesign_Rounding_truth_telling_dominant

-- carved verbatim out of submission f1440ef5-c72a-493f-a1d5-3923198cee07, lines 159-173

section
set_option autoImplicit false
open AlgMechDesign.Rounding

theorem solution {n k : ℕ} [NeZero n] (a b ε δ : ℝ) (ha : 0 < a)
    (hab : a < b) (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε * a)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (halloc : IsRoundedOptimal a b δ alloc) :
    Truthful a b alloc (roundingPay δ alloc) ∧
    ∀ t : Fin n → Fin k → ℝ, IsBoundedType a b t →
      ∀ (D : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k),
        (∀ l : Fin n, Dominant a b alloc (roundingPay δ alloc) l (t l) (D l) (E l)) →
        (∀ l : Fin n, RoundsLikeTruth δ l (t l) (D l) (E l)) →
          ∀ y : Fin k → Fin n,
            gT (alloc D) (actualTimes alloc D E) ≤ (1 + ε) * makespan t y := by
  refine ⟨(AlgMechDesign.Rounding.truth_telling_dominant a b δ ha hab hδ alloc halloc).2, ?_⟩
  intro t ht D E hdom hround
  exact AlgMechDesign.Rounding.rounds_like_truth_approx a b ε δ ha hab hε hδ hδε alloc halloc t ht D
    (fun l => (hdom l).1) E (fun l => (hdom l).2.1) hround

end
