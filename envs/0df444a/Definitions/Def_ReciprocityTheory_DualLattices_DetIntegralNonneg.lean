-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_DetIntegralNonneg
-- name    : ReciprocityTheory_DualLattices_DetIntegralNonneg
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T18:12:06.043572+00:00
-- url     : https://prove2.me/theorems/cabded21-6abb-544d-b767-d3898afb5dd0
-- title:
--   Det Integral Nonneg
-- statement:
--   Definitions and structural lemmas for Det Integral Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetIntegralNonneg.lean

import Definitions.Def_ReciprocityTheory_DualLattices_FrobeniusOfGroupDivisorsRank
import Definitions.Def_ReciprocityTheory_DualLattices_KilledGen
import Definitions.Def_ReciprocityTheory_DualLattices_IdemGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
namespace Cons
def lenCoker {R : Type*} [CommRing R] (v : AddValuation R (WithTop ℝ)) {m h : ℕ}
    (B : Matrix (Fin m) (Fin h) R) : WithTop ℝ :=
  Finset.univ.inf fun g : Fin m → Fin h => v (B.submatrix id g).det
def ThmAiii {R : Type*} [CommRing R] (v : AddValuation R (WithTop ℝ)) {m h : ℕ}
    (α : Matrix (Fin m) (Fin h) R) (l1 : ℝ) : Prop :=
  lenCoker v α = (l1 : WithTop ℝ)
end Cons
section Bridge
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
def IsLogVal (v : Valuation C NNReal) (b : ℝ) (vA : AddValuation R (WithTop ℝ)) : Prop :=
  ∀ r : R, r ≠ 0 → vA r = ((Real.logb b (v (algebraMap R C r)) : ℝ) : WithTop ℝ)
end Bridge
end ReciprocityTheory.PGsh.Up


