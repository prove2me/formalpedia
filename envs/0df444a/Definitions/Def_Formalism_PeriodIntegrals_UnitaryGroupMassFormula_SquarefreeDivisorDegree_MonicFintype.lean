-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:37.327688+00:00
-- url     : https://prove2.me/theorems/cccb1273-3b76-499a-a690-98eb45b7b46a
-- title:
--   Monic Fintype
-- statement:
--   Definitions and structural lemmas for Monic Fintype, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeDivisorDegree/MonicFintype.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqfLab
import Definitions.Def_Formalism_PeriodIntegrals_SqfDivDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace PI.SqfDivDeg.W
instance monicFintype (g : ℕ) [Fact g.Prime] (n : ℕ) :
    Fintype {p : (ZMod g)[X] // p.Monic ∧ p.natDegree = n} :=
  Fintype.ofEquiv _ ((monicEquivDegreeLT n).trans (degreeLTEquiv (ZMod g) n).toEquiv).symm
def Mon (g : ℕ) [Fact g.Prime] (n : ℕ) : Finset (ZMod g)[X] :=
  (Finset.univ : Finset {p : (ZMod g)[X] // p.Monic ∧ p.natDegree = n}).map
    (Function.Embedding.subtype _)
open Classical in

def Rt (g : ℕ) [Fact g.Prime] (n : ℕ) : Finset (ZMod g)[X] :=
  (Mon g n).filter (fun p => ∃ x : ZMod g, p.IsRoot x)
def RootDense : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 1 ≤ n → g ^ n ≤ 2 * (Rt g n).card
def MainCount : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime] (a : ℕ), a ≤ r → ∀ T : Finset (ZMod g)[X],
    (∀ f ∈ T, PI.SqfLab.Eiv g r a f) →
      2 * (T.card : ℝ) + ((Rt g a).card : ℝ) * ((Rt g (r - a)).card : ℝ) ≤ 2 * (g : ℝ) ^ r
end PI.SqfDivDeg.W


