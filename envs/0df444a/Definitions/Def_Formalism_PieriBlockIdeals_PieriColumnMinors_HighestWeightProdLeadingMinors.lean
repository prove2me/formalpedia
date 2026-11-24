-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:57:54.114314+00:00
-- url     : https://prove2.me/theorems/29d649f3-1107-473d-94d3-d3590a25e7d8
-- title:
--   Highest Weight Prod Leading Minors
-- statement:
--   Definitions and structural lemmas for Highest Weight Prod Leading Minors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
def finSumEquivOfAddEq {r s t : ℕ} (h : s + t = r) : Fin s ⊕ Fin t ≃ Fin r :=
  ((Equiv.sumCongr Fin.revPerm (Equiv.refl (Fin t))).trans (Equiv.sumComm _ _)).trans
    (finSumFinEquiv.trans (finCongr (by omega)))
def diagonalEntryIndicator (r : ℕ) : Fin r × Fin r → Fin r → ℕ := fun v c => if c = Fin.rev v.1 then 0 else 1
def columnWeight {r : ℕ} (c : Fin r) : Fin r × Fin r → ℤ := fun v => ((lgraded_wa (n := r) c v : ℕ) : ℤ)
noncomputable def leadingMinorPolynomial (r s : ℕ) : MvPolynomial (Fin r × Fin r) ℤ := if h : s ≤ r then lpMinor ℤ s h h else 1
def partialSumOfExponents {r : ℕ} (ν : Fin r → ℕ) (s : ℕ) : ℕ := if h : s < r then ν ⟨s, h⟩ else 0
noncomputable def ld3Q {r : ℕ} (ν : Fin r → ℕ) : MvPolynomial (Fin r × Fin r) ℤ :=
  ∏ s ∈ Finset.range r, leadingMinorPolynomial r (r - (s + 1)) ^ (partialSumOfExponents ν s - partialSumOfExponents ν (s + 1))
end Formalism.CohomologicalDescent.LD


