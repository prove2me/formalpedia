-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:41.767451+00:00
-- url     : https://prove2.me/theorems/396ea040-2040-4f2b-b6ce-c92d7820798f
-- title:
--   Restriction Min Max Int Holds
-- statement:
--   Definitions and structural lemmas for Restriction Min Max Int Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictionMinMaxIntHolds.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
section EProj
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def LowIm (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (ρ : Fin r) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  ⨆ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ d < c), Submodule.map (glAct p LL j c d) ⊤
def IsEProj (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (ρ : Fin r) (w : Fin r → ℤ)
    (PE : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop :=
  PE ∘ₗ PE = PE ∧ LinearMap.range PE = HWC p LL j (univ.erase ρ) w ⊓ WtSpC p LL j univ w ∧
    LinearMap.ker PE ⊓ WtSpC p LL j univ w = LowIm p LL j ρ ⊓ WtSpC p LL j univ w
end EProj
section WtComp
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def wtComp (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (w : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  compP (fun m => ∀ c, wt LL j c m = w c) x
end WtComp
section MulX
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end MulX
end Formalism.InvariantFactorPaths.L4


