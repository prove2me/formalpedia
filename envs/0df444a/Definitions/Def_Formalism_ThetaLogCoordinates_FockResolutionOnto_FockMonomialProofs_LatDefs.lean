-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:50.443881+00:00
-- url     : https://prove2.me/theorems/4359d365-e60d-4501-8584-b19f322b7071
-- title:
--   Lat Defs
-- statement:
--   Definitions and structural lemmas for Lat Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/LatDefs.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas MvPolynomial Finset
noncomputable def Wtot (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  ⨆ o : ℕ, XSp p (setLast LL o) J M ρ
noncomputable def M2 (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) : Submodule ℤ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  ⨆ o : ℕ, Submodule.map (initL p (Fin.last K, ρ) 0)
    ((Y p (setLast LL o) J M).restrictScalars ℤ_[p] ⊓ IntPol p (Fin (K + 1) × Fin r))
end Formalism.InvariantFactorPaths.L4


