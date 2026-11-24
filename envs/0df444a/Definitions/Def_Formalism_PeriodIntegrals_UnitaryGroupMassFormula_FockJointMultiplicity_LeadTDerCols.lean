-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:39.365229+00:00
-- url     : https://prove2.me/theorems/03e1176e-2948-4e92-abb6-6b11bef62893
-- title:
--   Lead TDer Cols
-- statement:
--   Definitions and structural lemmas for Lead TDer Cols, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PI.FJMX
section Gen
variable {A : Type*} [CommRing A] [Algebra ℂ A] {m k : ℕ}
end Gen
section Block
variable {σ : Type*} {m n : ℕ}
def rowD (ι : Fin m × Fin n → σ) (a b : Fin m) : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
  ∑ k : Fin n, (X (ι (a, k)) : MvPolynomial σ ℂ) • pderiv (ι (b, k))
def colD (ι : Fin m × Fin n → σ) (c d : Fin n) : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
  ∑ i : Fin m, (X (ι (i, c)) : MvPolynomial σ ℂ) • pderiv (ι (i, d))
abbrev blkM (ι : Fin m × Fin n → σ) : Matrix (Fin m) (Fin n) (MvPolynomial σ ℂ) :=
  Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)
end Block
section Diag
variable {σ : Type*} {m : ℕ}
end Diag
end PI.FJMX


