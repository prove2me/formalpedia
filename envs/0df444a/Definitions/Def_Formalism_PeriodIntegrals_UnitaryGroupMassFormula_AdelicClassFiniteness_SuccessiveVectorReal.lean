-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorReal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorReal
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:33:41.744155+00:00
-- url     : https://prove2.me/theorems/56b033ce-9fba-4440-959b-840cf8a5739c
-- title:
--   Successive Vector Real
-- statement:
--   Definitions and structural lemmas for Successive Vector Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorReal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.AdelClassFin
open Formalism.UG NumberField Matrix
open scoped ComplexOrder
section Gen
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
end Gen
section Coord
variable {E : Type} [Field E] [NumberField E] [StarRing E]
def svP {m N : ℕ} (e : Fin N → Fin m → E) (φ : E →+* ℂ) : Matrix (Fin m) (Fin N) ℂ :=
  Matrix.of fun k i => φ (e i k)
def svBig {m N : ℕ} (e : Fin N → Fin m → E) : Matrix (Fin m × (E →+* ℂ)) (Fin N) ℂ :=
  Matrix.of fun p i => p.2 (e i p.1)
end Coord
end PIW.AdelClassFin


