-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:18.934859+00:00
-- url     : https://prove2.me/theorems/fdb7e576-6739-42ef-9555-77cc4c13ae34
-- title:
--   Apply At0 Eq Sum
-- statement:
--   Definitions and structural lemmas for Apply At0 Eq Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ApplyAt0EqSum.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace PI.IsoDerivBFintype
open PI.IsoDerivB
section lin
variable {T : Type} [Fintype T] {N N' : ℕ} (Θ : VC T N N' → ℂ)
def wt (α : Mono T N N') : ℂ := (α.prod fun _ n => (n.factorial : ℂ)) * taylor Θ α
end lin
section main
variable {Lt T : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) {N N' : ℕ}
  (nu : Lt → YoungDiagram)
instance fintypeCC (n : ℕ) : Fintype (ColChoice (Lt := Lt) n nu) :=
  inferInstanceAs (Fintype (∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin n))
def mY (J : ColChoice N nu) : MvPolynomial (FrV T N) ℂ :=
  ∏ z, ∏ c : Fin ((nu z).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu z).colLen c) =>
    if h : (j : ℕ) < N then (MvPolynomial.X (tp z, J z c i, ⟨j, h⟩) : MvPolynomial (FrV T N) ℂ)
    else 0)
variable [Fintype T]
end main
end PI.IsoDerivBFintype


