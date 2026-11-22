-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_EvalBindTorusSubst
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_EvalBindTorusSubst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:41.680402+00:00
-- url     : https://prove2.me/theorems/fc210763-554b-4d67-83ab-60a6f8879b63
-- title:
--   Eval Bind Torus Subst
-- statement:
--   Definitions and structural lemmas for Eval Bind Torus Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/EvalBindTorusSubst.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_GramStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
namespace PI.UD
noncomputable def torusSubst {ι : Type} {n : ℕ} (w v : ι → Matrix (Fin n) (Fin n) ℂ) :
    ι × Fin n × Fin n → MvPolynomial (ι × Fin n) ℂ :=
  fun x => ∑ k, C (w x.1 x.2.1 k) * X (x.1, k) * C (v x.1 k x.2.2)
noncomputable def leftSubst {ι : Type} {n : ℕ} (A : ι → Matrix (Fin n) (Fin n) ℂ) :
    ι × Fin n × Fin n → MvPolynomial (ι × Fin n × Fin n) ℂ :=
  fun x => ∑ k, C (A x.1 x.2.1 k) * X (x.1, k, x.2.2)
end PI.UD


