-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
-- name    : LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:48:39.751982+00:00
-- url     : https://prove2.me/theorems/7966479a-9761-435e-8d90-4869eaf0ad90
-- title:
--   LIDT definitions: LDT / Test / MainTheorem / ScalarBounds / EnvelopeBounds
-- statement:
--   This bundle defines the scalar step envelope used in the main formal error cascade. The envelope combines fractional powers of the test error and the degree-to-field-size ratio with an exponential sampling tail, and its later lemmas compare scales and square roots of the envelope.
--
--   Principal definitions:
--   - `stepEnvelope`: For positive scale parameters $n,N$, the quantity $\varepsilon^{1/n}+(d/q)^{1/n}+\exp(-k/(Nm^2))$.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean#L27-L32

-- Generated from MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Mathlib

namespace LIDT

/-!
# Error cascade — envelope and root bounding machinery

Internal helper lemmas for the error-cascade bookkeeping of Step 8.
These provide the step-envelope interpolation (`stepEnvelope`),
monotonicity under denominator enlargement, square-root scaling, and
explicit numeric bounds on various `rpow` and `sqrt` expressions.
All lemmas are technical and should not be part of downstream API.

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test

/-- A paper-local envelope with exponent `1/n` and decay scale `N`. -/
noncomputable def stepEnvelope (params : Parameters) (k : ℕ) (eps : Error)
    (n N : Error) : Error :=
  Real.rpow eps (1 / n) +
    Real.rpow ((params.d : Error) / (params.q : Error)) (1 / n) +
    Real.exp (-((k : Error) / (N * ((params.m : Error) ^ (2 : ℕ)))))





































































end Test

end MIPStarRE.LDT

end

end LIDT


