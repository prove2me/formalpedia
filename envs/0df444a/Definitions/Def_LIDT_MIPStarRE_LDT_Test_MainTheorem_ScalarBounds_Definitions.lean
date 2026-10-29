-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
-- name    : LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:47:39.12716+00:00
-- url     : https://prove2.me/theorems/8c5d3c60-0491-491d-8cf5-495687cbf722
-- title:
--   LIDT definitions: LDT / Test / MainTheorem / ScalarBounds / Definitions
-- statement:
--   This bundle defines the scalar error cascade for the formal main theorem. It introduces the final error envelope, the shared exponent envelope, the first cascade scalar and four subsequent cascade errors, and the hypotheses that connect the incoming induction error to these bounds.
--
--   Principal definitions:
--   - `mainFormalError`: the final formal error envelope.
--   - `mainFormalEnvelope`: the common polynomial-exponent and decay envelope.
--   - `cascadeSigma`: the first cascade scalar built from the incoming induction error.
--   - `cascadeZeta1`: the first displayed cascade error.
--   - `cascadeZeta2`: the formal Step 6 cascade error.
--   - `cascadeZeta3`: the self-consistency cascade error.
--   - `cascadeZeta4`: the point-consistency cascade error.
--   - `CascadeHypotheses`: the hypotheses for the complete cascade.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean#L32-L155

-- Generated from MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Mathlib

namespace LIDT

/-!
# Error cascade — core definitions

This module defines the central error quantities `mainFormalError`,
`mainFormalEnvelope`, the cascade variables `σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄`,
and the `CascadeHypotheses` numeric regime used throughout the error-cascade
bookkeeping for Step 8 of `mainFormal`.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test

/-- The formal final error envelope for `thm:main-formal`.

The sharper pre-completion line-169 repair keeps the point-transport scale at
the original `1/40000` exponent used by the surrounding Step 8 cascade. -/
noncomputable def mainFormalError (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
    (Real.rpow eps (1 / (40000 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (40000 : Error)) +
      Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))))



/-- The polynomial-exponent envelope common to all cascade bounds,
`ε^(1/40000) + (d/q)^(1/40000) + exp(-k/(2560000 m²))`. See
`mainFormalError_eq_envelope` for the identification
`mainFormalError = 100000 · k² · m⁴ · mainFormalEnvelope`. -/
noncomputable def mainFormalEnvelope (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  Real.rpow eps (1 / (40000 : Error)) +
    Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (40000 : Error)) +
    Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ)))))





/-- Paper quantity `σ` (see `inductive_step.tex:189`), built from an incoming
induction-step error `ν` and the main-induction exponential decay factor. -/
noncomputable def cascadeSigma (params : Parameters) (k : ℕ) (ν : Error) : Error :=
  ((params.m : Error) ^ (2 : ℕ)) *
    (ν + Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))

/-- Paper quantity `ζ₁ = 2σ + 2·√(3ε + 2σ) + m·d/q` (see `inductive_step.tex:133`). -/
noncomputable def cascadeZeta1 (params : Parameters) (eps σ : Error) : Error :=
  2 * σ + 2 * Real.sqrt (3 * eps + 2 * σ) +
    (params.m : Error) * (params.d : Error) / (params.q : Error)

/-- Formal Step 6 quantity
`ζ₂ = 200·ζ₁^(1/4) + 42·ζ₁^(1/8)`.

The paper prints coefficient `40` in `inductive_step.tex:149`; the extra `2`
absorbs the residual `+ 2ζ₁` term from completing an orthonormalized
submeasurement when `0 ≤ ζ₁ ≤ 1`. -/
noncomputable def cascadeZeta2 (ζ₁ : Error) : Error :=
  200 * Real.rpow ζ₁ (1 / (4 : Error)) + 42 * Real.rpow ζ₁ (1 / (8 : Error))

/-- Paper quantity `ζ₃ = 6·ζ₁ + 6·ζ₂` (see `inductive_step.tex:158`). -/
noncomputable def cascadeZeta3 (ζ₁ ζ₂ : Error) : Error :=
  6 * ζ₁ + 6 * ζ₂

/-- Paper quantity `ζ₄ = 2σ + 2·√(ζ₁ + ζ₃/2)` (see `inductive_step.tex:181`). -/
noncomputable def cascadeZeta4 (σ ζ₁ ζ₃ : Error) : Error :=
  2 * σ + 2 * Real.sqrt (ζ₁ + ζ₃ / 2)

/-- Repaired line-169 error obtained by the checked local pre-completion route.

**Source:** This is source-faithful scalar bookkeeping for the repaired
line-169 route documented in `docs/paper-gaps/issue-1099-sharper-local-fix.tex`
and used in `references/ldt-paper/inductive_step.tex:167-173`.

Paper line 169 is printed with the exact error `ζ₁`; the checked local repair
instead yields `ζ₁ + 10·ζ₁^(1/8)`.  The additional term comes from
`sqrt (orthonormalizationError ζ₁) = sqrt (100·ζ₁^(1/4)) = 10·ζ₁^(1/8)` in
`ProjectivizationLine169Repair.leftConsistency_with_orthonormalization_loss`
and its Bob-side mirror.

This is an internal repaired-route scalar for the Step 6 transport.  It is not
the paper's printed line-169 parameter, and it is later absorbed into
`mainFormalError`. -/
noncomputable def cascadeLine169RepairError (ζ₁ : Error) : Error :=
  ζ₁ + 10 * Real.rpow ζ₁ (1 / (8 : Error))

/-- Repaired final point-consistency scalar obtained by substituting the checked
line-169 repair error into the last Step 8 transport triangle.

**Source:** This is source-faithful scalar bookkeeping for the repaired
line-169 route documented in `docs/paper-gaps/issue-1099-sharper-local-fix.tex`
and absorbed by the error cascade from
`references/ldt-paper/inductive_step.tex:186-234`.

The paper's `ζ₄` at `references/ldt-paper/inductive_step.tex:181` is
`2σ + 2·√(ζ₁ + ζ₃/2)`.  This repaired variant replaces `ζ₁` by the internal
checked line-169 repair error above, so it is likewise an internal scalar that
is subsequently absorbed into `mainFormalError` rather than a new paper-facing
theorem parameter. -/
noncomputable def cascadeZeta4Repaired (σ ζ₁ ζ₃ : Error) : Error :=
  2 * σ + 2 * Real.sqrt (cascadeLine169RepairError ζ₁ + ζ₃ / 2)

/-- Paper origin: `references/ldt-paper/inductive_step.tex:130-211`
(`\label{eq:G-self-consistency}` through
`\label{eq:final-right-point-consistency}`, error cascade ζ₁–ζ₄); blueprint
`\label{def:main-formal-error-cascade}`.

**Source:** This is a faithful encoding of the standing scalar regime used in
the paper's error cascade, with the corrected large-\(k\) and nonzero-sampling
boundaries documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex`
and `docs/paper-gaps/issue-422-main-formal-zero-k-boundary.tex`.

Standing numeric regime used throughout the cascade bounds: parameters
satisfy the unit scale, and `ε, d/q ∈ [0, 1]`. -/
structure CascadeHypotheses (params : Parameters) (k : ℕ) (eps : Error) : Prop where
  hk : 1 ≤ (k : Error)
  hm : 1 ≤ (params.m : Error)
  hepsNN : 0 ≤ eps
  hepsOne : eps ≤ 1
  hdq : (params.d : Error) ≤ (params.q : Error)
  hqPos : 0 < (params.q : Error)

namespace CascadeHypotheses

variable {params : Parameters} {k : ℕ} {eps : Error}
variable (h : CascadeHypotheses params k eps)

include h























end CascadeHypotheses

end Test

end MIPStarRE.LDT

end

end LIDT


