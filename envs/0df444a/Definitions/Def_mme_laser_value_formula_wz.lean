-- Prove2me | Definitions.Def_mme_laser_value_formula_wz
-- name    : mme_laser_value_formula_wz
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-01T15:08:22.853946+00:00
-- url     : https://prove2.me/theorems/c95939ce-0456-463e-b5be-cdc8814ee537
-- statement:
--   Wigderson-Zuiddam §6 laser-method value functional — real (non-placeholder) definition. Replaces the placeholder `laserValueFormula := 1` from Def_mme_laser_pattern (which poisoned every downstream theorem; see REPORT_placeholder_issue.md). For a t-way mode-graded 3-tensor T with grading G and laser pattern S ⊆ (Fin t)³, `laserValueFormula_wz G S` is the supremum over probability distributions π on S of exp(log 2 · (H(π) + (1/3)·Σ_σ π(σ)·log₂(d₀(σ)·d₁(σ)·d₂(σ)))), where d_i(σ) is the K-dimension of grading class G.classOf i σ_i. Specializes to Filmus's closed form for the CW case (see Def_mme_CW_value_function). Suffix `_wz` per feedback_meaningful_suffix.md.
-- source:
--   https://arxiv.org/abs/2212.11824

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_mme_tensor_type_grading
import Definitions.Def_mme_tensor_rank

/-! # Wigderson–Zuiddam laser-method value functional — *real* definition

This file is the **non-placeholder** replacement for `laserValueFormula` from
`Def_mme_laser_pattern`. The original was `:= 1`, a stub; that placeholder
poisoned every downstream theorem that mentioned it (see
`REPORT_placeholder_issue.md`). The present file defines the genuine
Wigderson–Zuiddam §6 laser-method value functional, suffixed `_wz` to
distinguish from the immutable placeholder.

## Mathematical content

For a `t`-way mode-graded 3-tensor `T : TensorObj K 3` with grading `G` and
a laser support pattern `S ⊆ (Fin t)^3`, the laser-method value (a lower
bound on the Strassen-spectrum value of `T` at the trivial spectrum point)
is the supremum over probability distributions `π` supported on `S` of

  log₂ V_S(T, G)  =  H(π)  +  (1/3) · Σ_{σ ∈ S} π(σ) · log₂( d_0(σ) · d_1(σ) · d_2(σ) )

where:
* `H(π) = − Σ π(σ) · log₂ π(σ)` is the Shannon entropy of `π` in bits
  (using the Mathlib convention `0 · log₂ 0 = 0` — automatic from
  `Real.log 0 = 0`);
* `d_i(σ) = dim_K (G.classOf i σ_i)` is the K-dimension of the `σ_i`-th
  grading class of mode `i`. Since `TensorObj` requires
  `[Module.Finite K (V i)]`, every submodule has a well-defined
  `Module.finrank`.

The value `V_S(T, G)` itself is the exponential `2^(log₂ V_S)`.

## Why a `sSup` over distributions

The laser method, at its heart, is a *probabilistic argument*: one chooses a
"weight" distribution `π` over the type-triples in `S` and reads off the
asymptotic value by combinatorial counting (multinomial coefficients) plus
the type-dimension factors. The optimum over `π` is the closed-form value
function. For CW, this optimum has a known closed form (Filmus Theorem 2.5);
for general `(T, G, S)` it does not.

## Bridge to `cwValueFunction`

The CW closed-form value function (`Def_mme_CW_value_function`, suffix
`cwValueFunction q`) is the specialization of this `_wz` functional to the
canonical CW 3-grading of `CWObj K q` with the canonical CW support pattern.
The equality

  `cwValueFunction q = laserValueFormula_wz (canonical_CW_grading q) (canonical_CW_pattern)`

is the content of Filmus Theorem 2.5 and lives as a separate theorem
(`Thm_mme_cwValueFunction_eq_laserValueFormula_wz`, to be uploaded
separately). Until that bridge is closed, the two functionals coexist:
`cwValueFunction` is the *concrete* closed form (and the CW witness
`mme_CW_value_function_ge_5_2 : 5/2 ≤ cwValueFunction 6` is PROVED against
it); `laserValueFormula_wz` is the *abstract* sup-over-distributions form
used by the general laser theorem.

## Suffix `_wz`

Per `feedback_meaningful_suffix`: the suffix names the source paper /
abstraction (Wigderson–Zuiddam) rather than a version number. The original
`laserValueFormula` Def is immutable by name on the platform; this `_wz`
variant lives alongside it. -/

universe u

namespace MME

variable {K : Type u} [Field K]

open BigOperators

/-- The Wigderson–Zuiddam laser-method value functional. See file docstring
for the underlying mathematical content. -/
noncomputable def laserValueFormula_wz
    {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) (S : Finset (Fin t × Fin t × Fin t)) : ℝ :=
  sSup { v : ℝ |
    ∃ π : (Fin t × Fin t × Fin t) → ℝ,
      (∀ σ, σ ∉ S → π σ = 0) ∧
      (∀ σ, 0 ≤ π σ) ∧
      (∑ σ ∈ S, π σ) = 1 ∧
      v = Real.exp (Real.log 2 *
        ( (-(∑ σ ∈ S, π σ * (Real.log (π σ) / Real.log 2)))
        + (1 / 3) *
            (∑ σ ∈ S, π σ *
              (Real.log
                  (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
                   ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
                   ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))
                / Real.log 2)) ) ) }

/-- The trivial probability distribution that puts all mass on a single
chosen point. Used to show that `laserValueFormula_wz` ≥ value at any
single-point distribution — a useful sanity bound. -/
noncomputable def diracProb {t : ℕ}
    (S : Finset (Fin t × Fin t × Fin t)) (σ₀ : Fin t × Fin t × Fin t) :
    (Fin t × Fin t × Fin t) → ℝ :=
  fun σ => if σ = σ₀ ∧ σ ∈ S then 1 else 0

end MME


