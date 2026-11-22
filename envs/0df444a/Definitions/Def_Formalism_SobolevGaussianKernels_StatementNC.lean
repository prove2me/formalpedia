-- Prove2me | Definitions.Def_Formalism_SobolevGaussianKernels_StatementNC
-- name    : Formalism_SobolevGaussianKernels_StatementNC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:50.366907+00:00
-- url     : https://prove2.me/theorems/17a569c6-8de6-45de-b99b-0c3c26f94ce5
-- title:
--   Statement NC
-- statement:
--   Definitions and structural lemmas for Statement NC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/StatementNC.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SL.NC
open Finset
def NormCount : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [DecidableEq K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n : ℕ) (c : K),
      |((univ.filter (fun y : Fin n → L => ∑ i, Algebra.norm K (y i) = c)).card : ℝ)
          - (Fintype.card L : ℝ) ^ n / (Fintype.card K : ℝ)|
        ≤ (1 - 1 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ n
def NormCharMean : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [DecidableEq K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (ψ : AddChar K ℂ), (∃ c, ψ c ≠ 1) →
    ∀ (n : ℕ) (ℓ : Fin n → L), ℓ ≠ 0 →
      ‖∑ y ∈ univ.filter (fun y : Fin n → L => ∑ i, Algebra.norm K (y i) = 0),
          ψ (∑ i, Algebra.trace K L (ℓ i * y i))‖
        ≤ (1 - 1 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ n
end Formalism.SL.NC


