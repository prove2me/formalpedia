-- Prove2me | Definitions.Def_PauliMatrix_IsAnticommuting
-- name    : PauliMatrix_IsAnticommuting
-- status  : Definition
-- author  : @LG
-- created : 2026-11-25T01:06:58.837808+00:00
-- url     : https://prove2.me/theorems/dbd69a23-4b35-46ee-ad98-71e49625fe53
-- title:
--   Anticommuting families of $2\times2$ matrices: $\tau_a\tau_b+\tau_b\tau_a=2\delta_{ab}I_2$
-- statement:
--   A family $\tau:\iota\to M_2(\mathbb{C})$ of $2\times2$ complex matrices, indexed by a type $\iota$ with decidable equality, is **anticommuting** when
--   $$\tau_a\tau_b+\tau_b\tau_a=2\delta_{ab}\,I_2\qquad\text{for all }a,b\in\iota.$$
--   Equivalently, each member squares to the identity, $\tau_a^2=I_2$, and two distinct members anticommute, $\tau_a\tau_b=-\tau_b\tau_a$. The three Pauli matrices are the prototypical example. This predicate is the hypothesis of the $2\times2$ bound proved in this mission: an anticommuting family has at most three members, the fact that excludes size two for the Dirac gamma matrices.
--
--   **Formalization Note.** The scalar $2\delta_{ab}$ is written `(if a = b then 2 else 0 : ℂ)`; `1` is the $2\times2$ identity matrix. The index type is universe-polymorphic and may be empty or infinite (the predicate itself imposes no finiteness).
-- source:
--   Physlib, `PhyslibAlpha/Relativity/PauliMatrices/Anticommuting.lean`, definition `PauliMatrix.IsAnticommuting` (L56–L58). https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/PhyslibAlpha/Relativity/PauliMatrices/Anticommuting.lean#L56-L58

import Mathlib

namespace PauliMatrix

open Matrix

/-- A family of `2 × 2` matrices with `τ_a τ_b + τ_b τ_a = 2 δ_ab 1`. -/
def IsAnticommuting {ι : Type*} [DecidableEq ι] (τ : ι → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ a b, τ a * τ b + τ b * τ a = (if a = b then 2 else 0 : ℂ) • 1

end PauliMatrix


