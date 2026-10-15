-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
-- name    : OAI_Combinatorics_Sensitivity_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:20:41.217016+00:00
-- url     : https://prove2.me/theorems/ffa634e7-5223-4184-b3d2-5b1d0b06564d
-- title:
--   Elementary identities for flipping coordinates of a Boolean input
-- statement:
--   For a set $I$, an input $x \in \{0,1\}^I$ (Boolean values identified with $\{0,1\}$) and a finite set $B \subseteq I$, let $x^{B}$ be the input obtained by flipping exactly the coordinates in $B$:
--
--   $$
--   x^{B}_i = \begin{cases} 1 - x_i, & i \in B, \\ x_i, & i \notin B. \end{cases}
--   $$
--
--   This file records four basic identities, valid for all $x$, $B$ and $i \in I$:
--
--   1. Flipping nothing changes nothing: $x^{\emptyset} = x$.
--   2. Flipping a single coordinate negates it: $(x^{\{i\}})_i = 1 - x_i$.
--   3. Flipping is an involution: $(x^{B})^{B} = x$.
--   4. Flipping $B$ in the all-zero input $\mathbf{0}$ gives the indicator vector of $B$: $(\mathbf{0}^{B})_i = 1$ if $i \in B$ and $(\mathbf{0}^{B})_i = 0$ otherwise.
--
--   These identities are used throughout the computation of sensitivities and block sensitivities, in particular at the all-zero input, where flipping a block produces its indicator vector.
--
--   **Formalization Note** The operation $x^{B}$ is `flip x B` from the base definitions, with `B : Finset I`; the set `I` need not be finite here. The four statements are the simp lemmas `flip_empty`, `flip_singleton_self`, `flip_flip` and `flip_false`; the file introduces no new definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SensitivitySeparation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Finite Boolean flips and the exact maximum/witness interfaces for sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K : Type}

@[simp] theorem flip_empty (x : I → Bool) : flip x ∅ = x := by
  funext i
  simp [flip]

@[simp] theorem flip_singleton_self (x : I → Bool) (i : I) :
    flip x {i} i = !(x i) := by
  simp [flip]

@[simp] theorem flip_flip (x : I → Bool) (B : Finset I) : flip (flip x B) B = x := by
  funext i
  by_cases h : i ∈ B <;> simp [flip, h]

@[simp] theorem flip_false (B : Finset I) (i : I) :
    flip (fun _ => false) B i = decide (i ∈ B) := by
  by_cases h : i ∈ B <;> simp [flip, h]

section Finite

variable [Fintype I]

end Finite
end Paper320

end

end OAI


