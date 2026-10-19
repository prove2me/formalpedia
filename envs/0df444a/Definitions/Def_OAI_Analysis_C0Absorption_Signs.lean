-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Signs
-- name    : OAI_Analysis_C0Absorption_Signs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T20:55:23.384563+00:00
-- url     : https://prove2.me/theorems/3313eead-640d-49e1-92be-3028f6e8df58
-- title:
--   Real signs from booleans and sign flips
-- statement:
--   Signed sums $\sum_i\pm f_i$ of test functions appear throughout the construction, with the signs encoded by booleans.
--
--   1. **Real sign.** $\mathrm{realSign}(b)=1$ if $b$ is true and $-1$ if $b$ is false, so $|\mathrm{realSign}(b)|=1$ and $\mathrm{realSign}(\lnot b)=-\mathrm{realSign}(b)$.
--   2. **Flipping one sign.** For an index $i$ among $n$, $\mathrm{flipSign}(i)$ is the involution of $\{\text{true},\text{false}\}^n$ that negates the $i$-th entry and keeps the others:
--   $$
--   \mathrm{flipSign}(i)(\varepsilon)_j=\begin{cases}\lnot\varepsilon_j,&j=i,\\\varepsilon_j,&j\ne i.\end{cases}
--   $$
--   Averaging over sign patterns paired by this involution isolates individual terms.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Signs.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Signs.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion

namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section Signs

def realSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem realSign_true : realSign true = 1 := rfl
@[simp] theorem realSign_false : realSign false = -1 := rfl
@[simp] theorem abs_realSign (b : Bool) : |realSign b| = 1 := by cases b <;> norm_num

def flipSign {n : ℕ} (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun ε j := if j = i then !(ε j) else ε j
  invFun ε j := if j = i then !(ε j) else ε j
  left_inv ε := by funext j; by_cases h : j = i <;> simp [h]
  right_inv ε := by funext j; by_cases h : j = i <;> simp [h]

@[simp] theorem realSign_not (b : Bool) : realSign (!b) = -realSign b := by
  cases b <;> norm_num

end Signs

end
end C0Absorption

end OAI


