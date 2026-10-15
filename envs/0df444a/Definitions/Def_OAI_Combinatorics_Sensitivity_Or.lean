-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_Or
-- name    : OAI_Combinatorics_Sensitivity_Or
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:40:11.522815+00:00
-- url     : https://prove2.me/theorems/1527686e-49e0-451d-bdf4-e810d87c6ed0
-- title:
--   OR of bits and the OR of disjoint copies of a Boolean function
-- statement:
--   Identify Boolean values with $\{0,1\}$ and let $K$ be a finite set.
--
--   1. **OR of bits.** For $y \in \{0,1\}^K$,
--   $$
--   \mathrm{OR}_K(y) = 1 \iff \exists\, k \in K:\ y_k = 1 ,
--   $$
--   equivalently $\mathrm{OR}_K(y) = 0$ exactly when $y_k = 0$ for every $k \in K$. In particular $\mathrm{OR}_K(\mathbf{0}) = 0$ at the all-zero input $\mathbf{0}$ (and $\mathrm{OR}_K$ is constantly $0$ when $K$ is empty).
--
--   2. **OR of disjoint copies.** For a set $I$ and a Boolean function $f : \{0,1\}^I \to \{0,1\}$, the OR of $|K|$ disjoint copies of $f$ is the block composition $\mathrm{OR}_K \circ f$, a Boolean function on $\{0,1\}^{K \times I}$:
--   $$
--   (\mathrm{OR}_K \circ f)(x) = \bigvee_{k \in K} f(x_{k,\cdot}), \qquad x_{k,\cdot} = \big(x_{(k,a)}\big)_{a \in I} \in \{0,1\}^I .
--   $$
--   Copy $k$ reads only its own block of coordinates $\{k\} \times I$.
--
--   The OR of copies is the balancing step of the construction separating block sensitivity from sensitivity. If $f$ vanishes at $\mathbf{0}$, then so does $\mathrm{OR}_K \circ f$, and its block sensitivity at $\mathbf{0}$ is at least $|K|$ times that of $f$, while its sensitivity is at most the larger of $|K|$ times the sensitivity of $f$ on 0-inputs and the sensitivity of $f$ on 1-inputs; these facts are proved separately.
--
--   **Formalization Note** The definitions are `orBits` (a `Bool` produced with `decide`) and `orCopies (K := K) f`, which is `compose orBits f`. The simp lemmas `orBits_eq_true`, `orBits_eq_false` and `orBits_zero` are the three characterizations in item 1. The index type $K$ carries a `Fintype` instance, while $I$ is an arbitrary type in these definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Or.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Or.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SensitivitySeparation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition

namespace OAI

/-! Balancing the zero and one sensitivities by an OR of disjoint copies. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I K : Type} [Fintype K]

def orBits (x : K → Bool) : Bool := decide (∃ k, x k = true)

@[simp] theorem orBits_eq_true (x : K → Bool) : orBits x = true ↔ ∃ k, x k = true := by
  simp [orBits]

@[simp] theorem orBits_eq_false (x : K → Bool) : orBits x = false ↔ ∀ k, x k = false := by
  simp [orBits]

@[simp] theorem orBits_zero : orBits (fun _ : K => false) = false := by
  simp [orBits]

def orCopies (f : (I → Bool) → Bool) : (K × I → Bool) → Bool := compose orBits f

variable [Fintype I]

end Paper320

end

end OAI


