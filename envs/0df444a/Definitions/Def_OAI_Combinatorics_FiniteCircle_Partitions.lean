-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions
-- name    : OAI_Combinatorics_FiniteCircle_Partitions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:17:17.640757+00:00
-- url     : https://prove2.me/theorems/2a6a1b62-ebe3-4e32-a413-759e24da02a8
-- title:
--   Finite probability laws, product selection weights and random cut labels
-- statement:
--   This file provides a minimal language of finite probability distributions together with the product construction behind random partitions.
--
--   1. **Finite laws.** For a finite set $\Omega$, a finite law $\mu$ on $\Omega$ is a weight function $\mu:\Omega\to\mathbb{R}$ with $\mu(\omega)\ge0$ for every $\omega$ and $\sum_{\omega\in\Omega}\mu(\omega)=1$. For $f:\Omega\to\mathbb{R}$ and a predicate $P$ on $\Omega$, the expectation and the probability of the event $P$ are
--   $$
--   \mathbb{E}_\mu[f]=\sum_{\omega\in\Omega}\mu(\omega)\,f(\omega),\qquad \mu(P)=\sum_{\omega\in\Omega:\ P(\omega)}\mu(\omega).
--   $$
--   The module records that $\mathbb{E}_\mu[a]=a$ for a constant $a$, that the sure event has probability $1$, and that the impossible event has probability $0$.
--
--   2. **Selection weights.** For a finite index set $I$, numbers $q:I\to\mathbb{R}$ and a selection pattern $s:I\to\{0,1\}$,
--   $$
--   \operatorname{sel}_q(s)=\prod_{i\in I}\begin{cases}1-q_i & \text{if } s_i=1,\\ q_i & \text{if } s_i=0.\end{cases}
--   $$
--   When $0\le q_i\le1$ for all $i$, this is the probability of the pattern $s$ if every index $i$ is selected independently with probability $1-q_i$.
--
--   3. **Selection labels.** Given Boolean functions (cuts) $c_i:X\to\{0,1\}$ for $i\in I$ and a pattern $s$, the label of $x\in X$ is the Boolean vector
--   $$
--   \operatorname{lab}_{c,s}(x)=\bigl(s_i\wedge c_i(x)\bigr)_{i\in I}\in\{0,1\}^I ,
--   $$
--   which records, for the selected indices only, on which side of the cut $c_i$ the point $x$ lies.
--
--   4. **Partition space.** $\operatorname{Part}(X)=\{0,1\}^{\{0,1\}^X}$ is the set of Boolean functions on the set of all cuts $c:X\to\{0,1\}$. Selection patterns indexed by all cuts of $X$, and the labels they produce, are both elements of this set.
--
--   Two points $x,y$ receive the same label exactly when no selected cut separates them, which under independent selections happens with probability $\prod_{i:\,c_i(x)\neq c_i(y)}q_i$. Taking $q_c=e^{-\alpha a_c}$, for a parameter $\alpha\ge0$ and a decomposition $\rho(x,y)=\sum_c a_c\,[c(x)\neq c(y)]$ of a distance into cuts with coefficients $a_c\ge0$ gives a random partition of a finite set $X$ in which $x$ and $y$ lie in the same part with probability $e^{-\alpha\rho(x,y)}$; such random partitions supply the randomness of the low-distortion embeddings in the upper bound.
--
--   **Formalization Note** `FiniteLaw Ω` (for `[Fintype Ω]`) is a structure with fields `weight`, `nonneg` and `total`; `FiniteLaw.expect` and `FiniteLaw.event` are the two sums of item 1, and `expect_const`, `event_true`, `event_false` are simp lemmas. `selectionWeight q s` and `selectionLabel c s x` are items 2 and 3; no constraint on the values of `q` is built into `selectionWeight`. `PartitionSpace X` abbreviates the function type `(X -> Bool) -> Bool`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Partitions.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Partitions.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

noncomputable def expect (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * f ω

noncomputable def event (μ : FiniteLaw Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if P ω then μ.weight ω else 0

@[simp] theorem expect_const (μ : FiniteLaw Ω) (a : ℝ) : μ.expect (fun _ => a) = a := by
  simp only [expect, ← Finset.sum_mul, μ.total, one_mul]

@[simp] theorem event_true (μ : FiniteLaw Ω) : μ.event (fun _ => True) = 1 := by
  simp [event, μ.total]

@[simp] theorem event_false (μ : FiniteLaw Ω) : μ.event (fun _ => False) = 0 := by simp [event]

end FiniteLaw

noncomputable def selectionWeight {I : Type*} [Fintype I] (q : I → ℝ) (s : I → Bool) : ℝ :=
  ∏ i, if s i then 1 - q i else q i

def selectionLabel {I X : Type*} (c : I → X → Bool) (s : I → Bool) (x : X) : I → Bool :=
  fun i => s i && c i x

abbrev PartitionSpace (X : Type*) := (X → Bool) → Bool

end FiniteCircle

end OAI


