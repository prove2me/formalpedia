-- Prove2me | Definitions.Def_KMedian195_Basic
-- name    : KMedian195_Basic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:23.593971+00:00
-- url     : https://prove2.me/theorems/8bb00306-800c-43fc-add2-4772a4e6da27
-- title:
--   KMedian195.Basic
-- statement:
--   This is module `KMedian195.Basic` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   **Contents.** The module is published as a whole: 11 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_Basic`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/Basic.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/Basic.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`), and:
* `Idx` and `suffixRange` are moved to `Imported/KMedian195/Program.lean`, which this file imports.
* `Mathlib.Data.Real.Basic` (deprecated) is `Mathlib.Data.Real.Basic`.
-/
module

public import Definitions.Def_KMedian195_Program
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Real.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.Basic` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
@[expose] public section

open scoped BigOperators

namespace KMedian195

/-- Prefix `{j | j ≤ i}` used in the paper's cumulative constraints. -/
def prefixRange (i : Idx n) : Finset (Idx n) :=
  Finset.univ.filter fun j => j ≤ i

/-- Strict suffix `{i | j < i}` used in the client-credit expression. -/
def strictSuffixRange (j : Idx n) : Finset (Idx n) :=
  Finset.univ.filter fun i => j < i

/-- Closed interval `{p | j ≤ p ∧ p ≤ i}`. -/
def intervalRange (j i : Idx n) : Finset (Idx n) :=
  Finset.univ.filter fun p => j ≤ p ∧ p ≤ i

/-- Half-open interval `{p | j ≤ p ∧ p < i}`. -/
def halfOpenIntervalRange (j i : Idx n) : Finset (Idx n) :=
  Finset.univ.filter fun p => j ≤ p ∧ p < i

@[simp] theorem mem_prefixRange {i j : Idx n} : j ∈ prefixRange i ↔ j ≤ i := by
  simp [prefixRange]

@[simp] theorem mem_suffixRange {j i : Idx n} : i ∈ suffixRange j ↔ j ≤ i := by
  simp [suffixRange]

@[simp] theorem mem_strictSuffixRange {j i : Idx n} : i ∈ strictSuffixRange j ↔ j < i := by
  simp [strictSuffixRange]

@[simp] theorem mem_intervalRange {j i p : Idx n} :
    p ∈ intervalRange j i ↔ j ≤ p ∧ p ≤ i := by
  simp [intervalRange]

@[simp] theorem mem_halfOpenIntervalRange {j i p : Idx n} :
    p ∈ halfOpenIntervalRange j i ↔ j ≤ p ∧ p < i := by
  simp [halfOpenIntervalRange]

/-- The last paper index `n`, represented in Lean's `Fin n` model as `n - 1`. -/
def lastIdx (n : ℕ) [NeZero n] : Idx n :=
  ⟨Nat.pred n, Nat.pred_lt (show n ≠ 0 from NeZero.ne n)⟩

@[simp] theorem le_lastIdx [NeZero n] (i : Idx n) : i ≤ lastIdx n := by
  exact Fin.le_iff_val_le_val.mpr (Nat.le_pred_of_lt i.is_lt)

end KMedian195


