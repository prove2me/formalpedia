-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointSchedule
-- name    : ConsistentSubmodular_Randomized_Reduction_CheckpointSchedule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:35.420869+00:00
-- url     : https://prove2.me/theorems/e9d53ea6-c66b-47f4-b1fc-ddef90594a18
-- title:
--   Checkpoint schedule: transition paths between cores and subblock progress
-- statement:
--   Sets are subsets of the stream elements $\{0,\dots,n-1\}$ (element $e$ is the paper's $x_{e+1}$).
--
--   - `pre D r` is the set of the first $r$ elements of the finite set $D$ in a fixed enumeration (its list of elements), so $|{\rm pre}(D,r)|=\min(r,|D|)$.
--   - `path C A r` is the core after $r$ operations of the transition from $C$ to $A$: the first $r$ elements of $C\setminus A$ are deleted and the first $r$ elements of $A\setminus C$ are inserted,
--   $$\bigl(C\setminus {\rm pre}(C\setminus A,r)\bigr)\ \cup\ {\rm pre}(A\setminus C,r).$$
--   - `operations C A` is the number of operations of the transition, $\max(|C\setminus A|,\,|A\setminus C|)$.
--
--   For a block of $\ell$ updates cut into $h$ subblocks (all quantities natural numbers, with integer division):
--
--   - `lo ℓ h σ` $=\lfloor \sigma\ell/h\rfloor$ and `hi ℓ h σ` $=\lfloor(\sigma+1)\ell/h\rfloor$; subblock $\sigma$ consists of the updates $\mathrm{lo}+1,\dots,\mathrm{hi}$.
--   - `elapsed ℓ h σ r` $=\min(\mathrm{hi}(\sigma),r)-\mathrm{lo}(\sigma)$ (truncated subtraction), the number of updates of subblock $\sigma$ among the first $r$ updates of the block.
--   - `done ℓ h s R σ r` $=\min\bigl(R,\ s\cdot \mathrm{elapsed}(\ell,h,\sigma,r)\bigr)$, the number of operations performed after $r$ updates of a block whose selected subblock is $\sigma$, with $s$ operations per update and $R$ operations in total.
--
--   The file also proves the basic facts that `pre D 0` is empty and that `path C A 0` equals $C$.
--
--   These definitions describe how Algorithm 1 of the randomized reduction (Lemma 1, Appendix A.3) turns the old core into the new core gradually, by a bounded number of insertions and deletions per update, inside a randomly selected subblock.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointSchedule.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

/-- The first `r` elements of `D` in a fixed enumeration. -/
def pre (D : Finset (Fin n)) (r : ℕ) : Finset (Fin n) := (D.toList.take r).toFinset

@[simp] theorem pre_zero (D : Finset (Fin n)) : pre D 0 = ∅ := by
  simp [pre]

/-- The core after `r` operations of the transition from `C` to `A`: the first
`r` elements of `C \ A` are deleted and the first `r` elements of `A \ C` are
inserted. -/
def path (C A : Finset (Fin n)) (r : ℕ) : Finset (Fin n) :=
  (C \ pre (C \ A) r) ∪ pre (A \ C) r

/-- The number of operations of the transition, `max(|C \ A|, |A \ C|)`. -/
def operations (C A : Finset (Fin n)) : ℕ := max (C \ A).card (A \ C).card

@[simp] theorem path_zero (C A : Finset (Fin n)) : path C A 0 = C := by
  simp [path]

/-- Subblock `σ` of a block of `ℓ` updates consists of the updates
`lo σ + 1, ..., hi σ`. -/
def lo (ℓ h σ : ℕ) : ℕ := σ * ℓ / h

/-- The last update of subblock `σ`. -/
def hi (ℓ h σ : ℕ) : ℕ := (σ + 1) * ℓ / h

/-- The number of updates of subblock `σ` among the first `r` updates of the
block. -/
def elapsed (ℓ h σ r : ℕ) : ℕ := min (hi ℓ h σ) r - lo ℓ h σ

/-- The number of operations performed after `r` updates of a block whose
selected subblock is `σ`, with `s` operations per update and `R` operations
in total. -/
def done (ℓ h s R σ r : ℕ) : ℕ := min R (s * elapsed ℓ h σ r)

end ConsistentSubmodular.Checkpoints

end


