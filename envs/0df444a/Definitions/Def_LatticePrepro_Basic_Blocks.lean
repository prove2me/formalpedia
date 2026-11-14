-- Prove2me | Definitions.Def_LatticePrepro_Basic_Blocks
-- name    : LatticePrepro_Basic_Blocks
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:19:14.049658+00:00
-- url     : https://prove2.me/theorems/9b05d14e-0516-4894-9fa4-80078745fff9
-- title:
--   Binary and block-sparse vectors (Definitions 3.10 and 4.4)
-- statement:
--   Fix a finite set $\iota$ of coordinates, a set $\beta$ of block labels, and a map $\mathrm{blk}\colon \iota \to \beta$ assigning each coordinate to its block. Vectors are functions $y\colon \iota \to F$ with entries in a type $F$ that has a zero (and a one, for binary vectors). The bundle defines:
--
--   - **Binary vectors** (`IsBinary`): $y$ is binary if $y_i \in \{0,1\}$ for every coordinate $i$.
--   - **Support in a block** (`blockSupport`): for a block label $s \in \beta$,
--   $$\operatorname{supp}_s(y) = \{\, i \in \iota : \mathrm{blk}(i) = s,\ y_i \neq 0 \,\},$$
--   the set of nonzero coordinates of $y$ that lie in block $s$.
--   - **At most one nonzero coordinate per block** (`AtMostOnePerBlock`): $|\operatorname{supp}_s(y)| \le 1$ for every $s \in \beta$.
--   - **Exactly one nonzero coordinate per block** (`ExactlyOnePerBlock`): $|\operatorname{supp}_s(y)| = 1$ for every $s \in \beta$.
--
--   These are the sparsity patterns used throughout the paper. YES instances of the block-sparse linear-system problem (Definition 3.10) have a binary solution with at most one nonzero coordinate per block, and the completeness property of a moment representation (Definition 4.4) asks for binary evaluation tables with exactly one nonzero coordinate in each block.
--
--   **Formalization Note**: The partition into blocks is encoded by the map $\mathrm{blk}$; blocks need not have equal size here (equal block sizes are imposed where needed, e.g. in moment representations). The conditions quantify over every label $s \in \beta$, so `ExactlyOnePerBlock` forces every label to have a nonempty block. `blockSupport` requires decidable equality on $\beta$ and on $F$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Definition 3.10 (\label{def:block-sparse-linear-system}) and Definition 4.4 (\label{def:moment-representation}); Lean: LatticePrepro/Basic/Blocks.lean, LatticePrepro.IsBinary, LatticePrepro.blockSupport, LatticePrepro.AtMostOnePerBlock, LatticePrepro.ExactlyOnePerBlock

import Mathlib

/-!
# Block-sparse vectors

Vectors `y : ι → F` whose coordinates are partitioned into blocks by a map `blk : ι → β`.
We define binary vectors and vectors with at most (exactly) one nonzero entry per block,
and relate them to the Hamming weight `hammingNorm`.
-/

namespace LatticePrepro

variable {ι β F : Type*}

/-- A vector is binary if every coordinate is `0` or `1`. -/
def IsBinary [Zero F] [One F] (y : ι → F) : Prop := ∀ i, y i = 0 ∨ y i = 1

variable [Fintype ι] [DecidableEq β]

/-- The nonzero coordinates of `y` inside the block `s`. -/
def blockSupport [Zero F] [DecidableEq F] (blk : ι → β) (y : ι → F) (s : β) : Finset ι :=
  Finset.univ.filter fun i => blk i = s ∧ y i ≠ 0

/-- At most one nonzero coordinate in every block. -/
def AtMostOnePerBlock [Zero F] [DecidableEq F] (blk : ι → β) (y : ι → F) : Prop :=
  ∀ s, (blockSupport blk y s).card ≤ 1

/-- Exactly one nonzero coordinate in every block. -/
def ExactlyOnePerBlock [Zero F] [DecidableEq F] (blk : ι → β) (y : ι → F) : Prop :=
  ∀ s, (blockSupport blk y s).card = 1

end LatticePrepro


