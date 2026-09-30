-- Prove2me | Definitions.Def_capacityFourLabelAtoms
-- name    : capacityFourLabelAtoms
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-07T18:03:58.586219+00:00
-- url     : https://prove2.me/theorems/46058151-e4fe-4c2a-ab17-bf2e8e0906b9
-- title:
--   Four-label partition laws and refinement couplings
-- statement:
--   On labels $1,2,3,4$, represent the four block families $12\mid34$, $1\mid2\mid3\mid4$, $1\mid2\mid34$, and $12\mid3\mid4$. Their exact block indicators are $I_B(P)=\mathbf1_{\{B\in P\}}$, with values in $\mathbb Q$. Uniform two-atom averages define the laws
--
--   $$\mu_+=\tfrac12(\delta_{12\mid34}+\delta_{1\mid2\mid3\mid4}),\qquad \mu_-=\tfrac12(\delta_{1\mid2\mid34}+\delta_{12\mid3\mid4}).$$
--
--   Write $P\preceq Q$ when every block of $P$ is contained in some block of $Q$, so refinement is directed from fine to coarse. A uniform two-atom coupling is a table $K\in\mathbb Q_{\geq0}^{2\times2}$ with every row and column sum equal to $1/2$. This bundle fixes the explicit atoms, incidence scores, refinement relation, and coupling representation used by the correlation and non-coupling results. It does not assume a coupling supported on refinement exists. The implementation uses zero-based labels and retains the required decision instances.
-- source:
--   The four-label correlation threshold, Proposition 1.1 and equations (1.2)–(1.3). Unpublished research note (2026), N4_BLOCK_CORRELATION_NOTE.md, SHA-256 a9b67c132ca0e0af807fb917ca2322833b84e162c45a4da7329ee88fbe4f1c83. Exact formal source: formal_capacity/FormalCapacity/Finite/N4.lean, source-file SHA-256 280e7a5db975df324036a6fa34b42c689519d3d508ba10e85a18645f77ddeb26. Local source archive; no public repository URL or commit is asserted. Upload checked with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib

set_option autoImplicit false

/-!
# The four-label correlation obstruction

This file kernel-checks the signed square

`12|34 + 1|2|3|4 = 1|2|34 + 12|3|4`

at every block-incidence coordinate.  The four atoms are represented by
their finite sets of blocks.  `n4Atom_isPartition` verifies that each label
belongs to exactly one nonempty block, so this concrete representation does
not hide a partition-validity assumption.
-/

namespace FormalCapacity.Finite

open Finset

abbrev Label4 := Fin 4

/-- The four partition atoms in the signed square. -/
inductive N4Atom
  | plusCoarse    -- `12|34`
  | plusDiscrete  -- `1|2|3|4`
  | minusLeft     -- `1|2|34`
  | minusRight    -- `12|3|4`
  deriving DecidableEq

/-- Explicit blocks of the four atoms (labels are zero-based). -/
def N4Atom.blocks : N4Atom → Finset (Finset Label4)
  | .plusCoarse => {{0, 1}, {2, 3}}
  | .plusDiscrete => {{0}, {1}, {2}, {3}}
  | .minusLeft => {{0}, {1}, {2, 3}}
  | .minusRight => {{0, 1}, {2}, {3}}





/-- The rational first-order incidence coordinate of a block. -/
def N4Atom.blockIndicator (P : N4Atom) (B : Finset Label4) : ℚ :=
  if B ∈ P.blocks then 1 else 0



/-- Average a statistic under a uniform two-atom law. -/
def n4TwoAtomAverage (P Q : N4Atom) (F : N4Atom → ℚ) : ℚ :=
  (F P + F Q) / 2





/-- Refinement: every source block is contained in a target block. -/
def N4Atom.Refines (P Q : N4Atom) : Prop :=
  ∀ B ∈ P.blocks, ∃ C ∈ Q.blocks, B ⊆ C

instance (P Q : N4Atom) : Decidable (P.Refines Q) := by
  unfold N4Atom.Refines
  exact Finset.decidableDforallFinset

/-- A coupling of two uniform two-atom laws. -/
structure UniformTwoCoupling where
  mass : Bool → Bool → ℚ
  nonneg : ∀ i j, 0 ≤ mass i j
  row : ∀ i, mass i false + mass i true = 1 / 2
  col : ∀ j, mass false j + mass true j = 1 / 2

/-- Atoms of the positive law. -/
def plusAtom : Bool → N4Atom
  | false => .plusCoarse
  | true => .plusDiscrete

/-- Atoms of the negative law. -/
def minusAtom : Bool → N4Atom
  | false => .minusLeft
  | true => .minusRight















end FormalCapacity.Finite


