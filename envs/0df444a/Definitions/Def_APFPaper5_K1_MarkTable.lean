-- Prove2me | Definitions.Def_APFPaper5_K1_MarkTable
-- name    : APFPaper5_K1_MarkTable
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:07:53.941948+00:00
-- url     : https://prove2.me/theorems/36dc5dc8-d451-44ef-b76f-b124df31a8ef
-- title:
--   Finite real tables and Boolean weighted-overlap tables
-- statement:
--   Defines the finite coefficient form, the interchangeable-table predicate, Boolean indicator and weighted atom-overlap table. These are supplied mathematical data and predicates.
--
--   **Representation and scope.** A finite Gram-style score vocabulary inspired by K1; atomTable alone does not encode the Paper1 defender, normalized probabilities or the algebraic PairNumbers relation.
--
--   **Supplied data or hypotheses.** Finite index and atom types where summed; arbitrary real table or weights. Interchangeable is the predicate G(i,j)=1 on the diagonal and c off it, not an asserted law.
--
--   **Claim boundaries.** Do not call arbitrary atomTable entries normalized pair numbers; diagonal entries need not be one. Negative weights are allowed in the definition; nonnegativity is a theorem hypothesis.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K1_MarkTable.lean; Sib v15, SHA-256 14370b31453796fca7f904748173724be88a698b328933b9c7b6e7215f0738a7. [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'lines_or_section': '353-391;3038-3041'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'lines_or_section': '3721-3749'}]

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_MarkTable
title: Tables of pair numbers on finitely many marks
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
statement: tableForm is the form of a real table on coefficient vectors; Interchangeable says each mark scores 1 against itself and any two different marks score the same c; ind sends a Boolean reading to 1 or 0; atomTable is the table read off weights on the atoms of a record space. Supplied data only; no law is assumed. Moved out of theorem files on 2026-11-12 (one module per node).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
namespace APFPaper5.K1

universe u v
variable {ι : Type u} [Fintype ι] {W : Type v} [Fintype W]

/-- The form of a table of pair numbers on coefficient vectors. -/
def tableForm (G : ι → ι → ℝ) (x y : ι → ℝ) : ℝ := ∑ i, ∑ j, x i * G i j * y j

/-- Each mark scores 1 against itself and every two different marks score the same number `c`. -/
def Interchangeable [DecidableEq ι] (G : ι → ι → ℝ) (c : ℝ) : Prop :=
  ∀ i j, G i j = if i = j then 1 else c

/-- 1 for a marked reading, 0 for an unmarked one. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

/-- The table of pair numbers read off weights on the atoms of a record space. -/
def atomTable (w : W → ℝ) (mark : ι → W → Bool) (i j : ι) : ℝ :=
  ∑ a, w a * (ind (mark i a) * ind (mark j a))

end APFPaper5.K1


