-- Prove2me | Definitions.Def_APFPaper5_K1_OrderedScore
-- name    : APFPaper5_K1_OrderedScore
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:08:21.391826+00:00
-- url     : https://prove2.me/theorems/0df6e430-dea8-45e2-9656-a1b974b9d96c
-- title:
--   Supplied ordered pairing, role exchange and conditional K1 predicates
-- statement:
--   Defines bilinearity, nondegeneracy, score reproduction, a faithful nonnegative diagonal, and the symmetric and alternating parts of an exchanged pairing on supplied real modules. No score completion or physical boundary map is constructed.
--
--   **Representation and scope.** Faithfully types the conditional algebraic end of the Paper5 theorem, while explicitly omitting construction from disjoint coarse-graining and quotients by radicals.
--
--   **Supplied data or hypotheses.** Real additive groups/modules VP and VE; function C; supplied linear equivalence theta. IsBilinear, IsNondegenerate, Linearizes and FaithfulNonnegDiagonal are separately defined predicates, not asserted inputs.
--
--   **Claim boundaries.** The header saying destination is not ruled is superseded by author ruling 5: reference mission. The title says three hypotheses while four predicates are defined; use the proposed neutral title. theta remains an isomorphism by author direction, though its invertibility is unused in the symmetrization proofs.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K1_OrderedScore.lean; Sib v15, SHA-256 3ab1a0ecbef51688b11d1827780382cf1d466122669d530de6009ed47b4f7160. [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'lines_or_section': '312-391;3038-3041'}, {'path': 'Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_eight_decisions_2026-11-12.md', 'lines_or_section': '5,8'}]

/-
APF — named hypotheses for Paper 5 obligation K1. DRAFT for author and cold review. Not gated, not released, not
uploaded. Where K-target predicates live (Foundation Ledger or a reference mission) is not ruled; see the note.
name: APFPaper5_K1_OrderedScore
title: The ordered completed score and its boundary-role exchange: the data and the three hypotheses of K1
inputs_revision: 2026-10-04.1 (consumes no declared input)
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Technical Supplement v7.33:312-351 (the scalar ledger does not determine the ordered score; remaining
  burden), 353-382 (ordered-score bilinearization theorem), 3038-3041 (obligation K1).
statement: Data: real vector spaces VP (completed preparation classes, linearized and reduced) and VE (completed
  terminal classes); an ordered pairing C on VE x VP; a linear isomorphism theta from VP to VE.
  Hypotheses, each a named predicate and none asserted: IsBilinear C; IsNondegenerate C; Linearizes (the pairing
  reproduces a given score on the classes); FaithfulNonnegDiagonal C theta (the diagonal x |-> C (theta x) x is
  nonnegative and vanishes only at zero). Definitions: the ledger form (symmetric part) and the orientation form
  (alternating part) of the exchanged pairing.
what is NOT here: the construction of VP, VE and C from a score table by linearization and quotient by radicals
  (the archive's finite-pairing modules do this on another vocabulary); separate additivity of the score under
  disjoint coarse-graining; any claim that the diagonal is an admissibility cost.
no structure, no class, no Prop-valued field.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Equiv.Defs

set_option autoImplicit false
namespace APFPaper5.K1

variable {VP VE : Type*} [AddCommGroup VP] [Module ℝ VP] [AddCommGroup VE] [Module ℝ VE]

/-- The ordered pairing is real-bilinear. Stated on a function; no bundled bilinear-map type is imported. -/
def IsBilinear (C : VE → VP → ℝ) : Prop :=
  (∀ e e' p, C (e + e') p = C e p + C e' p) ∧ (∀ (r : ℝ) e p, C (r • e) p = r * C e p) ∧
  (∀ e p p', C e (p + p') = C e p + C e p') ∧ (∀ (r : ℝ) e p, C e (r • p) = r * C e p)

/-- Neither side has a nonzero vector paired to zero with everything (the state after quotienting radicals). -/
def IsNondegenerate (C : VE → VP → ℝ) : Prop :=
  (∀ e, (∀ p, C e p = 0) → e = 0) ∧ (∀ p, (∀ e, C e p = 0) → p = 0)

/-- K1.a, the part that can be typed without constructing the spaces: the pairing reproduces a given ordered score
`s` on the classes of completed terminal tests `E` and completed preparations `P`. -/
def Linearizes {P E : Type*} (s : E → P → ℝ) (prepClass : P → VP) (testClass : E → VE)
    (C : VE → VP → ℝ) : Prop :=
  ∀ e p, C (testClass e) (prepClass p) = s e p

/-- K1.c: the diagonal of the exchanged pairing is nonnegative and faithful. -/
def FaithfulNonnegDiagonal (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE) : Prop :=
  (∀ x, 0 ≤ C (theta x) x) ∧ (∀ x, C (theta x) x = 0 → x = 0)

/-- The ledger form: the symmetric part of the exchanged pairing. -/
noncomputable def ledgerForm (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE) (x y : VP) : ℝ :=
  (C (theta x) y + C (theta y) x) / 2

/-- The orientation form: the alternating part of the exchanged pairing. -/
noncomputable def orientationForm (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE) (x y : VP) : ℝ :=
  (C (theta x) y - C (theta y) x) / 2

end APFPaper5.K1


