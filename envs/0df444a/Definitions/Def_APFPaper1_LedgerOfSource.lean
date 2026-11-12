-- Prove2me | Definitions.Def_APFPaper1_LedgerOfSource
-- name    : APFPaper1_LedgerOfSource
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:15:59.155318+00:00
-- url     : https://prove2.me/theorems/e62cbe83-15b7-459a-9a2b-b6b81a4794bc
-- title:
--   The ledger of a source data record
-- statement:
--   Fix a protocol class, distinction and record types, calibrated whole-resource bills, maintained records, sufficient support and actual-use data. Choose a designated protocol $p_0$. The source adapter constructs a CostLedger with that protocol as its null protocol and with the supplied support relations unchanged.
--
--   Its prices satisfy the defining convention
--
--   $$\operatorname{price}(p_0)=0,\qquad \operatorname{price}(p)=\chi(r(p))\quad(p\ne p_0).$$
--
--   The adapter itself assumes no law about the data. The separate cost and support-novelty bridge theorems explicitly require $\chi(r(p_0))=0$ to identify all ledger prices with the original calibrated bills. This conditional bridge does not prove that an arbitrary chosen $p_0$ is the original empty protocol or that an arbitrary data instance describes the physical source.
--
--   **Formalization note.** Foundation Inputs revision 2026-10-04.1; independent source review brook-2026-11-12-cold_fidelity_review. Stated hypotheses and representation limits are retained.
-- source:
--   Paper 1 Technical Supplement v9.28 and FOUNDATION_INPUTS.json revision 2026-10-04.1; exact reviewed module Definitions.Def_APFPaper1_LedgerOfSource; source SHA256 784e4264073362c316667ed7f3d263f5bf1b7b2940ac73085957261a1166326e. See the source header for original v9.27 line references and the November 11 testedness ruling.

/-
APF Foundation Ledger — definition node (Batch 1, bridge)
name: APFPaper1_LedgerOfSource
title: The ledger of a source data record
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.27:1754-1757,1778-1787,2188-2221,2880-2883. Builds a CostLedger Ledger from the
  source data used by B03/B05 (whole resource, calibration, maintained, sufficient, usesToRealize) and a
  designated null protocol.
statement: Ledger.ofSource p0 wholeResource calibration maintained sufficient usesToRealize is the Ledger whose
  null protocol is p0, whose non-null bill is the calibrated whole resource, and whose support predicates are
  the given ones. Its price agrees with the calibrated whole resource at every protocol exactly when the null
  protocol's calibrated bill is zero; that null-bill convention (Supplement 2880-2883) is a hypothesis of the
  bridge theorems, not a field.
-/
import Definitions.Def_APFPaper1_CostLedger
import Definitions.Def_APFPaper1_FamilyCost

set_option autoImplicit false
namespace APFPaper1.Foundation

/-- The Ledger of a source data record. -/
noncomputable def Ledger.ofSource {D P R Record : Type*} (p0 : P)
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) : Ledger D P Record where
  nullProtocol := p0
  nonNullBill := fun q => calibration (wholeResource q.val)
  maintained := maintained
  sufficient := sufficient
  usesToRealize := usesToRealize

end APFPaper1.Foundation


