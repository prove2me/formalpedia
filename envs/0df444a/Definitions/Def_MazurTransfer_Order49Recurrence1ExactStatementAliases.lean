-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence1ExactStatementAliases
-- name    : MazurTransfer_Order49Recurrence1ExactStatementAliases
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T05:35:05.929356+00:00
-- url     : https://prove2.me/theorems/67268f02-7f62-4bb0-bb43-e64232a23e7b
-- title:
--   Exact statements for five first-recurrence polynomial identities
-- statement:
--   These five transparent predicates express the exact original coefficient conversion and normalized polynomial identities in the first order-seven pseudo-division recurrence. Each is definitionally equal to the corresponding original proposition. They carry no proof or extra hypothesis. Named downstream consumers are the six original first-recurrence inner identities and the full order49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; Apache-2.0 attribution preserved. Exact original Lean AST signature ranges and resolved references determine every proposition. Each proposition is independently kernel-reflexivity checked against its original theorem type; public exact conversion bridges are checked separately. All coefficient data were previously independently compared with the WIP originals. This changed representation addresses five retained 300-second statement-publication failures without changing mathematical scope.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData1

def MazurTransfer.Order49Recurrence1ExactStatementAliases.spec_recurrence1NormalizedInner5 : Prop :=
  MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source5 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder25 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientConstant +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Exceptional *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35
#print axioms MazurTransfer.Order49Recurrence1ExactStatementAliases.spec_recurrence1NormalizedInner5

def MazurTransfer.Order49Recurrence1ExactStatementAliases.spec_remainder2Coefficient3_eq_normalized : Prop :=
  MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23
#print axioms MazurTransfer.Order49Recurrence1ExactStatementAliases.spec_remainder2Coefficient3_eq_normalized

def MazurTransfer.Order49Recurrence1ExactStatementAliases.spec_remainder3Coefficient2_eq_normalized : Prop :=
  MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient2 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder32
#print axioms MazurTransfer.Order49Recurrence1ExactStatementAliases.spec_remainder3Coefficient2_eq_normalized

def MazurTransfer.Order49Recurrence1ExactStatementAliases.spec_remainder3Coefficient4_eq_normalized : Prop :=
  MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34
#print axioms MazurTransfer.Order49Recurrence1ExactStatementAliases.spec_remainder3Coefficient4_eq_normalized

def MazurTransfer.Order49Recurrence1ExactStatementAliases.spec_remainder3Coefficient5_eq_normalized : Prop :=
  MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35
#print axioms MazurTransfer.Order49Recurrence1ExactStatementAliases.spec_remainder3Coefficient5_eq_normalized


