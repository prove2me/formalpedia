-- Prove2me | Definitions.Def_MazurTransfer_Order49ResultantRecurrence6MinimalData
-- name    : MazurTransfer_Order49ResultantRecurrence6MinimalData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T21:41:12.793649+00:00
-- url     : https://prove2.me/theorems/ceb7124f-dc66-40b7-892f-6a8be13c8958
-- title:
--   Order-49 sixth recurrence: exact final remainder, quotient and exceptional factor
-- statement:
--   In $\mathbb Q[T][X]$, retain the fixed final remainder $R_8=-1$, the linear pseudo-division quotient $Q_6$, and the exceptional factor $\varepsilon_6$. The proposition for the final step is $$a_7^2 R_6=R_7Q_6+a_6^2\varepsilon_6R_8,$$ where $a_i$ is the prescribed leading coefficient of $R_i$. These definitions specify the unchanged original data and the identity to be proved; they assume no arithmetic identity.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Apache-2.0 original header retained. All eight pure original definitions selected and audited at complete Lean AST ranges; their type and value bytes are unchanged and every value was compared to the original by rfl. Boundary: original step-six pure data only, excluding later normalized arithmetic tables. Named downstream consumers: the exact original recurrence6 theorem and generic_resultant_eq_resultantFactorData.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData5

/-!
# Step 6 data for the order-seven branch-zero resultant PRS

This serial data shard records one normalized primitive remainder and
exceptional content factor. Its linear pseudo-division quotient is
derived from leading coefficients and checked by the Lean recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

noncomputable section

def remainder8Coefficient0Chunk0 : Coefficient :=
  coefficientTerm 0
    (-((1 : ℚ)))

def remainder8Coefficient0Block0 : Coefficient :=
  remainder8Coefficient0Chunk0

def remainder8Coefficient0 : Coefficient :=
  remainder8Coefficient0Block0

def remainder8 : Bivariate :=
  outerTerm 0 remainder8Coefficient0

def quotient6 : Bivariate :=
  linearPseudoQuotient
    remainder6 remainder7
    2 1

def exceptionalUnit6 : Coefficient :=
  C
    (((((((26813799997641 : ℚ) * 10 ^ 36 +
      142369575613846289747847827330896388) * 10 ^ 36 +
      174087143449204393900331622823388931) * 10 ^ 36 +
      504208118624079313576123579518587434) * 10 ^ 36 +
      856069465570511249870923189965244671) * 10 ^ 36 +
      650107475862081909428552923558342334) * 10 ^ 36 +
      248809782697354987477701994402490000)

def exceptional6 : Coefficient :=
  exceptionalUnit6 *
  (parameter - 1) ^ 1 *
  (discriminantFactor) ^ 6 *
  (cmTwelve) ^ 1

def recurrence6 : Prop :=
  C ((remainder7.coeff 1) ^ 2) *
      remainder6 =
    remainder7 * quotient6 +
      C ((remainder6.coeff 2) ^ 2 *
        exceptional6) * remainder8

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate


