-- Prove2me | Definitions.Def_MazurTransfer_ExactEqualityCertificate
-- name    : MazurTransfer_ExactEqualityCertificate
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T07:45:27.053798+00:00
-- url     : https://prove2.me/theorems/65320c4a-dcc0-4007-86fd-e10a1d7d4696
-- title:
--   Exact parametric equality statement certificate
-- statement:
--   For any sort and two elements a,b, ExactEqualityCertificate a b is a one-field Prop structure whose identity field is exactly a=b. It declares no constructed proof. Both directions of logical equivalence to the original equality were checked generically in Lean. Named downstream consumers are the original first-recurrence left5 identity and the normalized coefficient identities in the full order49 resultant certificate.
-- source:
--   New proof-free statement interface with an explicit boundary: a generic one-field Prop representation of exactly the supplied equality. The original equality and the certificate are logically equivalent, not definitionally equal. Generic forward and reverse conversion proofs have ordinary Lean kernel checks with standard axioms only. No mathematical hypothesis, coefficient or proof is added. Named downstream consumers: original recurrence1Left5_eq, normalized recurrence identities, bounded-resultant nonvanishing and full every-curve order49 exclusion. Apache-2.0 attribution retained.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
universe u

structure MazurTransfer.ExactEqualityCertificate {α : Sort u} (a b : α) : Prop where
  identity : a = b

#print axioms MazurTransfer.ExactEqualityCertificate
#print axioms MazurTransfer.ExactEqualityCertificate.mk
#print axioms MazurTransfer.ExactEqualityCertificate.identity


