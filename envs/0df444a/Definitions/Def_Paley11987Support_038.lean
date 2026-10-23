-- Prove2me | Definitions.Def_Paley11987Support_038
-- name    : Paley11987Support_038
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T02:52:15.869354+00:00
-- url     : https://prove2.me/theorems/549f971c-601f-4f99-a473-8fdce6ec0d4f
-- title:
--   Deletion costs
-- statement:
--   Defines the finite deletion-cost expression used when estimating marked and source candidate sets.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module BooleanTransferCrossCost.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module BooleanTransferCrossCost, SHA256 fc75a228b10b4a9c134ec9da88a39f1775aef09b7ed78dfc7f7b78f9812871a1

import Mathlib.Data.Nat.Basic

set_option autoImplicit false
set_option Elab.async false
section z59

set_option maxHeartbeats 5000000
namespace ZT

def deletionCost (K t ext intr budget B S J : ℕ) : ℕ :=
  let k := min K t
  let extra := min t (k+budget)-k
  max (k*B+ext*S+intr*J)
    ((k+extra)*B+(ext-extra)*S+(intr+extra)*J)







end ZT
end z59


