-- Prove2me | Definitions.Def_Autoconvolutions_Coefficients
-- name    : Autoconvolutions_Coefficients
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:48:52.265501+00:00
-- url     : https://prove2.me/theorems/4a8e2205-7266-40c3-a523-04df53558364
-- title:
--   Coefficients
-- statement:
--   Definitions and structural lemmas for Coefficients, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Coefficients.lean

module
public import Definitions.Def_Autoconvolutions_BlockExpansion
public import Definitions.Def_Autoconvolutions_Occupancy
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_Flat
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Polynomial
open scoped BigOperators
namespace Autoconvolutions.Blocks
abbrev Ticket (m : ℕ) := Σ _ : ℕ, Row m
noncomputable def tickets {m : ℕ} (I J : Finset (Fin m)) (n K D : ℕ) :
    Finset (Ticket m) :=
  (range (2*K+1)).sigma fun s => rows I J (2*n-s) (2*n+s) D
noncomputable def weight {m : ℕ} (I J : Finset (Fin m)) (K : ℕ)
    (t : Ticket m) : ℝ :=
  (Nat.multinomial I t.2.1.1 : ℝ) * (Nat.multinomial J t.2.1.2 : ℝ) *
    (Flat.B K t.1).coeff t.2.2
end Autoconvolutions.Blocks


