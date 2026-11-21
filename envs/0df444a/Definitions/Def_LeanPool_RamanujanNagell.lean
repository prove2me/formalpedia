-- Prove2me | Definitions.Def_LeanPool_RamanujanNagell
-- name    : LeanPool_RamanujanNagell
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:45:22.628742+00:00
-- url     : https://prove2.me/theorems/8596c259-f0b1-4309-8ea6-2226ef9dd940
-- title:
--   Ramanujan Nagell
-- statement:
--   Definitions and structural lemmas for Ramanujan Nagell, from Barinder S. Banwait and Xinze Li; maintained by LeanPool contributors's pinned The Ramanujan-Nagell theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell.lean

module
public import Definitions.Def_LeanPool_RamanujanNagell_Basic
public import Definitions.Def_LeanPool_RamanujanNagell_Helpers
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
set_option autoImplicit true
@[expose] public section
@[expose] public section


