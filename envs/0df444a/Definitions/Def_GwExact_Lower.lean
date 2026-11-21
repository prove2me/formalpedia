-- Prove2me | Definitions.Def_GwExact_Lower
-- name    : GwExact_Lower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T20:18:02.079187+00:00
-- url     : https://prove2.me/theorems/107a9918-e99c-4cf7-8ef5-22e8a40f6fcc
-- title:
--   Lower
-- statement:
--   Definitions and structural lemmas for Lower, from arhancanli and contributors's pinned Exact Gallai–van der Waerden numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Lower.lean

module
public import Definitions.Def_GwExact_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GwExact
def goodB (r l n : ℕ) (c : ℕ → Fin r) : Bool :=
  ((List.range r).all fun k => (List.range (n + 1)).any fun x =>
    decide (1 ≤ x) && decide (x ≤ n) && decide ((c x : ℕ) = k)) &&
  ((List.range (n + 1)).all fun x => (List.range (n + 1)).all fun d =>
    !(decide (1 ≤ x) && decide (1 ≤ d) && decide (x + 2 * d ≤ n)) ||
    !(decide ((c x : ℕ) ≠ c (x + d)) && decide ((c x : ℕ) ≠ c (x + 2 * d)) &&
      decide ((c (x + d) : ℕ) ≠ c (x + 2 * d)))) &&
  ((List.range (n + 1)).all fun x => (List.range (n + 1)).all fun d =>
    !(decide (1 ≤ x) && decide (1 ≤ d) && decide (x + (l - 1) * d ≤ n)) ||
    (List.range l).any fun j => decide ((c (x + j * d) : ℕ) ≠ c x))
def digitCol (r : ℕ) (hr : 0 < r) (B x : ℕ) : Fin r :=
  ⟨(B >>> (3 * (x - 1))) % 8 % r, Nat.mod_lt _ hr⟩
def col3 : ℕ → Fin 3 := digitCol 3 (by decide) 0x49144948928a41228929125148245125224a290
def col4 : ℕ → Fin 4 := digitCol 4 (by decide) 0x6da6926d24d365b4d24da49a6cb69a49b4934d8
def col5 : ℕ → Fin 5 := digitCol 5 (by decide) 0x84a2922524512c945244a48a25928a489491448
end GwExact


