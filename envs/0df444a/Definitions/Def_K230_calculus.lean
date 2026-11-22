-- Prove2me | Definitions.Def_K230_calculus
-- name    : K230_calculus
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T21:13:27.23756+00:00
-- url     : https://prove2.me/theorems/4dd20411-f780-4fc0-9430-1186815218e8
-- title:
--   K230: numerical proof calculus
-- statement:
--   The inductive predicate `Thm230 n`: the code $n$ is derivable from the truth code $0$, the logical rows `rho1`–`rho8`, and gated source bundles, by modus ponens (`wim`) and generalization (`wal`). This is the code-level proof calculus `thm230` of `Thm230.v`.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/logic/Thm230.v

import Definitions.Def_K230_codes
namespace K230
inductive Thm230 : Nat → Prop where
  | T_true : Thm230 0
  | T_mp (t b : Nat) : Thm230 t → Thm230 (wim t b) → Thm230 b
  | T_gen (a h : Nat) : Thm230 h → Thm230 (wal a h)
  | T_r1 (a b : Nat) : Thm230 (rho1 a b)
  | T_r2 (a b c : Nat) : Thm230 (rho2 a b c)
  | T_r3 (a b c : Nat) : Thm230 (rho3 a b c)
  | T_r4 (a b c : Nat) : Thm230 (rho4 a b c)
  | T_r5 (a b c : Nat) : Thm230 (rho5 a b c)
  | T_r6 (a b : Nat) : Thm230 (rho6 a b)
  | T_r7 (a b c : Nat) : Thm230 (rho7 a b c)
  | T_r8 (a b c u : Nat) : Thm230 (rho8 a b c u)
  | T_bundle (a b c : Nat) : c ≠ a → c ≠ b → Thm230 (bundle230 a b c)
end K230


