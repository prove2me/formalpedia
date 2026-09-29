-- Prove2me | Definitions.Def_GeneralCK_E8_mixed_polynomial_interface
-- name    : GeneralCK_E8_mixed_polynomial_interface
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T00:08:34.503717+00:00
-- url     : https://prove2.me/theorems/544e90aa-ac40-44e0-b796-080b8722044a
-- title:
--   Exact real and interval E8 mixed coefficient polynomials
-- statement:
--   The real mixed polynomial combines the six components of a jet at $t,2s+t,s+t,s$ for each source index pair $(i,j)$. Its interval counterpart evaluates the same exact integer polynomial using outward dyadic interval arithmetic. Both preserve the source's zero default for other index pairs. A separate soundness theorem proves containment whenever the four interval jets enclose those real jet components; derivative identities are established separately.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/tree/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core

open GeneralCK GeneralCK.Certificates Set GeneralCK.Certificates.DyadicInterval

section
namespace GeneralCK.Certificates.E8TAxisMixedCoefficients

open DyadicInterval
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- Candidate raw `s^i t^j` derivative coefficient, through total order five. -/
noncomputable def mixed (q : Jet5) (s t : ℝ) : ℕ → ℕ → ℝ
  | 0, 1 =>
      -(2 * q.d0 t * q.d1 (2 * s + t)) +
      (q.d0 t * q.d1 (s + t)) +
      -(2 * q.d1 t * q.d0 (2 * s + t)) +
      (q.d1 t * q.d0 (s + t)) +
      (q.d1 t * q.d0 s) +
      (q.d0 (2 * s + t) * q.d1 (s + t)) +
      (q.d1 (2 * s + t) * q.d0 (s + t)) +
      -(q.d1 (2 * s + t) * q.d0 s)
  | 0, 2 =>
      -(2 * q.d0 t * q.d2 (2 * s + t)) +
      (q.d0 t * q.d2 (s + t)) +
      -(4 * q.d1 t * q.d1 (2 * s + t)) +
      (2 * q.d1 t * q.d1 (s + t)) +
      -(2 * q.d2 t * q.d0 (2 * s + t)) +
      (q.d2 t * q.d0 (s + t)) +
      (q.d2 t * q.d0 s) +
      (q.d0 (2 * s + t) * q.d2 (s + t)) +
      (2 * q.d1 (2 * s + t) * q.d1 (s + t)) +
      (q.d2 (2 * s + t) * q.d0 (s + t)) +
      -(q.d2 (2 * s + t) * q.d0 s)
  | 1, 1 =>
      -(4 * q.d0 t * q.d2 (2 * s + t)) +
      (q.d0 t * q.d2 (s + t)) +
      -(4 * q.d1 t * q.d1 (2 * s + t)) +
      (q.d1 t * q.d1 (s + t)) +
      (q.d1 t * q.d1 s) +
      (q.d0 (2 * s + t) * q.d2 (s + t)) +
      (3 * q.d1 (2 * s + t) * q.d1 (s + t)) +
      -(q.d1 (2 * s + t) * q.d1 s) +
      (2 * q.d2 (2 * s + t) * q.d0 (s + t)) +
      -(2 * q.d2 (2 * s + t) * q.d0 s)
  | 0, 3 =>
      -(2 * q.d0 t * q.d3 (2 * s + t)) +
      (q.d0 t * q.d3 (s + t)) +
      -(6 * q.d1 t * q.d2 (2 * s + t)) +
      (3 * q.d1 t * q.d2 (s + t)) +
      -(6 * q.d2 t * q.d1 (2 * s + t)) +
      (3 * q.d2 t * q.d1 (s + t)) +
      -(2 * q.d3 t * q.d0 (2 * s + t)) +
      (q.d3 t * q.d0 (s + t)) +
      (q.d3 t * q.d0 s) +
      (q.d0 (2 * s + t) * q.d3 (s + t)) +
      (3 * q.d1 (2 * s + t) * q.d2 (s + t)) +
      (3 * q.d2 (2 * s + t) * q.d1 (s + t)) +
      (q.d3 (2 * s + t) * q.d0 (s + t)) +
      -(q.d3 (2 * s + t) * q.d0 s)
  | 1, 2 =>
      -(4 * q.d0 t * q.d3 (2 * s + t)) +
      (q.d0 t * q.d3 (s + t)) +
      -(8 * q.d1 t * q.d2 (2 * s + t)) +
      (2 * q.d1 t * q.d2 (s + t)) +
      -(4 * q.d2 t * q.d1 (2 * s + t)) +
      (q.d2 t * q.d1 (s + t)) +
      (q.d2 t * q.d1 s) +
      (q.d0 (2 * s + t) * q.d3 (s + t)) +
      (4 * q.d1 (2 * s + t) * q.d2 (s + t)) +
      (5 * q.d2 (2 * s + t) * q.d1 (s + t)) +
      -(q.d2 (2 * s + t) * q.d1 s) +
      (2 * q.d3 (2 * s + t) * q.d0 (s + t)) +
      -(2 * q.d3 (2 * s + t) * q.d0 s)
  | 2, 1 =>
      -(8 * q.d0 t * q.d3 (2 * s + t)) +
      (q.d0 t * q.d3 (s + t)) +
      -(8 * q.d1 t * q.d2 (2 * s + t)) +
      (q.d1 t * q.d2 (s + t)) +
      (q.d1 t * q.d2 s) +
      (q.d0 (2 * s + t) * q.d3 (s + t)) +
      (5 * q.d1 (2 * s + t) * q.d2 (s + t)) +
      -(q.d1 (2 * s + t) * q.d2 s) +
      (8 * q.d2 (2 * s + t) * q.d1 (s + t)) +
      -(4 * q.d2 (2 * s + t) * q.d1 s) +
      (4 * q.d3 (2 * s + t) * q.d0 (s + t)) +
      -(4 * q.d3 (2 * s + t) * q.d0 s)
  | 0, 4 =>
      -(2 * q.d0 t * q.d4 (2 * s + t)) +
      (q.d0 t * q.d4 (s + t)) +
      -(8 * q.d1 t * q.d3 (2 * s + t)) +
      (4 * q.d1 t * q.d3 (s + t)) +
      -(12 * q.d2 t * q.d2 (2 * s + t)) +
      (6 * q.d2 t * q.d2 (s + t)) +
      -(8 * q.d3 t * q.d1 (2 * s + t)) +
      (4 * q.d3 t * q.d1 (s + t)) +
      -(2 * q.d4 t * q.d0 (2 * s + t)) +
      (q.d4 t * q.d0 (s + t)) +
      (q.d4 t * q.d0 s) +
      (q.d0 (2 * s + t) * q.d4 (s + t)) +
      (4 * q.d1 (2 * s + t) * q.d3 (s + t)) +
      (6 * q.d2 (2 * s + t) * q.d2 (s + t)) +
      (4 * q.d3 (2 * s + t) * q.d1 (s + t)) +
      (q.d4 (2 * s + t) * q.d0 (s + t)) +
      -(q.d4 (2 * s + t) * q.d0 s)
  | 1, 3 =>
      -(4 * q.d0 t * q.d4 (2 * s + t)) +
      (q.d0 t * q.d4 (s + t)) +
      -(12 * q.d1 t * q.d3 (2 * s + t)) +
      (3 * q.d1 t * q.d3 (s + t)) +
      -(12 * q.d2 t * q.d2 (2 * s + t)) +
      (3 * q.d2 t * q.d2 (s + t)) +
      -(4 * q.d3 t * q.d1 (2 * s + t)) +
      (q.d3 t * q.d1 (s + t)) +
      (q.d3 t * q.d1 s) +
      (q.d0 (2 * s + t) * q.d4 (s + t)) +
      (5 * q.d1 (2 * s + t) * q.d3 (s + t)) +
      (9 * q.d2 (2 * s + t) * q.d2 (s + t)) +
      (7 * q.d3 (2 * s + t) * q.d1 (s + t)) +
      -(q.d3 (2 * s + t) * q.d1 s) +
      (2 * q.d4 (2 * s + t) * q.d0 (s + t)) +
      -(2 * q.d4 (2 * s + t) * q.d0 s)
  | 2, 2 =>
      -(8 * q.d0 t * q.d4 (2 * s + t)) +
      (q.d0 t * q.d4 (s + t)) +
      -(16 * q.d1 t * q.d3 (2 * s + t)) +
      (2 * q.d1 t * q.d3 (s + t)) +
      -(8 * q.d2 t * q.d2 (2 * s + t)) +
      (q.d2 t * q.d2 (s + t)) +
      (q.d2 t * q.d2 s) +
      (q.d0 (2 * s + t) * q.d4 (s + t)) +
      (6 * q.d1 (2 * s + t) * q.d3 (s + t)) +
      (13 * q.d2 (2 * s + t) * q.d2 (s + t)) +
      -(q.d2 (2 * s + t) * q.d2 s) +
      (12 * q.d3 (2 * s + t) * q.d1 (s + t)) +
      -(4 * q.d3 (2 * s + t) * q.d1 s) +
      (4 * q.d4 (2 * s + t) * q.d0 (s + t)) +
      -(4 * q.d4 (2 * s + t) * q.d0 s)
  | 3, 1 =>
      -(16 * q.d0 t * q.d4 (2 * s + t)) +
      (q.d0 t * q.d4 (s + t)) +
      -(16 * q.d1 t * q.d3 (2 * s + t)) +
      (q.d1 t * q.d3 (s + t)) +
      (q.d1 t * q.d3 s) +
      (q.d0 (2 * s + t) * q.d4 (s + t)) +
      (7 * q.d1 (2 * s + t) * q.d3 (s + t)) +
      -(q.d1 (2 * s + t) * q.d3 s) +
      (18 * q.d2 (2 * s + t) * q.d2 (s + t)) +
      -(6 * q.d2 (2 * s + t) * q.d2 s) +
      (20 * q.d3 (2 * s + t) * q.d1 (s + t)) +
      -(12 * q.d3 (2 * s + t) * q.d1 s) +
      (8 * q.d4 (2 * s + t) * q.d0 (s + t)) +
      -(8 * q.d4 (2 * s + t) * q.d0 s)
  | 0, 5 =>
      -(2 * q.d0 t * q.d5 (2 * s + t)) +
      (q.d0 t * q.d5 (s + t)) +
      -(10 * q.d1 t * q.d4 (2 * s + t)) +
      (5 * q.d1 t * q.d4 (s + t)) +
      -(20 * q.d2 t * q.d3 (2 * s + t)) +
      (10 * q.d2 t * q.d3 (s + t)) +
      -(20 * q.d3 t * q.d2 (2 * s + t)) +
      (10 * q.d3 t * q.d2 (s + t)) +
      -(10 * q.d4 t * q.d1 (2 * s + t)) +
      (5 * q.d4 t * q.d1 (s + t)) +
      -(2 * q.d5 t * q.d0 (2 * s + t)) +
      (q.d5 t * q.d0 (s + t)) +
      (q.d5 t * q.d0 s) +
      (q.d0 (2 * s + t) * q.d5 (s + t)) +
      (5 * q.d1 (2 * s + t) * q.d4 (s + t)) +
      (10 * q.d2 (2 * s + t) * q.d3 (s + t)) +
      (10 * q.d3 (2 * s + t) * q.d2 (s + t)) +
      (5 * q.d4 (2 * s + t) * q.d1 (s + t)) +
      (q.d5 (2 * s + t) * q.d0 (s + t)) +
      -(q.d5 (2 * s + t) * q.d0 s)
  | 1, 4 =>
      -(4 * q.d0 t * q.d5 (2 * s + t)) +
      (q.d0 t * q.d5 (s + t)) +
      -(16 * q.d1 t * q.d4 (2 * s + t)) +
      (4 * q.d1 t * q.d4 (s + t)) +
      -(24 * q.d2 t * q.d3 (2 * s + t)) +
      (6 * q.d2 t * q.d3 (s + t)) +
      -(16 * q.d3 t * q.d2 (2 * s + t)) +
      (4 * q.d3 t * q.d2 (s + t)) +
      -(4 * q.d4 t * q.d1 (2 * s + t)) +
      (q.d4 t * q.d1 (s + t)) +
      (q.d4 t * q.d1 s) +
      (q.d0 (2 * s + t) * q.d5 (s + t)) +
      (6 * q.d1 (2 * s + t) * q.d4 (s + t)) +
      (14 * q.d2 (2 * s + t) * q.d3 (s + t)) +
      (16 * q.d3 (2 * s + t) * q.d2 (s + t)) +
      (9 * q.d4 (2 * s + t) * q.d1 (s + t)) +
      -(q.d4 (2 * s + t) * q.d1 s) +
      (2 * q.d5 (2 * s + t) * q.d0 (s + t)) +
      -(2 * q.d5 (2 * s + t) * q.d0 s)
  | 2, 3 =>
      -(8 * q.d0 t * q.d5 (2 * s + t)) +
      (q.d0 t * q.d5 (s + t)) +
      -(24 * q.d1 t * q.d4 (2 * s + t)) +
      (3 * q.d1 t * q.d4 (s + t)) +
      -(24 * q.d2 t * q.d3 (2 * s + t)) +
      (3 * q.d2 t * q.d3 (s + t)) +
      -(8 * q.d3 t * q.d2 (2 * s + t)) +
      (q.d3 t * q.d2 (s + t)) +
      (q.d3 t * q.d2 s) +
      (q.d0 (2 * s + t) * q.d5 (s + t)) +
      (7 * q.d1 (2 * s + t) * q.d4 (s + t)) +
      (19 * q.d2 (2 * s + t) * q.d3 (s + t)) +
      (25 * q.d3 (2 * s + t) * q.d2 (s + t)) +
      -(q.d3 (2 * s + t) * q.d2 s) +
      (16 * q.d4 (2 * s + t) * q.d1 (s + t)) +
      -(4 * q.d4 (2 * s + t) * q.d1 s) +
      (4 * q.d5 (2 * s + t) * q.d0 (s + t)) +
      -(4 * q.d5 (2 * s + t) * q.d0 s)
  | 3, 2 =>
      -(16 * q.d0 t * q.d5 (2 * s + t)) +
      (q.d0 t * q.d5 (s + t)) +
      -(32 * q.d1 t * q.d4 (2 * s + t)) +
      (2 * q.d1 t * q.d4 (s + t)) +
      -(16 * q.d2 t * q.d3 (2 * s + t)) +
      (q.d2 t * q.d3 (s + t)) +
      (q.d2 t * q.d3 s) +
      (q.d0 (2 * s + t) * q.d5 (s + t)) +
      (8 * q.d1 (2 * s + t) * q.d4 (s + t)) +
      (25 * q.d2 (2 * s + t) * q.d3 (s + t)) +
      -(q.d2 (2 * s + t) * q.d3 s) +
      (38 * q.d3 (2 * s + t) * q.d2 (s + t)) +
      -(6 * q.d3 (2 * s + t) * q.d2 s) +
      (28 * q.d4 (2 * s + t) * q.d1 (s + t)) +
      -(12 * q.d4 (2 * s + t) * q.d1 s) +
      (8 * q.d5 (2 * s + t) * q.d0 (s + t)) +
      -(8 * q.d5 (2 * s + t) * q.d0 s)
  | 4, 1 =>
      -(32 * q.d0 t * q.d5 (2 * s + t)) +
      (q.d0 t * q.d5 (s + t)) +
      -(32 * q.d1 t * q.d4 (2 * s + t)) +
      (q.d1 t * q.d4 (s + t)) +
      (q.d1 t * q.d4 s) +
      (q.d0 (2 * s + t) * q.d5 (s + t)) +
      (9 * q.d1 (2 * s + t) * q.d4 (s + t)) +
      -(q.d1 (2 * s + t) * q.d4 s) +
      (32 * q.d2 (2 * s + t) * q.d3 (s + t)) +
      -(8 * q.d2 (2 * s + t) * q.d3 s) +
      (56 * q.d3 (2 * s + t) * q.d2 (s + t)) +
      -(24 * q.d3 (2 * s + t) * q.d2 s) +
      (48 * q.d4 (2 * s + t) * q.d1 (s + t)) +
      -(32 * q.d4 (2 * s + t) * q.d1 s) +
      (16 * q.d5 (2 * s + t) * q.d0 (s + t)) +
      -(16 * q.d5 (2 * s + t) * q.d0 s)
  | _, _ => 0

/-- Identical arithmetic graph evaluated with dyadic interval operations. -/
def mixedBox {p : ℕ} (a b c d : DyadicJet5Enclosure p) :
    ℕ → ℕ → DyadicInterval p
  | 0, 1 =>
      let v0 := (((ofInt p 2).mul a.d0).mul b.d1).neg
      let v1 := a.d0.mul c.d1
      let v2 := (((ofInt p 2).mul a.d1).mul b.d0).neg
      let v3 := a.d1.mul c.d0
      let v4 := a.d1.mul d.d0
      let v5 := b.d0.mul c.d1
      let v6 := b.d1.mul c.d0
      let v7 := (b.d1.mul d.d0).neg
      (((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7)
  | 0, 2 =>
      let v0 := (((ofInt p 2).mul a.d0).mul b.d2).neg
      let v1 := a.d0.mul c.d2
      let v2 := (((ofInt p 4).mul a.d1).mul b.d1).neg
      let v3 := ((ofInt p 2).mul a.d1).mul c.d1
      let v4 := (((ofInt p 2).mul a.d2).mul b.d0).neg
      let v5 := a.d2.mul c.d0
      let v6 := a.d2.mul d.d0
      let v7 := b.d0.mul c.d2
      let v8 := ((ofInt p 2).mul b.d1).mul c.d1
      let v9 := b.d2.mul c.d0
      let v10 := (b.d2.mul d.d0).neg
      ((((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9).add v10)
  | 1, 1 =>
      let v0 := (((ofInt p 4).mul a.d0).mul b.d2).neg
      let v1 := a.d0.mul c.d2
      let v2 := (((ofInt p 4).mul a.d1).mul b.d1).neg
      let v3 := a.d1.mul c.d1
      let v4 := a.d1.mul d.d1
      let v5 := b.d0.mul c.d2
      let v6 := ((ofInt p 3).mul b.d1).mul c.d1
      let v7 := (b.d1.mul d.d1).neg
      let v8 := ((ofInt p 2).mul b.d2).mul c.d0
      let v9 := (((ofInt p 2).mul b.d2).mul d.d0).neg
      (((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9)
  | 0, 3 =>
      let v0 := (((ofInt p 2).mul a.d0).mul b.d3).neg
      let v1 := a.d0.mul c.d3
      let v2 := (((ofInt p 6).mul a.d1).mul b.d2).neg
      let v3 := ((ofInt p 3).mul a.d1).mul c.d2
      let v4 := (((ofInt p 6).mul a.d2).mul b.d1).neg
      let v5 := ((ofInt p 3).mul a.d2).mul c.d1
      let v6 := (((ofInt p 2).mul a.d3).mul b.d0).neg
      let v7 := a.d3.mul c.d0
      let v8 := a.d3.mul d.d0
      let v9 := b.d0.mul c.d3
      let v10 := ((ofInt p 3).mul b.d1).mul c.d2
      let v11 := ((ofInt p 3).mul b.d2).mul c.d1
      let v12 := b.d3.mul c.d0
      let v13 := (b.d3.mul d.d0).neg
      (((((((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9).add v10).add v11).add v12).add v13)
  | 1, 2 =>
      let v0 := (((ofInt p 4).mul a.d0).mul b.d3).neg
      let v1 := a.d0.mul c.d3
      let v2 := (((ofInt p 8).mul a.d1).mul b.d2).neg
      let v3 := ((ofInt p 2).mul a.d1).mul c.d2
      let v4 := (((ofInt p 4).mul a.d2).mul b.d1).neg
      let v5 := a.d2.mul c.d1
      let v6 := a.d2.mul d.d1
      let v7 := b.d0.mul c.d3
      let v8 := ((ofInt p 4).mul b.d1).mul c.d2
      let v9 := ((ofInt p 5).mul b.d2).mul c.d1
      let v10 := (b.d2.mul d.d1).neg
      let v11 := ((ofInt p 2).mul b.d3).mul c.d0
      let v12 := (((ofInt p 2).mul b.d3).mul d.d0).neg
      ((((((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9).add v10).add v11).add v12)
  | 2, 1 =>
      let v0 := (((ofInt p 8).mul a.d0).mul b.d3).neg
      let v1 := a.d0.mul c.d3
      let v2 := (((ofInt p 8).mul a.d1).mul b.d2).neg
      let v3 := a.d1.mul c.d2
      let v4 := a.d1.mul d.d2
      let v5 := b.d0.mul c.d3
      let v6 := ((ofInt p 5).mul b.d1).mul c.d2
      let v7 := (b.d1.mul d.d2).neg
      let v8 := ((ofInt p 8).mul b.d2).mul c.d1
      let v9 := (((ofInt p 4).mul b.d2).mul d.d1).neg
      let v10 := ((ofInt p 4).mul b.d3).mul c.d0
      let v11 := (((ofInt p 4).mul b.d3).mul d.d0).neg
      (((((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9).add v10).add v11)
  | 0, 4 =>
      let v0 := (((ofInt p 2).mul a.d0).mul b.d4).neg
      let v1 := a.d0.mul c.d4
      let v2 := (((ofInt p 8).mul a.d1).mul b.d3).neg
      let v3 := ((ofInt p 4).mul a.d1).mul c.d3
      let v4 := (((ofInt p 12).mul a.d2).mul b.d2).neg
      let v5 := ((ofInt p 6).mul a.d2).mul c.d2
      let v6 := (((ofInt p 8).mul a.d3).mul b.d1).neg
      let v7 := ((ofInt p 4).mul a.d3).mul c.d1
      let v8 := (((ofInt p 2).mul a.d4).mul b.d0).neg
      let v9 := a.d4.mul c.d0
      let v10 := a.d4.mul d.d0
      let v11 := b.d0.mul c.d4
      let v12 := ((ofInt p 4).mul b.d1).mul c.d3
      let v13 := ((ofInt p 6).mul b.d2).mul c.d2
      let v14 := ((ofInt p 4).mul b.d3).mul c.d1
      let v15 := b.d4.mul c.d0
      let v16 := (b.d4.mul d.d0).neg
      ((((((((((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9).add v10).add v11).add v12).add v13).add v14).add v15).add v16)
  | 1, 3 =>
      let v0 := (((ofInt p 4).mul a.d0).mul b.d4).neg
      let v1 := a.d0.mul c.d4
      let v2 := (((ofInt p 12).mul a.d1).mul b.d3).neg
      let v3 := ((ofInt p 3).mul a.d1).mul c.d3
      let v4 := (((ofInt p 12).mul a.d2).mul b.d2).neg
      let v5 := ((ofInt p 3).mul a.d2).mul c.d2
      let v6 := (((ofInt p 4).mul a.d3).mul b.d1).neg
      let v7 := a.d3.mul c.d1
      let v8 := a.d3.mul d.d1
      let v9 := b.d0.mul c.d4
      let v10 := ((ofInt p 5).mul b.d1).mul c.d3
      let v11 := ((ofInt p 9).mul b.d2).mul c.d2
      let v12 := ((ofInt p 7).mul b.d3).mul c.d1
      let v13 := (b.d3.mul d.d1).neg
      let v14 := ((ofInt p 2).mul b.d4).mul c.d0
      let v15 := (((ofInt p 2).mul b.d4).mul d.d0).neg
      (((((((((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9).add v10).add v11).add v12).add v13).add v14).add v15)
  | 2, 2 =>
      let v0 := (((ofInt p 8).mul a.d0).mul b.d4).neg
      let v1 := a.d0.mul c.d4
      let v2 := (((ofInt p 16).mul a.d1).mul b.d3).neg
      let v3 := ((ofInt p 2).mul a.d1).mul c.d3
      let v4 := (((ofInt p 8).mul a.d2).mul b.d2).neg
      let v5 := a.d2.mul c.d2
      let v6 := a.d2.mul d.d2
      let v7 := b.d0.mul c.d4
      let v8 := ((ofInt p 6).mul b.d1).mul c.d3
      let v9 := ((ofInt p 13).mul b.d2).mul c.d2
      let v10 := (b.d2.mul d.d2).neg
      let v11 := ((ofInt p 12).mul b.d3).mul c.d1
      let v12 := (((ofInt p 4).mul b.d3).mul d.d1).neg
      let v13 := ((ofInt p 4).mul b.d4).mul c.d0
      let v14 := (((ofInt p 4).mul b.d4).mul d.d0).neg
      ((((((((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9).add v10).add v11).add v12).add v13).add v14)
  | 3, 1 =>
      let v0 := (((ofInt p 16).mul a.d0).mul b.d4).neg
      let v1 := a.d0.mul c.d4
      let v2 := (((ofInt p 16).mul a.d1).mul b.d3).neg
      let v3 := a.d1.mul c.d3
      let v4 := a.d1.mul d.d3
      let v5 := b.d0.mul c.d4
      let v6 := ((ofInt p 7).mul b.d1).mul c.d3
      let v7 := (b.d1.mul d.d3).neg
      let v8 := ((ofInt p 18).mul b.d2).mul c.d2
      let v9 := (((ofInt p 6).mul b.d2).mul d.d2).neg
      let v10 := ((ofInt p 20).mul b.d3).mul c.d1
      let v11 := (((ofInt p 12).mul b.d3).mul d.d1).neg
      let v12 := ((ofInt p 8).mul b.d4).mul c.d0
      let v13 := (((ofInt p 8).mul b.d4).mul d.d0).neg
      (((((((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9).add v10).add v11).add v12).add v13)
  | 0, 5 =>
      let v0 := (((ofInt p 2).mul a.d0).mul b.d5).neg
      let v1 := a.d0.mul c.d5
      let v2 := (((ofInt p 10).mul a.d1).mul b.d4).neg
      let v3 := ((ofInt p 5).mul a.d1).mul c.d4
      let v4 := (((ofInt p 20).mul a.d2).mul b.d3).neg
      let v5 := ((ofInt p 10).mul a.d2).mul c.d3
      let v6 := (((ofInt p 20).mul a.d3).mul b.d2).neg
      let v7 := ((ofInt p 10).mul a.d3).mul c.d2
      let v8 := (((ofInt p 10).mul a.d4).mul b.d1).neg
      let v9 := ((ofInt p 5).mul a.d4).mul c.d1
      let v10 := (((ofInt p 2).mul a.d5).mul b.d0).neg
      let v11 := a.d5.mul c.d0
      let v12 := a.d5.mul d.d0
      let v13 := b.d0.mul c.d5
      let v14 := ((ofInt p 5).mul b.d1).mul c.d4
      let v15 := ((ofInt p 10).mul b.d2).mul c.d3
      let v16 := ((ofInt p 10).mul b.d3).mul c.d2
      let v17 := ((ofInt p 5).mul b.d4).mul c.d1
      let v18 := b.d5.mul c.d0
      let v19 := (b.d5.mul d.d0).neg
      (((((((((((((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9).add v10).add v11).add v12).add v13).add v14).add v15).add v16).add v17).add v18).add v19)
  | 1, 4 =>
      let v0 := (((ofInt p 4).mul a.d0).mul b.d5).neg
      let v1 := a.d0.mul c.d5
      let v2 := (((ofInt p 16).mul a.d1).mul b.d4).neg
      let v3 := ((ofInt p 4).mul a.d1).mul c.d4
      let v4 := (((ofInt p 24).mul a.d2).mul b.d3).neg
      let v5 := ((ofInt p 6).mul a.d2).mul c.d3
      let v6 := (((ofInt p 16).mul a.d3).mul b.d2).neg
      let v7 := ((ofInt p 4).mul a.d3).mul c.d2
      let v8 := (((ofInt p 4).mul a.d4).mul b.d1).neg
      let v9 := a.d4.mul c.d1
      let v10 := a.d4.mul d.d1
      let v11 := b.d0.mul c.d5
      let v12 := ((ofInt p 6).mul b.d1).mul c.d4
      let v13 := ((ofInt p 14).mul b.d2).mul c.d3
      let v14 := ((ofInt p 16).mul b.d3).mul c.d2
      let v15 := ((ofInt p 9).mul b.d4).mul c.d1
      let v16 := (b.d4.mul d.d1).neg
      let v17 := ((ofInt p 2).mul b.d5).mul c.d0
      let v18 := (((ofInt p 2).mul b.d5).mul d.d0).neg
      ((((((((((((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9).add v10).add v11).add v12).add v13).add v14).add v15).add v16).add v17).add v18)
  | 2, 3 =>
      let v0 := (((ofInt p 8).mul a.d0).mul b.d5).neg
      let v1 := a.d0.mul c.d5
      let v2 := (((ofInt p 24).mul a.d1).mul b.d4).neg
      let v3 := ((ofInt p 3).mul a.d1).mul c.d4
      let v4 := (((ofInt p 24).mul a.d2).mul b.d3).neg
      let v5 := ((ofInt p 3).mul a.d2).mul c.d3
      let v6 := (((ofInt p 8).mul a.d3).mul b.d2).neg
      let v7 := a.d3.mul c.d2
      let v8 := a.d3.mul d.d2
      let v9 := b.d0.mul c.d5
      let v10 := ((ofInt p 7).mul b.d1).mul c.d4
      let v11 := ((ofInt p 19).mul b.d2).mul c.d3
      let v12 := ((ofInt p 25).mul b.d3).mul c.d2
      let v13 := (b.d3.mul d.d2).neg
      let v14 := ((ofInt p 16).mul b.d4).mul c.d1
      let v15 := (((ofInt p 4).mul b.d4).mul d.d1).neg
      let v16 := ((ofInt p 4).mul b.d5).mul c.d0
      let v17 := (((ofInt p 4).mul b.d5).mul d.d0).neg
      (((((((((((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9).add v10).add v11).add v12).add v13).add v14).add v15).add v16).add v17)
  | 3, 2 =>
      let v0 := (((ofInt p 16).mul a.d0).mul b.d5).neg
      let v1 := a.d0.mul c.d5
      let v2 := (((ofInt p 32).mul a.d1).mul b.d4).neg
      let v3 := ((ofInt p 2).mul a.d1).mul c.d4
      let v4 := (((ofInt p 16).mul a.d2).mul b.d3).neg
      let v5 := a.d2.mul c.d3
      let v6 := a.d2.mul d.d3
      let v7 := b.d0.mul c.d5
      let v8 := ((ofInt p 8).mul b.d1).mul c.d4
      let v9 := ((ofInt p 25).mul b.d2).mul c.d3
      let v10 := (b.d2.mul d.d3).neg
      let v11 := ((ofInt p 38).mul b.d3).mul c.d2
      let v12 := (((ofInt p 6).mul b.d3).mul d.d2).neg
      let v13 := ((ofInt p 28).mul b.d4).mul c.d1
      let v14 := (((ofInt p 12).mul b.d4).mul d.d1).neg
      let v15 := ((ofInt p 8).mul b.d5).mul c.d0
      let v16 := (((ofInt p 8).mul b.d5).mul d.d0).neg
      ((((((((((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9).add v10).add v11).add v12).add v13).add v14).add v15).add v16)
  | 4, 1 =>
      let v0 := (((ofInt p 32).mul a.d0).mul b.d5).neg
      let v1 := a.d0.mul c.d5
      let v2 := (((ofInt p 32).mul a.d1).mul b.d4).neg
      let v3 := a.d1.mul c.d4
      let v4 := a.d1.mul d.d4
      let v5 := b.d0.mul c.d5
      let v6 := ((ofInt p 9).mul b.d1).mul c.d4
      let v7 := (b.d1.mul d.d4).neg
      let v8 := ((ofInt p 32).mul b.d2).mul c.d3
      let v9 := (((ofInt p 8).mul b.d2).mul d.d3).neg
      let v10 := ((ofInt p 56).mul b.d3).mul c.d2
      let v11 := (((ofInt p 24).mul b.d3).mul d.d2).neg
      let v12 := ((ofInt p 48).mul b.d4).mul c.d1
      let v13 := (((ofInt p 32).mul b.d4).mul d.d1).neg
      let v14 := ((ofInt p 16).mul b.d5).mul c.d0
      let v15 := (((ofInt p 16).mul b.d5).mul d.d0).neg
      (((((((((((((((v0.add v1).add v2).add v3).add v4).add v5).add v6).add v7).add v8).add v9).add v10).add v11).add v12).add v13).add v14).add v15)
  | _, _ => ofInt p 0





end GeneralCK.Certificates.E8TAxisMixedCoefficients
end


