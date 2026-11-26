-- Prove2me | Definitions.Def_FourierJacobi_Valuations_Cartan
-- name    : FourierJacobi_Valuations_Cartan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:46:54.906043+00:00
-- url     : https://prove2.me/theorems/02be86ed-3332-4342-b3bb-5cbac1604d29
-- title:
--   Cartan
-- statement:
--   Definitions and structural lemmas for Cartan, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/Cartan.lean

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
set_option autoImplicit false
namespace FourierJacobi
namespace Valuations
def baseMinimum (k j h : ℤ) : ℤ :=
  min (min (min (min (min 0 k) (-k)) (k + j)) h) (k + h)
def entryMinimum (r k j h : ℤ) : ℤ :=
  if r = 0 then baseMinimum k j h else min (baseMinimum k j h) (-r)
def determinantValuation (r j h c : ℤ) : ℤ :=
  if 2 * h = j - r then 2 * h + c else min (2 * h) (j - r)
def minorMinimum (r k j h c : ℤ) : ℤ :=
  if r = 0 then min (baseMinimum k j h) (k + 2 * h)
  else min (min (min (baseMinimum k j h) (k - r)) (-k - r))
    (k + determinantValuation r j h c)
def cartanIndices (r k j h c : ℤ) : ℤ × ℤ :=
  let u := entryMinimum r k j h
  let s := minorMinimum r k j h c
  (-2 * (s - u), s - 2 * u)
def tableZero (k j h : ℤ) : ℤ × ℤ :=
  if 0 ≤ k then
    if -2 * k ≤ j then
      if -k ≤ h then (0, k) else (-2 * k - 2 * h, k)
    else if h < k + j then (-2 * k - 2 * h, k)
    else if j ≤ 2 * h then (0, -k - j)
    else (2 * j - 4 * h, 2 * h - 2 * j - k)
  else
    if 0 ≤ j then
      if 0 ≤ h then (0, -k) else (-2 * h, -k)
    else if h < j then (-2 * h, -k)
    else if j ≤ 2 * h then (0, -k - j)
    else (2 * j - 4 * h, 2 * h - 2 * j - k)
def collisionRows (r k j h c : ℤ) : ℤ × ℤ :=
  if j - r + 1 ≤ 2 * h then (2 * r, -k - j - r)
  else if 2 * h = j - r then (2 * (r - min c r), -k - j - r + min c r)
  else (2 * j - 4 * h, 2 * h - 2 * j - k)
def tableOne (k j h c : ℤ) : ℤ × ℤ :=
  if 1 ≤ k then
    if -2 * k ≤ j then
      if h < -k then (-2 * k - 2 * h, k) else (2, k - 1)
    else if h < k + j then (-2 * k - 2 * h, k)
    else collisionRows 1 k j h c
  else
    if 0 ≤ j then
      if h < 0 then (-2 * h, -k)
      else if k = 0 then (0, 1) else (2, -k - 1)
    else if h < j then (-2 * h, -k)
    else collisionRows 1 k j h c
def tableTwo (k j h c : ℤ) : ℤ × ℤ :=
  if 1 ≤ k then
    if -2 * k ≤ j then
      if h < -k then (-2 * k - 2 * h, k)
      else if 2 ≤ k then (4, k - 2) else (2, 1)
    else if h < k + j then (-2 * k - 2 * h, k)
    else collisionRows 2 k j h c
  else
    if k = 0 ∧ -1 ≤ j then
      if h ≤ -2 then (-2 * h, 0)
      else if 0 ≤ j then (0, 2) else (2, 1)
    else if k ≤ -1 ∧ 0 ≤ j then
      if h ≤ -1 then (-2 * h, -k)
      else if k = -1 then (2, 1) else (4, -k - 2)
    else if k ≤ -1 ∧ j = -1 then
      if h ≤ -2 then
        if k = -1 then (-2 * h, 1) else (-2 * h, -k)
      else if k = -1 then (4, 0) else (4, -k - 1)
    else if h < j then (-2 * h, -k)
    else collisionRows 2 k j h c
end Valuations
end FourierJacobi


