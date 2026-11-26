-- Prove2me | Definitions.Def_FourierJacobi_Analysis_I2Partition
-- name    : FourierJacobi_Analysis_I2Partition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:07:09.453364+00:00
-- url     : https://prove2.me/theorems/ae9b0aba-e231-4f92-b391-dc28cf7048a5
-- title:
--   I2 Partition
-- statement:
--   Definitions and structural lemmas for I2 Partition, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Partition.lean

import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Mathlib.Data.Fintype.Fin
set_option autoImplicit false
namespace FourierJacobi.Analysis
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
def i2TailClassify (positive : Bool) (j h : ℤ) (c : ℕ) : Fin 25 :=
  if j - 1 ≤ 2 * h then (if positive then 3 else 19)
  else if 2 * h = j - 2 then
    if c = 0 then (if positive then 4 else 20)
    else if c = 1 then (if positive then 5 else 21)
    else (if positive then 6 else 22)
  else (if positive then 7 else 23)
def i2Classify (k j h : ℤ) (c : ℕ) : Fin 25 :=
  if 1 ≤ k then
    if -2 * k ≤ j then
      if h < -k then 2 else if 2 ≤ k then 0 else 1
    else if h < k + j then 8 else i2TailClassify true j h c
  else if k = 0 then
    if -1 ≤ j then
      if h ≤ -2 then 11 else if 0 ≤ j then 9 else 10
    else if h < j then 24 else i2TailClassify false j h c
  else if 0 ≤ j then
    if h ≤ -1 then 18 else if k = -1 then 12 else 15
  else if j = -1 then
    if h ≤ -2 then (if k = -1 then 14 else 17)
    else (if k = -1 then 13 else 16)
  else if h < j then 24 else i2TailClassify false j h c
end FourierJacobi.Analysis


