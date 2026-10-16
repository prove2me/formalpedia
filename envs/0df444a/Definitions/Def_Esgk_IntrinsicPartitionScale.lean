-- Prove2me | Definitions.Def_Esgk_IntrinsicPartitionScale
-- name    : Esgk_IntrinsicPartitionScale
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:43:50.692978+00:00
-- url     : https://prove2.me/theorems/f613875d-705d-4bbf-9e04-0d4155e16c4c
-- title:
--   A natural-number block size for degree and scale
-- statement:
--   This defines the natural number $(N+dj-1)/(dj)$, with subtraction and division in the natural numbers. When $dj>0$, it is the ceiling of $N/(dj)$.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

 
def intrinsicPartitionBlockSize (d j N : ℕ) : ℕ :=
  (N + d * j - 1) / (d * j)


end Esgk


