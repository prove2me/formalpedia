-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Main
-- name    : OddOrder_Isaacs_Ch01_Sylow_Main
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:47:44.522635+00:00
-- url     : https://prove2.me/theorems/c9556507-1978-4729-8104-5eb11a5fa97e
-- title:
--   Isaacs Ch. 1: Sylow theory (continuation file)
-- statement:
--   A continuation file of the Chapter 1 (Sylow theory) formalization following Isaacs, *Finite Group Theory*, split off from a longer module. Its docstring gives no further description, and the bundle contains no definitions or lemmas of its own.
--
--   The bundle consists of lemmas only.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch01_Sylow/Main.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch01_Sylow/Main.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Basic

namespace OddOrder.Isaacs.Ch01

open scoped IsMulCommutative

section

export Subgroup (chermakDelgadoMeasure chermakDelgadoLattice chermakDelgadoSubgroup
  chermakDelgadoMeasure_le_centralizer chermakDelgadoMeasure_mul_le
  chermakDelgadoLattice_inf_mem 
  
  chermakDelgadoLattice_centralizer_mem 
  chermakDelgadoSubgroup_mem_lattice
   
  )

end

end OddOrder.Isaacs.Ch01


