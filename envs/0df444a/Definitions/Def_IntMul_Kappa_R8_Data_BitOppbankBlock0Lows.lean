-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0Lows
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0Lows
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:38:51.713205+00:00
-- url     : https://prove2.me/theorems/134969a0-0be3-4dcc-b7be-e8bbe4154481
-- title:
--   Nodup of the 2602 block-0 gate lows
-- statement:
--   # Nodup of the block-0 gate lows
--
--   Glue pack: `lowsFlat.Nodup` for the 2602 block-0 gate lows (pivot and `bp-1` of each of 1301 gates), assembled from the published Data / A / B1–B3 / C1–C4 chunk-certificate packs via index-certificate `rfl`s, chunked strict-sortedness, and pigeonhole. Prefix / block-0 helper only; not a full-word W1F certificate.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: block-0 helper glue. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsA
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsB1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsB2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsB3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsC1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsC2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsC3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsC4

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open IntMul.Kappa.R8.Bit.Oppbank.Block0LowsData
open IntMul.Kappa.R8.Bit.Oppbank.Block0LowsA
open IntMul.Kappa.R8.Bit.Oppbank.Block0LowsB1
open IntMul.Kappa.R8.Bit.Oppbank.Block0LowsB2
open IntMul.Kappa.R8.Bit.Oppbank.Block0LowsB3
open IntMul.Kappa.R8.Bit.Oppbank.Block0LowsC1
open IntMul.Kappa.R8.Bit.Oppbank.Block0LowsC2
open IntMul.Kappa.R8.Bit.Oppbank.Block0LowsC3
open IntMul.Kappa.R8.Bit.Oppbank.Block0LowsC4

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0Lows

theorem lows_map_00 : sort_c00 = jx_c00.map (fun i => lowsFlat[i]!) := sort_c00_eq

theorem lows_map_01 : sort_c00 ++ sort_c01 =
    (jx_c00 ++ jx_c01).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_00, sort_c01_eq]

theorem lows_map_02 : sort_c00 ++ sort_c01 ++ sort_c02 =
    (jx_c00 ++ jx_c01 ++ jx_c02).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_01, sort_c02_eq]

theorem lows_map_03 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_02, sort_c03_eq]

theorem lows_map_04 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_03, sort_c04_eq]

theorem lows_map_05 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_04, sort_c05_eq]

theorem lows_map_06 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_05, sort_c06_eq]

theorem lows_map_07 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_06, sort_c07_eq]

theorem lows_map_08 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_07, sort_c08_eq]

theorem lows_map_09 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_08, sort_c09_eq]

theorem lows_map_10 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_09, sort_c10_eq]

theorem lows_map_11 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_10, sort_c11_eq]

theorem lows_map_12 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_11, sort_c12_eq]

theorem lows_map_13 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_12, sort_c13_eq]

theorem lows_map_14 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_13, sort_c14_eq]

theorem lows_map_15 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_14, sort_c15_eq]

theorem lows_map_16 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_15, sort_c16_eq]

theorem lows_map_17 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_16, sort_c17_eq]

theorem lows_map_18 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_17, sort_c18_eq]

theorem lows_map_19 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_18, sort_c19_eq]

theorem lows_map_20 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_19, sort_c20_eq]

theorem lows_map_21 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20 ++ jx_c21).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_20, sort_c21_eq]

theorem lows_map_22 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20 ++ jx_c21 ++ jx_c22).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_21, sort_c22_eq]

theorem lows_map_23 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20 ++ jx_c21 ++ jx_c22 ++ jx_c23).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_22, sort_c23_eq]

theorem lows_map_24 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20 ++ jx_c21 ++ jx_c22 ++ jx_c23 ++ jx_c24).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_23, sort_c24_eq]

theorem lows_map_25 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24 ++ sort_c25 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20 ++ jx_c21 ++ jx_c22 ++ jx_c23 ++ jx_c24 ++ jx_c25).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_24, sort_c25_eq]

theorem lows_map_26 : sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24 ++ sort_c25 ++ sort_c26 =
    (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20 ++ jx_c21 ++ jx_c22 ++ jx_c23 ++ jx_c24 ++ jx_c25 ++ jx_c26).map (fun i => lowsFlat[i]!) := by
  rw [List.map_append, lows_map_25, sort_c26_eq]

theorem lowsSorted_eq_ix : lowsSorted = lowsSortedIx_app.map (fun i => lowsFlat[i]!) := by
  rw [sort_split]
  exact lows_map_26

theorem all_append (p : Nat → Bool) (A B : List Nat) :
    (A ++ B).all p = (A.all p && B.all p) := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp [List.all_cons, ih, Bool.and_assoc]

theorem jx_all_00 : jx_c00.all (fun i => decide (i < 2602)) = true := jx_c00_all

theorem jx_all_01 : (jx_c00 ++ jx_c01).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_00, jx_c01_all]
  rfl

theorem jx_all_02 : (jx_c00 ++ jx_c01 ++ jx_c02).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_01, jx_c02_all]
  rfl

theorem jx_all_03 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_02, jx_c03_all]
  rfl

theorem jx_all_04 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_03, jx_c04_all]
  rfl

theorem jx_all_05 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_04, jx_c05_all]
  rfl

theorem jx_all_06 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_05, jx_c06_all]
  rfl

theorem jx_all_07 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_06, jx_c07_all]
  rfl

theorem jx_all_08 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_07, jx_c08_all]
  rfl

theorem jx_all_09 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_08, jx_c09_all]
  rfl

theorem jx_all_10 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_09, jx_c10_all]
  rfl

theorem jx_all_11 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_10, jx_c11_all]
  rfl

theorem jx_all_12 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_11, jx_c12_all]
  rfl

theorem jx_all_13 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_12, jx_c13_all]
  rfl

theorem jx_all_14 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_13, jx_c14_all]
  rfl

theorem jx_all_15 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_14, jx_c15_all]
  rfl

theorem jx_all_16 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_15, jx_c16_all]
  rfl

theorem jx_all_17 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_16, jx_c17_all]
  rfl

theorem jx_all_18 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_17, jx_c18_all]
  rfl

theorem jx_all_19 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_18, jx_c19_all]
  rfl

theorem jx_all_20 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_19, jx_c20_all]
  rfl

theorem jx_all_21 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20 ++ jx_c21).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_20, jx_c21_all]
  rfl

theorem jx_all_22 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20 ++ jx_c21 ++ jx_c22).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_21, jx_c22_all]
  rfl

theorem jx_all_23 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20 ++ jx_c21 ++ jx_c22 ++ jx_c23).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_22, jx_c23_all]
  rfl

theorem jx_all_24 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20 ++ jx_c21 ++ jx_c22 ++ jx_c23 ++ jx_c24).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_23, jx_c24_all]
  rfl

theorem jx_all_25 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20 ++ jx_c21 ++ jx_c22 ++ jx_c23 ++ jx_c24 ++ jx_c25).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_24, jx_c25_all]
  rfl

theorem jx_all_26 : (jx_c00 ++ jx_c01 ++ jx_c02 ++ jx_c03 ++ jx_c04 ++ jx_c05 ++ jx_c06 ++ jx_c07 ++ jx_c08 ++ jx_c09 ++ jx_c10 ++ jx_c11 ++ jx_c12 ++ jx_c13 ++ jx_c14 ++ jx_c15 ++ jx_c16 ++ jx_c17 ++ jx_c18 ++ jx_c19 ++ jx_c20 ++ jx_c21 ++ jx_c22 ++ jx_c23 ++ jx_c24 ++ jx_c25 ++ jx_c26).all (fun i => decide (i < 2602)) = true := by
  rw [all_append, jx_all_25, jx_c26_all]
  rfl

theorem jx_all : lowsSortedIx_app.all (fun i => decide (i < 2602)) = true :=
  jx_all_26

theorem jx_lt : ∀ i ∈ lowsSortedIx_app, i < lowsFlat.length := by
  intro i hi
  have h := all_lt_of_all_true jx_all i hi
  rw [lowsFlat_len]
  exact h

theorem lowsSorted_subset : ∀ x ∈ lowsSorted, x ∈ lowsFlat := by
  intro x hx
  rw [lowsSorted_eq_ix] at hx
  exact mem_of_map_getElem! jx_lt hx

theorem lows_sorted_00 : isStrictSorted sort_c00 = true := sort_c00_sorted

theorem lows_prefix_01_ne : sort_c00 ≠ [] := sort_c00_ne

theorem sort_gap_00 :
    sort_c00.getLast sort_c00_ne < sort_c01.head sort_c01_ne := by
  rw [sort_c00_last, sort_c01_hd]
  decide

theorem sort_gap_01 :
    sort_c01.getLast sort_c01_ne < sort_c02.head sort_c02_ne := by
  rw [sort_c01_last, sort_c02_hd]
  decide

theorem sort_gap_02 :
    sort_c02.getLast sort_c02_ne < sort_c03.head sort_c03_ne := by
  rw [sort_c02_last, sort_c03_hd]
  decide

theorem sort_gap_03 :
    sort_c03.getLast sort_c03_ne < sort_c04.head sort_c04_ne := by
  rw [sort_c03_last, sort_c04_hd]
  decide

theorem sort_gap_04 :
    sort_c04.getLast sort_c04_ne < sort_c05.head sort_c05_ne := by
  rw [sort_c04_last, sort_c05_hd]
  decide

theorem sort_gap_05 :
    sort_c05.getLast sort_c05_ne < sort_c06.head sort_c06_ne := by
  rw [sort_c05_last, sort_c06_hd]
  decide

theorem sort_gap_06 :
    sort_c06.getLast sort_c06_ne < sort_c07.head sort_c07_ne := by
  rw [sort_c06_last, sort_c07_hd]
  decide

theorem sort_gap_07 :
    sort_c07.getLast sort_c07_ne < sort_c08.head sort_c08_ne := by
  rw [sort_c07_last, sort_c08_hd]
  decide

theorem sort_gap_08 :
    sort_c08.getLast sort_c08_ne < sort_c09.head sort_c09_ne := by
  rw [sort_c08_last, sort_c09_hd]
  decide

theorem sort_gap_09 :
    sort_c09.getLast sort_c09_ne < sort_c10.head sort_c10_ne := by
  rw [sort_c09_last, sort_c10_hd]
  decide

theorem sort_gap_10 :
    sort_c10.getLast sort_c10_ne < sort_c11.head sort_c11_ne := by
  rw [sort_c10_last, sort_c11_hd]
  decide

theorem sort_gap_11 :
    sort_c11.getLast sort_c11_ne < sort_c12.head sort_c12_ne := by
  rw [sort_c11_last, sort_c12_hd]
  decide

theorem sort_gap_12 :
    sort_c12.getLast sort_c12_ne < sort_c13.head sort_c13_ne := by
  rw [sort_c12_last, sort_c13_hd]
  decide

theorem sort_gap_13 :
    sort_c13.getLast sort_c13_ne < sort_c14.head sort_c14_ne := by
  rw [sort_c13_last, sort_c14_hd]
  decide

theorem sort_gap_14 :
    sort_c14.getLast sort_c14_ne < sort_c15.head sort_c15_ne := by
  rw [sort_c14_last, sort_c15_hd]
  decide

theorem sort_gap_15 :
    sort_c15.getLast sort_c15_ne < sort_c16.head sort_c16_ne := by
  rw [sort_c15_last, sort_c16_hd]
  decide

theorem sort_gap_16 :
    sort_c16.getLast sort_c16_ne < sort_c17.head sort_c17_ne := by
  rw [sort_c16_last, sort_c17_hd]
  decide

theorem sort_gap_17 :
    sort_c17.getLast sort_c17_ne < sort_c18.head sort_c18_ne := by
  rw [sort_c17_last, sort_c18_hd]
  decide

theorem sort_gap_18 :
    sort_c18.getLast sort_c18_ne < sort_c19.head sort_c19_ne := by
  rw [sort_c18_last, sort_c19_hd]
  decide

theorem sort_gap_19 :
    sort_c19.getLast sort_c19_ne < sort_c20.head sort_c20_ne := by
  rw [sort_c19_last, sort_c20_hd]
  decide

theorem sort_gap_20 :
    sort_c20.getLast sort_c20_ne < sort_c21.head sort_c21_ne := by
  rw [sort_c20_last, sort_c21_hd]
  decide

theorem sort_gap_21 :
    sort_c21.getLast sort_c21_ne < sort_c22.head sort_c22_ne := by
  rw [sort_c21_last, sort_c22_hd]
  decide

theorem sort_gap_22 :
    sort_c22.getLast sort_c22_ne < sort_c23.head sort_c23_ne := by
  rw [sort_c22_last, sort_c23_hd]
  decide

theorem sort_gap_23 :
    sort_c23.getLast sort_c23_ne < sort_c24.head sort_c24_ne := by
  rw [sort_c23_last, sort_c24_hd]
  decide

theorem sort_gap_24 :
    sort_c24.getLast sort_c24_ne < sort_c25.head sort_c25_ne := by
  rw [sort_c24_last, sort_c25_hd]
  decide

theorem sort_gap_25 :
    sort_c25.getLast sort_c25_ne < sort_c26.head sort_c26_ne := by
  rw [sort_c25_last, sort_c26_hd]
  decide

theorem lows_prefix_01_last :
    (sort_c00).getLast lows_prefix_01_ne = sort_c00.getLast sort_c00_ne := by
  rfl

theorem lows_sorted_01 : isStrictSorted (sort_c00 ++ sort_c01) = true := by
  refine isStrictSorted_append (A := sort_c00) (B := sort_c01)
    lows_sorted_00 sort_c01_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_01_ne sort_c01_ne
    lows_sorted_00 sort_c01_sorted ?hlt
  rw [lows_prefix_01_last]
  exact sort_gap_00

theorem lows_prefix_02_ne : (sort_c00 ++ sort_c01) ≠ [] :=
  append_ne_nil_right (A := sort_c00) sort_c01_ne

theorem lows_prefix_02_last :
    (sort_c00 ++ sort_c01).getLast lows_prefix_02_ne = sort_c01.getLast sort_c01_ne := by
  have h := getLast_append_right (A := sort_c00) sort_c01_ne
  rw [getLast_proof_irrel lows_prefix_02_ne (append_ne_nil_right (A := sort_c00) sort_c01_ne)]
  exact h

theorem lows_sorted_02 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01) (B := sort_c02)
    lows_sorted_01 sort_c02_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_02_ne sort_c02_ne
    lows_sorted_01 sort_c02_sorted ?hlt
  rw [lows_prefix_02_last]
  exact sort_gap_01

theorem lows_prefix_03_ne : (sort_c00 ++ sort_c01 ++ sort_c02) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01) sort_c02_ne

theorem lows_prefix_03_last :
    (sort_c00 ++ sort_c01 ++ sort_c02).getLast lows_prefix_03_ne = sort_c02.getLast sort_c02_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01) sort_c02_ne
  rw [getLast_proof_irrel lows_prefix_03_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01) sort_c02_ne)]
  exact h

theorem lows_sorted_03 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02) (B := sort_c03)
    lows_sorted_02 sort_c03_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_03_ne sort_c03_ne
    lows_sorted_02 sort_c03_sorted ?hlt
  rw [lows_prefix_03_last]
  exact sort_gap_02

theorem lows_prefix_04_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02) sort_c03_ne

theorem lows_prefix_04_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03).getLast lows_prefix_04_ne = sort_c03.getLast sort_c03_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02) sort_c03_ne
  rw [getLast_proof_irrel lows_prefix_04_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02) sort_c03_ne)]
  exact h

theorem lows_sorted_04 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03) (B := sort_c04)
    lows_sorted_03 sort_c04_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_04_ne sort_c04_ne
    lows_sorted_03 sort_c04_sorted ?hlt
  rw [lows_prefix_04_last]
  exact sort_gap_03

theorem lows_prefix_05_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03) sort_c04_ne

theorem lows_prefix_05_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04).getLast lows_prefix_05_ne = sort_c04.getLast sort_c04_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03) sort_c04_ne
  rw [getLast_proof_irrel lows_prefix_05_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03) sort_c04_ne)]
  exact h

theorem lows_sorted_05 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04) (B := sort_c05)
    lows_sorted_04 sort_c05_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_05_ne sort_c05_ne
    lows_sorted_04 sort_c05_sorted ?hlt
  rw [lows_prefix_05_last]
  exact sort_gap_04

theorem lows_prefix_06_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04) sort_c05_ne

theorem lows_prefix_06_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05).getLast lows_prefix_06_ne = sort_c05.getLast sort_c05_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04) sort_c05_ne
  rw [getLast_proof_irrel lows_prefix_06_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04) sort_c05_ne)]
  exact h

theorem lows_sorted_06 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05) (B := sort_c06)
    lows_sorted_05 sort_c06_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_06_ne sort_c06_ne
    lows_sorted_05 sort_c06_sorted ?hlt
  rw [lows_prefix_06_last]
  exact sort_gap_05

theorem lows_prefix_07_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05) sort_c06_ne

theorem lows_prefix_07_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06).getLast lows_prefix_07_ne = sort_c06.getLast sort_c06_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05) sort_c06_ne
  rw [getLast_proof_irrel lows_prefix_07_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05) sort_c06_ne)]
  exact h

theorem lows_sorted_07 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06) (B := sort_c07)
    lows_sorted_06 sort_c07_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_07_ne sort_c07_ne
    lows_sorted_06 sort_c07_sorted ?hlt
  rw [lows_prefix_07_last]
  exact sort_gap_06

theorem lows_prefix_08_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06) sort_c07_ne

theorem lows_prefix_08_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07).getLast lows_prefix_08_ne = sort_c07.getLast sort_c07_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06) sort_c07_ne
  rw [getLast_proof_irrel lows_prefix_08_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06) sort_c07_ne)]
  exact h

theorem lows_sorted_08 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07) (B := sort_c08)
    lows_sorted_07 sort_c08_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_08_ne sort_c08_ne
    lows_sorted_07 sort_c08_sorted ?hlt
  rw [lows_prefix_08_last]
  exact sort_gap_07

theorem lows_prefix_09_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07) sort_c08_ne

theorem lows_prefix_09_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08).getLast lows_prefix_09_ne = sort_c08.getLast sort_c08_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07) sort_c08_ne
  rw [getLast_proof_irrel lows_prefix_09_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07) sort_c08_ne)]
  exact h

theorem lows_sorted_09 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08) (B := sort_c09)
    lows_sorted_08 sort_c09_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_09_ne sort_c09_ne
    lows_sorted_08 sort_c09_sorted ?hlt
  rw [lows_prefix_09_last]
  exact sort_gap_08

theorem lows_prefix_10_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08) sort_c09_ne

theorem lows_prefix_10_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09).getLast lows_prefix_10_ne = sort_c09.getLast sort_c09_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08) sort_c09_ne
  rw [getLast_proof_irrel lows_prefix_10_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08) sort_c09_ne)]
  exact h

theorem lows_sorted_10 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09) (B := sort_c10)
    lows_sorted_09 sort_c10_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_10_ne sort_c10_ne
    lows_sorted_09 sort_c10_sorted ?hlt
  rw [lows_prefix_10_last]
  exact sort_gap_09

theorem lows_prefix_11_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09) sort_c10_ne

theorem lows_prefix_11_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10).getLast lows_prefix_11_ne = sort_c10.getLast sort_c10_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09) sort_c10_ne
  rw [getLast_proof_irrel lows_prefix_11_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09) sort_c10_ne)]
  exact h

theorem lows_sorted_11 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10) (B := sort_c11)
    lows_sorted_10 sort_c11_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_11_ne sort_c11_ne
    lows_sorted_10 sort_c11_sorted ?hlt
  rw [lows_prefix_11_last]
  exact sort_gap_10

theorem lows_prefix_12_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10) sort_c11_ne

theorem lows_prefix_12_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11).getLast lows_prefix_12_ne = sort_c11.getLast sort_c11_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10) sort_c11_ne
  rw [getLast_proof_irrel lows_prefix_12_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10) sort_c11_ne)]
  exact h

theorem lows_sorted_12 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11) (B := sort_c12)
    lows_sorted_11 sort_c12_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_12_ne sort_c12_ne
    lows_sorted_11 sort_c12_sorted ?hlt
  rw [lows_prefix_12_last]
  exact sort_gap_11

theorem lows_prefix_13_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11) sort_c12_ne

theorem lows_prefix_13_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12).getLast lows_prefix_13_ne = sort_c12.getLast sort_c12_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11) sort_c12_ne
  rw [getLast_proof_irrel lows_prefix_13_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11) sort_c12_ne)]
  exact h

theorem lows_sorted_13 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12) (B := sort_c13)
    lows_sorted_12 sort_c13_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_13_ne sort_c13_ne
    lows_sorted_12 sort_c13_sorted ?hlt
  rw [lows_prefix_13_last]
  exact sort_gap_12

theorem lows_prefix_14_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12) sort_c13_ne

theorem lows_prefix_14_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13).getLast lows_prefix_14_ne = sort_c13.getLast sort_c13_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12) sort_c13_ne
  rw [getLast_proof_irrel lows_prefix_14_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12) sort_c13_ne)]
  exact h

theorem lows_sorted_14 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13) (B := sort_c14)
    lows_sorted_13 sort_c14_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_14_ne sort_c14_ne
    lows_sorted_13 sort_c14_sorted ?hlt
  rw [lows_prefix_14_last]
  exact sort_gap_13

theorem lows_prefix_15_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13) sort_c14_ne

theorem lows_prefix_15_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14).getLast lows_prefix_15_ne = sort_c14.getLast sort_c14_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13) sort_c14_ne
  rw [getLast_proof_irrel lows_prefix_15_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13) sort_c14_ne)]
  exact h

theorem lows_sorted_15 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14) (B := sort_c15)
    lows_sorted_14 sort_c15_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_15_ne sort_c15_ne
    lows_sorted_14 sort_c15_sorted ?hlt
  rw [lows_prefix_15_last]
  exact sort_gap_14

theorem lows_prefix_16_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14) sort_c15_ne

theorem lows_prefix_16_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15).getLast lows_prefix_16_ne = sort_c15.getLast sort_c15_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14) sort_c15_ne
  rw [getLast_proof_irrel lows_prefix_16_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14) sort_c15_ne)]
  exact h

theorem lows_sorted_16 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15) (B := sort_c16)
    lows_sorted_15 sort_c16_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_16_ne sort_c16_ne
    lows_sorted_15 sort_c16_sorted ?hlt
  rw [lows_prefix_16_last]
  exact sort_gap_15

theorem lows_prefix_17_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15) sort_c16_ne

theorem lows_prefix_17_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16).getLast lows_prefix_17_ne = sort_c16.getLast sort_c16_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15) sort_c16_ne
  rw [getLast_proof_irrel lows_prefix_17_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15) sort_c16_ne)]
  exact h

theorem lows_sorted_17 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16) (B := sort_c17)
    lows_sorted_16 sort_c17_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_17_ne sort_c17_ne
    lows_sorted_16 sort_c17_sorted ?hlt
  rw [lows_prefix_17_last]
  exact sort_gap_16

theorem lows_prefix_18_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16) sort_c17_ne

theorem lows_prefix_18_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17).getLast lows_prefix_18_ne = sort_c17.getLast sort_c17_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16) sort_c17_ne
  rw [getLast_proof_irrel lows_prefix_18_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16) sort_c17_ne)]
  exact h

theorem lows_sorted_18 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17) (B := sort_c18)
    lows_sorted_17 sort_c18_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_18_ne sort_c18_ne
    lows_sorted_17 sort_c18_sorted ?hlt
  rw [lows_prefix_18_last]
  exact sort_gap_17

theorem lows_prefix_19_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17) sort_c18_ne

theorem lows_prefix_19_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18).getLast lows_prefix_19_ne = sort_c18.getLast sort_c18_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17) sort_c18_ne
  rw [getLast_proof_irrel lows_prefix_19_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17) sort_c18_ne)]
  exact h

theorem lows_sorted_19 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18) (B := sort_c19)
    lows_sorted_18 sort_c19_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_19_ne sort_c19_ne
    lows_sorted_18 sort_c19_sorted ?hlt
  rw [lows_prefix_19_last]
  exact sort_gap_18

theorem lows_prefix_20_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18) sort_c19_ne

theorem lows_prefix_20_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19).getLast lows_prefix_20_ne = sort_c19.getLast sort_c19_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18) sort_c19_ne
  rw [getLast_proof_irrel lows_prefix_20_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18) sort_c19_ne)]
  exact h

theorem lows_sorted_20 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19) (B := sort_c20)
    lows_sorted_19 sort_c20_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_20_ne sort_c20_ne
    lows_sorted_19 sort_c20_sorted ?hlt
  rw [lows_prefix_20_last]
  exact sort_gap_19

theorem lows_prefix_21_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19) sort_c20_ne

theorem lows_prefix_21_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20).getLast lows_prefix_21_ne = sort_c20.getLast sort_c20_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19) sort_c20_ne
  rw [getLast_proof_irrel lows_prefix_21_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19) sort_c20_ne)]
  exact h

theorem lows_sorted_21 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20) (B := sort_c21)
    lows_sorted_20 sort_c21_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_21_ne sort_c21_ne
    lows_sorted_20 sort_c21_sorted ?hlt
  rw [lows_prefix_21_last]
  exact sort_gap_20

theorem lows_prefix_22_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20) sort_c21_ne

theorem lows_prefix_22_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21).getLast lows_prefix_22_ne = sort_c21.getLast sort_c21_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20) sort_c21_ne
  rw [getLast_proof_irrel lows_prefix_22_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20) sort_c21_ne)]
  exact h

theorem lows_sorted_22 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21) (B := sort_c22)
    lows_sorted_21 sort_c22_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_22_ne sort_c22_ne
    lows_sorted_21 sort_c22_sorted ?hlt
  rw [lows_prefix_22_last]
  exact sort_gap_21

theorem lows_prefix_23_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21) sort_c22_ne

theorem lows_prefix_23_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22).getLast lows_prefix_23_ne = sort_c22.getLast sort_c22_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21) sort_c22_ne
  rw [getLast_proof_irrel lows_prefix_23_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21) sort_c22_ne)]
  exact h

theorem lows_sorted_23 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22) (B := sort_c23)
    lows_sorted_22 sort_c23_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_23_ne sort_c23_ne
    lows_sorted_22 sort_c23_sorted ?hlt
  rw [lows_prefix_23_last]
  exact sort_gap_22

theorem lows_prefix_24_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22) sort_c23_ne

theorem lows_prefix_24_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23).getLast lows_prefix_24_ne = sort_c23.getLast sort_c23_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22) sort_c23_ne
  rw [getLast_proof_irrel lows_prefix_24_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22) sort_c23_ne)]
  exact h

theorem lows_sorted_24 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23) (B := sort_c24)
    lows_sorted_23 sort_c24_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_24_ne sort_c24_ne
    lows_sorted_23 sort_c24_sorted ?hlt
  rw [lows_prefix_24_last]
  exact sort_gap_23

theorem lows_prefix_25_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23) sort_c24_ne

theorem lows_prefix_25_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24).getLast lows_prefix_25_ne = sort_c24.getLast sort_c24_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23) sort_c24_ne
  rw [getLast_proof_irrel lows_prefix_25_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23) sort_c24_ne)]
  exact h

theorem lows_sorted_25 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24 ++ sort_c25) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24) (B := sort_c25)
    lows_sorted_24 sort_c25_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_25_ne sort_c25_ne
    lows_sorted_24 sort_c25_sorted ?hlt
  rw [lows_prefix_25_last]
  exact sort_gap_24

theorem lows_prefix_26_ne : (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24 ++ sort_c25) ≠ [] :=
  append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24) sort_c25_ne

theorem lows_prefix_26_last :
    (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24 ++ sort_c25).getLast lows_prefix_26_ne = sort_c25.getLast sort_c25_ne := by
  have h := getLast_append_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24) sort_c25_ne
  rw [getLast_proof_irrel lows_prefix_26_ne (append_ne_nil_right (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24) sort_c25_ne)]
  exact h

theorem lows_sorted_26 : isStrictSorted (sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24 ++ sort_c25 ++ sort_c26) = true := by
  refine isStrictSorted_append (A := sort_c00 ++ sort_c01 ++ sort_c02 ++ sort_c03 ++ sort_c04 ++ sort_c05 ++ sort_c06 ++ sort_c07 ++ sort_c08 ++ sort_c09 ++ sort_c10 ++ sort_c11 ++ sort_c12 ++ sort_c13 ++ sort_c14 ++ sort_c15 ++ sort_c16 ++ sort_c17 ++ sort_c18 ++ sort_c19 ++ sort_c20 ++ sort_c21 ++ sort_c22 ++ sort_c23 ++ sort_c24 ++ sort_c25) (B := sort_c26)
    lows_sorted_25 sort_c26_sorted ?gap
  refine all_lt_of_sorted_gap lows_prefix_26_ne sort_c26_ne
    lows_sorted_25 sort_c26_sorted ?hlt
  rw [lows_prefix_26_last]
  exact sort_gap_25

theorem lowsSorted_isStrictSorted : isStrictSorted lowsSorted = true := by
  rw [sort_split]
  exact lows_sorted_26

theorem lowsSorted_nodup : lowsSorted.Nodup :=
  isStrictSorted_nodup _ lowsSorted_isStrictSorted

theorem lowsFlat_nodup : lowsFlat.Nodup :=
  nodup_of_supset_nodup_length lowsSorted_nodup lowsSorted_subset lows_len_eq

/-- Re-export so `Block0Lows.lowsFlat` stays defeq to the Data literal (and to LowsOf). -/
abbrev lowsFlat := _root_.IntMul.Kappa.R8.Bit.Oppbank.Block0LowsData.lowsFlat
abbrev lowsSorted := _root_.IntMul.Kappa.R8.Bit.Oppbank.Block0LowsData.lowsSorted

end IntMul.Kappa.R8.Bit.Oppbank.Block0Lows


