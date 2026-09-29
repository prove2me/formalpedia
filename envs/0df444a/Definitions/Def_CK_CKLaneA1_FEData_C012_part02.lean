-- Prove2me | Definitions.Def_CK_CKLaneA1_FEData_C012_part02
-- name    : CK_CKLaneA1_FEData_C012_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T23:02:04.552021+00:00
-- url     : https://prove2.me/theorems/46faa5ed-3d7e-4c97-9835-02401fce04c0
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FEData.C012` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FEData.C012` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FEData.C012` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FEData.C012 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FEData/C012.lean)

import Definitions.Def_CK_CKLaneA1_FEData_C012_part01

/-! Generated fixedEdge cover chunk 12 (183 cells, 1 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.stripOK`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.FEData

open CKLaneA1


def strips012_s0_c40 : List FECell := [
  ⟨⟨2738188573441261568, 2, 0⟩, ⟨5861461073612251136, 6410298934983897088, 0, 0, 0, 0⟩⟩,
  ⟨⟨2882303761517117440, 2, 0⟩, ⟨6037407253685555200, 6564690615454908416, 0, 0, 0, 0⟩⟩,
  ⟨⟨3026418949592973312, 2, 0⟩, ⟨6206646544746791936, 6713874461987846144, 0, 0, 0, 0⟩⟩,
  ⟨⟨3170534137668829184, 2, 0⟩, ⟨6369890526764691456, 6858399734658537472, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c40_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨2594073385365405696, 2, 0⟩) strips012_s0_c40 = true := by
  decide +kernel

theorem strips012_s0_c40_start : (⟨2594073385365405696, 2, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35 ++ strips012_s0_c36 ++ strips012_s0_c37 ++ strips012_s0_c38 ++ strips012_s0_c39) := rfl

def strips012_s0_c41 : List FECell := [
  ⟨⟨3314649325744685056, 2, 0⟩, ⟨6527750196189067264, 6998737586928659456, 0, 0, 0, 0⟩⟩,
  ⟨⟨3458764513820540928, 2, 0⟩, ⟨6680753797116647424, 7135295170187003904, 0, 0, 0, 0⟩⟩,
  ⟨⟨3602879701896396800, 2, 0⟩, ⟨6829360922953127936, 7268426714124081152, 0, 0, 0, 0⟩⟩,
  ⟨⟨3746994889972252672, 1, 0⟩, ⟨6973973777797988352, 7398442324958737408, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c41_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨3170534137668829184, 2, 0⟩) strips012_s0_c41 = true := by
  decide +kernel

theorem strips012_s0_c41_start : (⟨3170534137668829184, 2, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35 ++ strips012_s0_c36 ++ strips012_s0_c37 ++ strips012_s0_c38 ++ strips012_s0_c39 ++ strips012_s0_c40) := rfl

def strips012_s0_c42 : List FECell := [
  ⟨⟨4035225266123964416, 1, 0⟩, ⟨7020033900035578880, 7755213471366845440, 0, 0, 0, 0⟩⟩,
  ⟨⟨4323455642275676160, 1, 0⟩, ⟨7299985926860383232, 7988054417204900864, 0, 0, 0, 0⟩⟩,
  ⟨⟨4611686018427387904, 1, 0⟩, ⟨7568220145178777600, 8213604049513919488, 0, 0, 0, 0⟩⟩,
  ⟨⟨4899916394579099648, 1, 0⟩, ⟨7826483315012528128, 8432924724328168448, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c42_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨3746994889972252672, 1, 0⟩) strips012_s0_c42 = true := by
  decide +kernel

theorem strips012_s0_c42_start : (⟨3746994889972252672, 1, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35 ++ strips012_s0_c36 ++ strips012_s0_c37 ++ strips012_s0_c38 ++ strips012_s0_c39 ++ strips012_s0_c40 ++ strips012_s0_c41) := rfl

def strips012_s0_c43 : List FECell := [
  ⟨⟨5188146770730811392, 1, 0⟩, ⟨8076203281937540096, 8646892783666237440, 0, 0, 0, 0⟩⟩,
  ⟨⟨5476377146882523136, 1, 0⟩, ⟨8318562301258953728, 8856240895285328896, 0, 0, 0, 0⟩⟩,
  ⟨⟨5764607523034234880, 1, 0⟩, ⟨8554550721754878976, 9061589033523840000, 0, 0, 0, 0⟩⟩,
  ⟨⟨6052837899185946624, 1, 0⟩, ⟨8785006973889846272, 9263467576020486144, 0, 0, 0, 1⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c43_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨4899916394579099648, 1, 0⟩) strips012_s0_c43 = true := by
  decide +kernel

theorem strips012_s0_c43_start : (⟨4899916394579099648, 1, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35 ++ strips012_s0_c36 ++ strips012_s0_c37 ++ strips012_s0_c38 ++ strips012_s0_c39 ++ strips012_s0_c40 ++ strips012_s0_c41 ++ strips012_s0_c42) := rfl

def strips012_s0_c44 : List FECell := [
  ⟨⟨6341068275337658368, 0, 0⟩, ⟨9010647822722912256, 9462334812171821056, 0, 0, 0, 1⟩⟩,
  ⟨⟨6629298651489370112, 0, 0⟩, ⟨9232091580102010880, 9658590416043257856, 0, 1, 0, 1⟩⟩,
  ⟨⟨6917529027641081856, 0, 0⟩, ⟨9449876144959950848, 9852585955989432320, 0, 1, 0, 1⟩⟩,
  ⟨⟨7493989779944505344, 0, 0⟩, ⟨9611488805855246336, 10297063084442249216, 0, 1, 0, 1⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c44_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨6052837899185946624, 1, 0⟩) strips012_s0_c44 = true := by
  decide +kernel

theorem strips012_s0_c44_start : (⟨6052837899185946624, 1, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35 ++ strips012_s0_c36 ++ strips012_s0_c37 ++ strips012_s0_c38 ++ strips012_s0_c39 ++ strips012_s0_c40 ++ strips012_s0_c41 ++ strips012_s0_c42 ++ strips012_s0_c43) := rfl

def strips012_s0_c45 : List FECell := [
  ⟨⟨8070450532247928832, 0, 0⟩, ⟨10049907710660444160, 10655718943596042240, 0, 1, 0, 1⟩⟩,
  ⟨⟨8646911284551352320, 0, 0⟩, ⟨10479184126816034816, 11011684056339476480, 0, 1, 0, 1⟩⟩,
  ⟨⟨9223372036854775808, 0, 1⟩, ⟨10901789146057531392, 11366153358682933248, 0, 1, 0, 1⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c45_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨7493989779944505344, 0, 0⟩) strips012_s0_c45 = true := by
  decide +kernel

theorem strips012_s0_c45_start : (⟨7493989779944505344, 0, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35 ++ strips012_s0_c36 ++ strips012_s0_c37 ++ strips012_s0_c38 ++ strips012_s0_c39 ++ strips012_s0_c40 ++ strips012_s0_c41 ++ strips012_s0_c42 ++ strips012_s0_c43 ++ strips012_s0_c44) := rfl

end CKLaneA1.FEData


