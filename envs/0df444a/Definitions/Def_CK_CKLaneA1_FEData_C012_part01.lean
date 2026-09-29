-- Prove2me | Definitions.Def_CK_CKLaneA1_FEData_C012_part01
-- name    : CK_CKLaneA1_FEData_C012_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:08:06.936469+00:00
-- url     : https://prove2.me/theorems/c02305f2-71b5-457c-9e50-797b589c34bb
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

import Definitions.Def_CK_CKLaneA1_FEData_C012_part00

/-! Generated fixedEdge cover chunk 12 (183 cells, 1 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.stripOK`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.FEData

open CKLaneA1


def strips012_s0_c20 : List FECell := [
  ⟨⟨536829075582563122, 5, 0⟩, ⟨1523388697680666368, 1693999172497358336, 0, 0, 0, 0⟩⟩,
  ⟨⟨540431955284459519, 5, 0⟩, ⟨1530030616463662080, 1714614396188549632, 0, 0, 0, 0⟩⟩,
  ⟨⟨544034834986355916, 5, 0⟩, ⟨1548041740731378688, 1732375117351672064, 0, 0, 0, 0⟩⟩,
  ⟨⟨547637714688252313, 5, 0⟩, ⟨1565942349315515392, 1750024869160145408, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c20_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨535027635731614924, 5, 0⟩) strips012_s0_c20 = true := by
  decide +kernel

theorem strips012_s0_c20_start : (⟨535027635731614924, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19) := rfl

def strips012_s0_c21 : List FECell := [
  ⟨⟨551240594390148709, 5, 0⟩, ⟨1583733732405408768, 1767564976548817920, 0, 0, 0, 0⟩⟩,
  ⟨⟨554843474092045106, 5, 0⟩, ⟨1601417158965297664, 1784996742158784256, 0, 0, 0, 0⟩⟩,
  ⟨⟨558446353793941503, 5, 0⟩, ⟨1618993877184710144, 1802321446820782336, 0, 0, 0, 0⟩⟩,
  ⟨⟨562049233495837900, 4, 0⟩, ⟨1636465114917113600, 1819540350025744896, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c21_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨547637714688252313, 5, 0⟩) strips012_s0_c21 = true := by
  decide +kernel

theorem strips012_s0_c21_start : (⟨547637714688252313, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20) := rfl

def strips012_s0_c22 : List FECell := [
  ⟨⟨565652113197734297, 4, 0⟩, ⟨1653832080107196160, 1836654690382905088, 0, 0, 0, 0⟩⟩,
  ⟨⟨569254992899630694, 4, 0⟩, ⟨1671095961207131392, 1853665686065848064, 0, 0, 0, 0⟩⟩,
  ⟨⟨572857872601527091, 4, 0⟩, ⟨1688257927582158336, 1870574535246886912, 0, 0, 0, 0⟩⟩,
  ⟨⟨576460752303423488, 4, 0⟩, ⟨1705319129905808384, 1887382416520125696, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c22_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨562049233495837900, 4, 0⟩) strips012_s0_c22 = true := by
  decide +kernel

theorem strips012_s0_c22_start : (⟨562049233495837900, 4, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21) := rfl

def strips012_s0_c23 : List FECell := [
  ⟨⟨580964351930793984, 4, 0⟩, ⟨1721002544965675008, 1909700346243032832, 0, 0, 0, 0⟩⟩,
  ⟨⟨585467951558164480, 4, 0⟩, ⟨1742058703756268032, 1930422449922470656, 0, 0, 0, 0⟩⟩,
  ⟨⟨589971551185534976, 4, 0⟩, ⟨1762963280762737920, 1950992798543884032, 0, 0, 0, 0⟩⟩,
  ⟨⟨594475150812905472, 4, 0⟩, ⟨1783718366924760064, 1971413532777396480, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c23_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨576460752303423488, 4, 0⟩) strips012_s0_c23 = true := by
  decide +kernel

theorem strips012_s0_c23_start : (⟨576460752303423488, 4, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22) := rfl

def strips012_s0_c24 : List FECell := [
  ⟨⟨598978750440275968, 4, 0⟩, ⟨1804326012589321216, 1991686750777057536, 0, 0, 0, 0⟩⟩,
  ⟨⟨603482350067646464, 4, 0⟩, ⟨1824788228525079552, 2011814509267089920, 0, 0, 0, 0⟩⟩,
  ⟨⟨607985949695016960, 4, 0⟩, ⟨1845106986905687296, 2031798824594190336, 0, 0, 0, 0⟩⟩,
  ⟨⟨612489549322387456, 4, 0⟩, ⟨1865284222263200768, 2051641673747141632, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c24_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨594475150812905472, 4, 0⟩) strips012_s0_c24 = true := by
  decide +kernel

theorem strips012_s0_c24_start : (⟨594475150812905472, 4, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23) := rfl

def strips012_s0_c25 : List FECell := [
  ⟨⟨616993148949757952, 4, 0⟩, ⟨1885321832412655616, 2071344995344942080, 0, 0, 0, 0⟩⟩,
  ⟨⟨621496748577128448, 4, 0⟩, ⟨1905221679348845568, 2090910690594596864, 0, 0, 0, 0⟩⟩,
  ⟨⟨626000348204498944, 4, 0⟩, ⟨1924985590116289792, 2110340624219679488, 0, 0, 0, 0⟩⟩,
  ⟨⟨630503947831869440, 4, 0⟩, ⟨1944615357653344512, 2129636625360716288, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c25_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨612489549322387456, 4, 0⟩) strips012_s0_c25 = true := by
  decide +kernel

theorem strips012_s0_c25_start : (⟨612489549322387456, 4, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24) := rfl

def strips012_s0_c26 : List FECell := [
  ⟨⟨635007547459239936, 4, 0⟩, ⟨1964112741611366400, 2148800488448406784, 0, 0, 0, 0⟩⟩,
  ⟨⟨639511147086610432, 4, 0⟩, ⟨1983479469149801472, 2167833974050651392, 0, 0, 0, 0⟩⟩,
  ⟨⟨648518346341351424, 4, 0⟩, ⟨1995933812140032256, 2213168313395663872, 0, 0, 0, 0⟩⟩,
  ⟨⟨657525545596092416, 4, 0⟩, ⟨2033981396278769408, 2250385109468214528, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c26_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨630503947831869440, 4, 0⟩) strips012_s0_c26 = true := by
  decide +kernel

theorem strips012_s0_c26_start : (⟨630503947831869440, 4, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25) := rfl

def strips012_s0_c27 : List FECell := [
  ⟨⟨666532744850833408, 4, 0⟩, ⟨2071535665782091264, 2287110941064800512, 0, 0, 0, 0⟩⟩,
  ⟨⟨675539944105574400, 4, 0⟩, ⟨2108608977638064896, 2323358420157028352, 0, 0, 0, 0⟩⟩,
  ⟨⟨684547143360315392, 4, 0⟩, ⟨2145213255416229888, 2359139704448096256, 0, 0, 0, 0⟩⟩,
  ⟨⟨693554342615056384, 4, 0⟩, ⟨2181360008716233728, 2394466518306724352, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c27_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨657525545596092416, 4, 0⟩) strips012_s0_c27 = true := by
  decide +kernel

theorem strips012_s0_c27_start : (⟨657525545596092416, 4, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26) := rfl

def strips012_s0_c28 : List FECell := [
  ⟨⟨702561541869797376, 4, 0⟩, ⟨2217060351555116032, 2429350172528557056, 0, 0, 0, 0⟩⟩,
  ⟨⟨711568741124538368, 4, 0⟩, ⟨2252325019761438208, 2463801583002278400, 0, 0, 0, 0⟩⟩,
  ⟨⟨720575940379279360, 4, 0⟩, ⟨2287164387439406336, 2497831288351839744, 0, 0, 0, 0⟩⟩,
  ⟨⟨729583139634020352, 4, 0⟩, ⟨2321588482561516544, 2531449466620844544, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c28_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨693554342615056384, 4, 0⟩) strips012_s0_c28 = true := by
  decide +kernel

theorem strips012_s0_c28_start : (⟨693554342615056384, 4, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27) := rfl

def strips012_s0_c29 : List FECell := [
  ⟨⟨738590338888761344, 4, 0⟩, ⟨2355607001744014848, 2564665951060243968, 0, 0, 0, 0⟩⟩,
  ⟨⟨747597538143502336, 4, 0⟩, ⟨2389229324255566848, 2597490245076008448, 0, 0, 0, 0⟩⟩,
  ⟨⟨756604737398243328, 4, 0⟩, ⟨2422464525305966080, 2629931536389317120, 0, 0, 0, 0⟩⟩,
  ⟨⟨765611936652984320, 4, 0⟩, ⟨2455321388658411520, 2661998710458054656, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c29_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨729583139634020352, 4, 0⟩) strips012_s0_c29 = true := by
  decide +kernel

theorem strips012_s0_c29_start : (⟨729583139634020352, 4, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28) := rfl

def strips012_s0_c30 : List FECell := [
  ⟨⟨774619135907725312, 4, 0⟩, ⟨2487808418605865984, 2693700363204897280, 0, 0, 0, 0⟩⟩,
  ⟨⟨783626335162466304, 4, 0⟩, ⟨2519933851349211648, 2725044813094122496, 0, 0, 0, 0⟩⟩,
  ⟨⟨792633534417207296, 4, 0⟩, ⟨2551705665812346368, 2756040112596294656, 0, 0, 0, 0⟩⟩,
  ⟨⟨810647932926689280, 4, 0⟩, ⟨2568746702982075904, 2833117360655786496, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c30_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨765611936652984320, 4, 0⟩) strips012_s0_c30 = true := by
  decide +kernel

theorem strips012_s0_c30_start : (⟨765611936652984320, 4, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29) := rfl

def strips012_s0_c31 : List FECell := [
  ⟨⟨828662331436171264, 4, 0⟩, ⟨2630541264915996160, 2892788156156595200, 0, 0, 0, 0⟩⟩,
  ⟨⟨846676729945653248, 4, 0⟩, ⟨2691049569778695168, 2951200131160475136, 0, 0, 0, 0⟩⟩,
  ⟨⟨864691128455135232, 4, 0⟩, ⟨2750324660045732864, 3008406625484364800, 0, 0, 0, 0⟩⟩,
  ⟨⟨882705526964617216, 4, 0⟩, ⟨2808416534294703616, 3064457824306507776, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c31_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨810647932926689280, 4, 0⟩) strips012_s0_c31 = true := by
  decide +kernel

theorem strips012_s0_c31_start : (⟨810647932926689280, 4, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30) := rfl

def strips012_s0_c32 : List FECell := [
  ⟨⟨900719925474099200, 4, 0⟩, ⟨2865372368951319552, 3119400995270080000, 0, 0, 0, 0⟩⟩,
  ⟨⟨918734323983581184, 4, 0⟩, ⟨2921236720564057600, 3173280704101153792, 0, 0, 0, 0⟩⟩,
  ⟨⟨936748722493063168, 4, 0⟩, ⟨2976051710601210368, 3226139011010879488, 0, 0, 0, 0⟩⟩,
  ⟨⟨954763121002545152, 4, 0⟩, ⟨3029857194531533312, 3278015649878670336, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c32_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨882705526964617216, 4, 0⟩) strips012_s0_c32 = true := by
  decide +kernel

theorem strips012_s0_c32_start : (⟨882705526964617216, 4, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31) := rfl

def strips012_s0_c33 : List FECell := [
  ⟨⟨972777519512027136, 4, 0⟩, ⟨3082690916747436544, 3328948191976846848, 0, 0, 0, 0⟩⟩,
  ⟨⟨990791918021509120, 4, 0⟩, ⟨3134588652713456640, 3378972195792181760, 0, 0, 0, 0⟩⟩,
  ⟨⟨1008806316530991104, 4, 0⟩, ⟨3185584339568820736, 3428121344321492992, 0, 0, 0, 0⟩⟩,
  ⟨⟨1044835113549955072, 4, 0⟩, ⟨3207308452320452096, 3555799288697708544, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c33_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨954763121002545152, 4, 0⟩) strips012_s0_c33 = true := by
  decide +kernel

theorem strips012_s0_c33_start : (⟨954763121002545152, 4, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32) := rfl

def strips012_s0_c34 : List FECell := [
  ⟨⟨1080863910568919040, 4, 0⟩, ⟨3305183374444117504, 3648181331123651584, 0, 0, 0, 0⟩⟩,
  ⟨⟨1116892707587883008, 3, 0⟩, ⟨3399954666126630912, 3737623990279973888, 0, 0, 0, 0⟩⟩,
  ⟨⟨1152921504606846976, 3, 0⟩, ⟨3491824212958909440, 3824324031187110400, 0, 0, 0, 0⟩⟩,
  ⟨⟨1188950301625810944, 3, 0⟩, ⟨3580975781794108928, 3908459944604022272, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c34_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨1044835113549955072, 4, 0⟩) strips012_s0_c34 = true := by
  decide +kernel

theorem strips012_s0_c34_start : (⟨1044835113549955072, 4, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33) := rfl

def strips012_s0_c35 : List FECell := [
  ⟨⟨1224979098644774912, 3, 0⟩, ⟨3667577066385788416, 3990194087319910400, 0, 0, 0, 0⟩⟩,
  ⟨⟨1261007895663738880, 3, 0⟩, ⟨3751781457415447040, 4069674522982584320, 0, 0, 0, 0⟩⟩,
  ⟨⟨1297036692682702848, 3, 0⟩, ⟨3833729579766898176, 4147036611840605696, 0, 0, 0, 0⟩⟩,
  ⟨⟨1333065489701666816, 3, 0⟩, ⟨3913550632389810688, 4222404388964019200, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c35_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨1188950301625810944, 3, 0⟩) strips012_s0_c35 = true := by
  decide +kernel

theorem strips012_s0_c35_start : (⟨1188950301625810944, 3, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34) := rfl

def strips012_s0_c36 : List FECell := [
  ⟨⟨1369094286720630784, 3, 0⟩, ⟨3991363560040451072, 4295891763475020800, 0, 0, 0, 0⟩⟩,
  ⟨⟨1405123083739594752, 3, 0⟩, ⟨4067278081283483648, 4367603565672649728, 0, 0, 0, 0⟩⟩,
  ⟨⟨1441151880758558720, 3, 0⟩, ⟨4141395593145552896, 4437636464375662592, 0, 0, 0, 0⟩⟩,
  ⟨⟨1513209474796486656, 3, 0⟩, ⟨4163228110052405248, 4629714986545037312, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c36_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨1333065489701666816, 3, 0⟩) strips012_s0_c36 = true := by
  decide +kernel

theorem strips012_s0_c36_start : (⟨1333065489701666816, 3, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35) := rfl

def strips012_s0_c37 : List FECell := [
  ⟨⟨1585267068834414592, 3, 0⟩, ⟨4304245415019277824, 4757931088651366400, 0, 0, 0, 0⟩⟩,
  ⟨⟨1657324662872342528, 3, 0⟩, ⟨4439435584211721728, 4881003823421076480, 0, 0, 0, 0⟩⟩,
  ⟨⟨1729382256910270464, 3, 0⟩, ⟨4569331763007550464, 4999414176347426816, 0, 0, 0, 0⟩⟩,
  ⟨⟨1801439850948198400, 3, 0⟩, ⟨4694400479436154880, 5113581083594484736, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c37_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨1513209474796486656, 3, 0⟩) strips012_s0_c37 = true := by
  decide +kernel

theorem strips012_s0_c37_start : (⟨1513209474796486656, 3, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35 ++ strips012_s0_c36) := rfl

def strips012_s0_c38 : List FECell := [
  ⟨⟨1873497444986126336, 3, 0⟩, ⟨4815052036464414720, 5223871476840054784, 0, 0, 0, 0⟩⟩,
  ⟨⟨1945555039024054272, 3, 0⟩, ⟨4931648987206434816, 5330608400370113536, 0, 0, 0, 0⟩⟩,
  ⟨⟨2017612633061982208, 3, 0⟩, ⟨5044513097413459968, 5434077623973336064, 0, 0, 0, 0⟩⟩,
  ⟨⟨2089670227099910144, 2, 0⟩, ⟨5153931104315900928, 5534533071161484288, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c38_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨1801439850948198400, 3, 0⟩) strips012_s0_c38 = true := by
  decide +kernel

theorem strips012_s0_c38_start : (⟨1801439850948198400, 3, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35 ++ strips012_s0_c36 ++ strips012_s0_c37) := rfl

def strips012_s0_c39 : List FECell := [
  ⟨⟨2161727821137838080, 2, 0⟩, ⟨5260159510268721152, 5632201306284777472, 0, 0, 0, 0⟩⟩,
  ⟨⟨2305843009213693952, 2, 0⟩, ⟨5284228955995792384, 5908790340438752256, 0, 0, 0, 0⟩⟩,
  ⟨⟨2449958197289549824, 2, 0⟩, ⟨5485955411132325888, 6083189970344585216, 0, 0, 0, 0⟩⟩,
  ⟨⟨2594073385365405696, 2, 0⟩, ⟨5677973053622922240, 6250053888164554752, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c39_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨2089670227099910144, 2, 0⟩) strips012_s0_c39 = true := by
  decide +kernel

theorem strips012_s0_c39_start : (⟨2089670227099910144, 2, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35 ++ strips012_s0_c36 ++ strips012_s0_c37 ++ strips012_s0_c38) := rfl

end CKLaneA1.FEData


