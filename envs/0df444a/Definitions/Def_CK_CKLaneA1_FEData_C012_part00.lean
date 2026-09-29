-- Prove2me | Definitions.Def_CK_CKLaneA1_FEData_C012_part00
-- name    : CK_CKLaneA1_FEData_C012_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:50:35.222146+00:00
-- url     : https://prove2.me/theorems/7918ccac-c9cb-4b5a-83b5-b6036cf9ea04
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

import Definitions.Def_CK_CKLaneA1_FEStrip
import Definitions.Def_CK_CKLaneA1_SplitLemmas

/-! Generated fixedEdge cover chunk 12 (183 cells, 1 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.stripOK`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.FEData

open CKLaneA1


def strips012_s0_c0 : List FECell := [
  ⟨⟨461393781824107314, 5, 0⟩, ⟨1127480683569607680, 1289676917691756288, 0, 0, 0, 0⟩⟩,
  ⟨⟨461618961805475839, 5, 0⟩, ⟨1128779917429291520, 1290964796019947776, 0, 0, 0, 0⟩⟩,
  ⟨⟨461844141786844364, 5, 0⟩, ⟨1130078579811011328, 1292252097704266240, 0, 0, 0, 0⟩⟩,
  ⟨⟨462069321768212889, 5, 0⟩, ⟨1131376671188256768, 1293538823232017664, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c0_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨461168601842738790, 5, 0⟩) strips012_s0_c0 = true := by
  decide +kernel

def strips012_s0_c1 : List FECell := [
  ⟨⟨462294501749581413, 5, 0⟩, ⟨1132674192033961472, 1294824973089924352, 0, 0, 0, 0⟩⟩,
  ⟨⟨462519681730949938, 5, 0⟩, ⟨1133971142820502912, 1296110547764126208, 0, 0, 0, 0⟩⟩,
  ⟨⟨462744861712318463, 5, 0⟩, ⟨1135267524019704064, 1297395547740181760, 0, 0, 0, 0⟩⟩,
  ⟨⟨462970041693686988, 5, 0⟩, ⟨1136563336102834176, 1298679973503067904, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c1_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨462069321768212889, 5, 0⟩) strips012_s0_c1 = true := by
  decide +kernel

theorem strips012_s0_c1_start : (⟨462069321768212889, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0) := rfl

def strips012_s0_c2 : List FECell := [
  ⟨⟨463420401656424037, 5, 0⟩, ⟨1137605989119077376, 1301542024350408960, 0, 0, 0, 0⟩⟩,
  ⟨⟨463870761619161087, 5, 0⟩, ⟨1140194385475166592, 1304107221711645696, 0, 0, 0, 0⟩⟩,
  ⟨⟨464321121581898136, 5, 0⟩, ⟨1142780513983051520, 1306670130799820544, 0, 0, 0, 0⟩⟩,
  ⟨⟨464771481544635186, 5, 0⟩, ⟨1145364378385466112, 1309230755467955968, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c2_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨462970041693686988, 5, 0⟩) strips012_s0_c2 = true := by
  decide +kernel

theorem strips012_s0_c2_start : (⟨462970041693686988, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1) := rfl

def strips012_s0_c3 : List FECell := [
  ⟨⟨465221841507372235, 5, 0⟩, ⟨1147945982416386560, 1311789099559885568, 0, 0, 0, 0⟩⟩,
  ⟨⟨465672201470109285, 5, 0⟩, ⟨1150525329801058432, 1314345166910282752, 0, 0, 0, 0⟩⟩,
  ⟨⟨466122561432846334, 5, 0⟩, ⟨1153102424256022528, 1316898961344687616, 0, 0, 0, 0⟩⟩,
  ⟨⟨466572921395583384, 5, 0⟩, ⟨1155677269489141760, 1319450486679537408, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c3_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨464771481544635186, 5, 0⟩) strips012_s0_c3 = true := by
  decide +kernel

theorem strips012_s0_c3_start : (⟨464771481544635186, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2) := rfl

def strips012_s0_c4 : List FECell := [
  ⟨⟨467023281358320433, 5, 0⟩, ⟨1158249869199627264, 1321999746722192384, 0, 0, 0, 0⟩⟩,
  ⟨⟨467473641321057483, 5, 0⟩, ⟨1160820227078064896, 1324546745270964992, 0, 0, 0, 0⟩⟩,
  ⟨⟨467924001283794533, 5, 0⟩, ⟨1163388346806441472, 1327091486115148288, 0, 0, 0, 0⟩⟩,
  ⟨⟨468374361246531583, 5, 0⟩, ⟨1165954232058170112, 1329633973035042560, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c4_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨466572921395583384, 5, 0⟩) strips012_s0_c4 = true := by
  decide +kernel

theorem strips012_s0_c4_start : (⟨466572921395583384, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3) := rfl

def strips012_s0_c5 : List FECell := [
  ⟨⟨468824721209268632, 5, 0⟩, ⟨1168517886498116864, 1332174209801983232, 0, 0, 0, 0⟩⟩,
  ⟨⟨469275081172005682, 5, 0⟩, ⟨1171079313782626560, 1334712200178369536, 0, 0, 0, 0⟩⟩,
  ⟨⟨469725441134742731, 5, 0⟩, ⟨1173638517559548416, 1337247947917690368, 0, 0, 0, 0⟩⟩,
  ⟨⟨470175801097479781, 5, 0⟩, ⟨1176195501468260864, 1339781456764552960, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c5_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨468374361246531583, 5, 0⟩) strips012_s0_c5 = true := by
  decide +kernel

theorem strips012_s0_c5_start : (⟨468374361246531583, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4) := rfl

def strips012_s0_c6 : List FECell := [
  ⟨⟨470626161060216830, 5, 0⟩, ⟨1178750269139699200, 1342312730454709760, 0, 0, 0, 0⟩⟩,
  ⟨⟨471076521022953880, 5, 0⟩, ⟨1181302824196378880, 1344841772715085312, 0, 0, 0, 0⟩⟩,
  ⟨⟨471526880985690930, 5, 0⟩, ⟨1183853170252422144, 1347368587263803392, 0, 0, 0, 0⟩⟩,
  ⟨⟨471977240948427980, 5, 0⟩, ⟨1186401310913582336, 1349893177810214656, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c6_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨470175801097479781, 5, 0⟩) strips012_s0_c6 = true := by
  decide +kernel

theorem strips012_s0_c6_start : (⟨470175801097479781, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5) := rfl

def strips012_s0_c7 : List FECell := [
  ⟨⟨472427600911165029, 5, 0⟩, ⟨1188947249777270784, 1352415548054922496, 0, 0, 0, 0⟩⟩,
  ⟨⟨472877960873902079, 5, 0⟩, ⟨1191490990432579840, 1354935701689810432, 0, 0, 0, 0⟩⟩,
  ⟨⟨473328320836639128, 5, 0⟩, ⟨1194032536460309504, 1357453642398068480, 0, 0, 0, 0⟩⟩,
  ⟨⟨473778680799376178, 5, 0⟩, ⟨1196571891432990976, 1359969373854220288, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c7_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨471977240948427980, 5, 0⟩) strips012_s0_c7 = true := by
  decide +kernel

theorem strips012_s0_c7_start : (⟨471977240948427980, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6) := rfl

def strips012_s0_c8 : List FECell := [
  ⟨⟨474229040762113227, 5, 0⟩, ⟨1199109058914912512, 1362482899724148224, 0, 0, 0, 0⟩⟩,
  ⟨⟨474679400724850277, 5, 0⟩, ⟨1201644042462144256, 1364994223665121536, 0, 0, 0, 0⟩⟩,
  ⟨⟨475580120650324377, 5, 0⟩, ⟨1203652713219747840, 1370619213371746048, 0, 0, 0, 0⟩⟩,
  ⟨⟨476480840575798476, 5, 0⟩, ⟨1208710359514475520, 1375627821972394240, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c8_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨473778680799376178, 5, 0⟩) strips012_s0_c8 = true := by
  decide +kernel

theorem strips012_s0_c8_start : (⟨473778680799376178, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7) := rfl

def strips012_s0_c9 : List FECell := [
  ⟨⟨477381560501272575, 5, 0⟩, ⟨1213759334756258048, 1380627687485629184, 0, 0, 0, 0⟩⟩,
  ⟨⟨478282280426746674, 5, 0⟩, ⟨1218799666989494528, 1385618838773671936, 0, 0, 0, 0⟩⟩,
  ⟨⟨479183000352220773, 5, 0⟩, ⟨1223831384130122752, 1390601304563915008, 0, 0, 0, 0⟩⟩,
  ⟨⟨480083720277694872, 5, 0⟩, ⟨1228854513966383616, 1395575113449738752, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c9_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨476480840575798476, 5, 0⟩) strips012_s0_c9 = true := by
  decide +kernel

theorem strips012_s0_c9_start : (⟨476480840575798476, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8) := rfl

def strips012_s0_c10 : List FECell := [
  ⟨⟨480984440203168971, 5, 0⟩, ⟨1233869084159578368, 1400540293891321344, 0, 0, 0, 0⟩⟩,
  ⟨⟨481885160128643070, 5, 0⟩, ⟨1238875122244823040, 1405496874216443648, 0, 0, 0, 0⟩⟩,
  ⟨⟨482785880054117170, 5, 0⟩, ⟨1243872655631794944, 1410444882621286912, 0, 0, 0, 0⟩⟩,
  ⟨⟨483686599979591269, 5, 0⟩, ⟨1248861711605474560, 1415384347171224832, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c10_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨480083720277694872, 5, 0⟩) strips012_s0_c10 = true := by
  decide +kernel

theorem strips012_s0_c10_start : (⟨480083720277694872, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9) := rfl

def strips012_s0_c11 : List FECell := [
  ⟨⟨484587319905065368, 5, 0⟩, ⟨1253842317326882048, 1420315295801611520, 0, 0, 0, 0⟩⟩,
  ⟨⟨485488039830539467, 5, 0⟩, ⟨1258814499833807872, 1425237756318560256, 0, 0, 0, 0⟩⟩,
  ⟨⟨486388759756013567, 5, 0⟩, ⟨1263778286041539840, 1430151756399718912, 0, 0, 0, 0⟩⟩,
  ⟨⟨487289479681487666, 5, 0⟩, ⟨1268733702743581952, 1435057323595040000, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c11_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨483686599979591269, 5, 0⟩) strips012_s0_c11 = true := by
  decide +kernel

theorem strips012_s0_c11_start : (⟨483686599979591269, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10) := rfl

def strips012_s0_c12 : List FECell := [
  ⟨⟨488190199606961765, 5, 0⟩, ⟨1273680776612370432, 1439954485327542784, 0, 0, 0, 0⟩⟩,
  ⟨⟨489090919532435864, 5, 0⟩, ⟨1278619534199983616, 1444843268894071552, 0, 0, 0, 0⟩⟩,
  ⟨⟨489991639457909964, 5, 0⟩, ⟨1283550001938846464, 1449723701466048000, 0, 0, 0, 0⟩⟩,
  ⟨⟨490892359383384063, 5, 0⟩, ⟨1288472206142431488, 1454595810090217728, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c12_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨487289479681487666, 5, 0⟩) strips012_s0_c12 = true := by
  decide +kernel

theorem strips012_s0_c12_start : (⟨487289479681487666, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11) := rfl

def strips012_s0_c13 : List FECell := [
  ⟨⟨491793079308858162, 5, 0⟩, ⟨1293386173005951488, 1459459621689391104, 0, 0, 0, 0⟩⟩,
  ⟨⟨492693799234332261, 5, 0⟩, ⟨1298291928607050752, 1464315163063179264, 0, 0, 0, 0⟩⟩,
  ⟨⟨493594519159806360, 5, 0⟩, ⟨1303189498906489344, 1469162460888724992, 0, 0, 0, 0⟩⟩,
  ⟨⟨494495239085280459, 5, 0⟩, ⟨1308078909748822784, 1474001541721426944, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c13_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨490892359383384063, 5, 0⟩) strips012_s0_c13 = true := by
  decide +kernel

theorem strips012_s0_c13_start : (⟨490892359383384063, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12) := rfl

def strips012_s0_c14 : List FECell := [
  ⟨⟨495395959010754558, 5, 0⟩, ⟨1312960186863076864, 1478832431995659264, 0, 0, 0, 0⟩⟩,
  ⟨⟨496296678936228657, 5, 0⟩, ⟨1317833355863417600, 1483655158025487104, 0, 0, 0, 0⟩⟩,
  ⟨⟨497197398861702757, 5, 0⟩, ⟨1322698442249817088, 1488469746005374208, 0, 0, 0, 0⟩⟩,
  ⟨⟨498998838712650955, 5, 0⟩, ⟨1326442056271453696, 1499358083114759936, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c14_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨494495239085280459, 5, 0⟩) strips012_s0_c14 = true := by
  decide +kernel

theorem strips012_s0_c14_start : (⟨494495239085280459, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13) := rfl

def strips012_s0_c15 : List FECell := [
  ⟨⟨500800278563599154, 5, 0⟩, ⟨1336127088697519616, 1508935185951393024, 0, 0, 0, 0⟩⟩,
  ⟨⟨502601718414547352, 5, 0⟩, ⟨1345780250083523328, 1518480198494196224, 0, 0, 0, 0⟩⟩,
  ⟨⟨504403158265495551, 5, 0⟩, ⟨1355401738882680320, 1527993324841198592, 0, 0, 0, 0⟩⟩,
  ⟨⟨506204598116443749, 5, 0⟩, ⟨1364991751801434112, 1537474767256408064, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c15_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨498998838712650955, 5, 0⟩) strips012_s0_c15 = true := by
  decide +kernel

theorem strips012_s0_c15_start : (⟨498998838712650955, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14) := rfl

def strips012_s0_c16 : List FECell := [
  ⟨⟨508006037967391948, 5, 0⟩, ⟨1374550483819367168, 1546924726191125760, 0, 0, 0, 0⟩⟩,
  ⟨⟨509807477818340146, 5, 0⟩, ⟨1384078128208834048, 1556343400304954880, 0, 0, 0, 0⟩⟩,
  ⟨⟨511608917669288345, 5, 0⟩, ⟨1393574876554318592, 1565730986486509824, 0, 0, 0, 0⟩⟩,
  ⟨⟨513410357520236543, 5, 0⟩, ⟨1403040918771520512, 1575087679873830656, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c16_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨506204598116443749, 5, 0⟩) strips012_s0_c16 = true := by
  decide +kernel

theorem strips012_s0_c16_start : (⟨506204598116443749, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15) := rfl

def strips012_s0_c17 : List FECell := [
  ⟨⟨515211797371184742, 5, 0⟩, ⟨1412476443126175488, 1584413673874508288, 0, 0, 0, 0⟩⟩,
  ⟨⟨517013237222132940, 5, 0⟩, ⟨1421881636252613376, 1593709160185525248, 0, 0, 0, 0⟩⟩,
  ⟨⟨518814677073081139, 5, 0⟩, ⟨1431256683172060160, 1602974328812814336, 0, 0, 0, 0⟩⟩,
  ⟨⟨520616116924029337, 5, 0⟩, ⟨1440601767310685440, 1612209368090545408, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c17_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨513410357520236543, 5, 0⟩) strips012_s0_c17 = true := by
  decide +kernel

theorem strips012_s0_c17_start : (⟨513410357520236543, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16) := rfl

def strips012_s0_c18 : List FECell := [
  ⟨⟨522417556774977535, 5, 0⟩, ⟨1449917070517401856, 1621414464700138752, 0, 0, 0, 0⟩⟩,
  ⟨⟨524218996625925733, 5, 0⟩, ⟨1459202773081419008, 1630589803689013760, 0, 0, 0, 0⟩⟩,
  ⟨⟨526020436476873932, 5, 0⟩, ⟨1468459053749557504, 1639735568489074688, 0, 0, 0, 0⟩⟩,
  ⟨⟨527821876327822130, 5, 0⟩, ⟨1477686089743324928, 1648851940934941696, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c18_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨520616116924029337, 5, 0⟩) strips012_s0_c18 = true := by
  decide +kernel

theorem strips012_s0_c18_start : (⟨520616116924029337, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17) := rfl

def strips012_s0_c19 : List FECell := [
  ⟨⟨529623316178770329, 5, 0⟩, ⟨1486884056775760128, 1657939101281925376, 0, 0, 0, 0⟩⟩,
  ⟨⟨531424756029718527, 5, 0⟩, ⟨1496053129068047616, 1666997228223755776, 0, 0, 0, 0⟩⟩,
  ⟨⟨533226195880666726, 5, 0⟩, ⟨1505193479365905920, 1676026498910063616, 0, 0, 0, 0⟩⟩,
  ⟨⟨535027635731614924, 5, 0⟩, ⟨1514305278955755008, 1685027088963623424, 0, 0, 0, 0⟩⟩]

set_option maxRecDepth 1000000 in
theorem strips012_s0_c19_ok : cellsCheck 22 (ln2Iv 22) (⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, []⟩ : FEStrip) (⟨527821876327822130, 5, 0⟩) strips012_s0_c19 = true := by
  decide +kernel

theorem strips012_s0_c19_start : (⟨527821876327822130, 5, 0⟩) = lastNode (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18) := rfl

end CKLaneA1.FEData


