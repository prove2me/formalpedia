-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
-- name    : Submission_Weighted_Global_TernaryArenaLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:21:53.854124+00:00
-- url     : https://prove2.me/theorems/a072f022-a949-4ead-b40d-ec9ba8ed69f0
-- title:
--   Ternary Arena Layout
-- statement:
--   Definitions and structural lemmas for Ternary Arena Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaLayout.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountHost
set_option autoImplicit false
namespace ThreeSum.WeightedGlobalArenaLayout
def addr (free capacity slot : ℕ) : ℕ :=free+slot*capacity
def slots : ℕ :=67
def finish (free capacity : ℕ) : ℕ :=addr free capacity slots
def capacity (D E U : ℕ) : ℕ :=256*(D+1)*(U+1)^E
namespace Slot
abbrev hostTemplate : ℕ :=0
abbrev host : ℕ :=1
abbrev seedTemplate : ℕ :=2
abbrev seed : ℕ :=3
abbrev oldB : ℕ :=4
abbrev oldC : ℕ :=5
abbrev oldO : ℕ :=6
abbrev oldSpan : ℕ :=7
abbrev newSpan : ℕ :=8
abbrev flags : ℕ :=9
abbrev scoreB : ℕ :=10
abbrev scoreC : ℕ :=11
abbrev scorePaired : ℕ :=12
abbrev bank : ℕ :=13
abbrev oldPowers : ℕ :=14
abbrev prefixHeader : ℕ :=15
abbrev newB : ℕ :=16
abbrev newC : ℕ :=17
abbrev newO : ℕ :=18
abbrev wanted : ℕ :=19
abbrev wantedWork : ℕ :=20
abbrev hashWork : ℕ :=21
abbrev histogram : ℕ :=22
abbrev tensor : ℕ :=23
abbrev quadScratch : ℕ :=24
abbrev quadPowers : ℕ :=25
abbrev potentialColumns : ℕ :=26
abbrev potentialPowers : ℕ :=27
abbrev leftWeights : ℕ :=28
abbrev rightWeights : ℕ :=29
abbrev leftNative : ℕ :=30
abbrev leftNativeRadix : ℕ :=31
abbrev leftWord : ℕ :=32
abbrev leftWordRadix : ℕ :=33
abbrev leftMap : ℕ :=34
abbrev leftMapRadix : ℕ :=35
abbrev leftJoin : ℕ :=36
abbrev leftKeys : ℕ :=37
abbrev leftHistogram : ℕ :=38
abbrev rightNative : ℕ :=39
abbrev rightNativeRadix : ℕ :=40
abbrev rightWord : ℕ :=41
abbrev rightWordRadix : ℕ :=42
abbrev rightMap : ℕ :=43
abbrev rightMapRadix : ℕ :=44
abbrev rightJoin : ℕ :=45
abbrev rightKeys : ℕ :=46
abbrev rightHistogram : ℕ :=47
abbrev metadata : ℕ :=48
abbrev bankPowers : ℕ :=49
abbrev fbank : ℕ :=50
abbrev gbank : ℕ :=51
abbrev hbank : ℕ :=52
abbrev countOutput : ℕ :=53
abbrev near : ℕ :=54
abbrev caps : ℕ :=55
abbrev active : ℕ :=56
abbrev nearPowers : ℕ :=57
abbrev fws : ℕ :=58
abbrev frank : ℕ :=59
abbrev fvals : ℕ :=60
abbrev fdivision : ℕ :=61
abbrev gws : ℕ :=62
abbrev grank : ℕ :=63
abbrev gvals : ℕ :=64
abbrev gdivision : ℕ :=65
abbrev out : ℕ :=66
end Slot
end ThreeSum.WeightedGlobalArenaLayout


