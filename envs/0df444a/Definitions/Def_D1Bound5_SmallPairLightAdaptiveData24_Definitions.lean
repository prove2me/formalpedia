-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightAdaptiveData24_Definitions
-- name    : D1Bound5_SmallPairLightAdaptiveData24_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:42:36.604331+00:00
-- url     : https://prove2.me/theorems/05e2c9ca-0588-4ce3-8cab-3aba858e2f3c
-- title:
--   Small Pair Light Adaptive Data24
-- statement:
--   The selected sublists and row data used to assemble the finite selected-floor prefix certificates. The named objects in this bundle include `PairLightAdaptivePrepared24.leftCached000`, `PairLightAdaptivePrepared24.leftRows000`, `PairLightAdaptivePrepared24.leftCached001`, `PairLightAdaptivePrepared24.leftRows001`, `PairLightAdaptivePrepared24.leftCached002`, `PairLightAdaptivePrepared24.leftRows002`, `PairLightAdaptivePrepared24.leftCached003`, `PairLightAdaptivePrepared24.leftRows003` and 8 further declarations.
-- source:
--   D1Bound5/SmallPairLightAdaptiveData24.lean, lines 8-8, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 9-9, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 11-11, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 12-12, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 14-14, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 15-15, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 17-17, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 18-18, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 20-20, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 21-21, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 23-23, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 24-24, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 26-26, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 27-27, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 29-29, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3; D1Bound5/SmallPairLightAdaptiveData24.lean, lines 30-30, SHA-256 ca816ecaf31d9f037cd58840a21fec94aceef203d51ea1a171592acc2ccecad3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def leftCached000 : List PairLightCachedVertex := PairLightPrepared24.leftCached
def leftRows000 : List (Nat × List Nat) := PairLightPrepared24.leftRows

def leftCached001 : List PairLightCachedVertex := leftCached000.drop 101
def leftRows001 : List (Nat × List Nat) := leftRows000.drop 101

def leftCached002 : List PairLightCachedVertex := leftCached001.drop 147
def leftRows002 : List (Nat × List Nat) := leftRows001.drop 147

def leftCached003 : List PairLightCachedVertex := leftCached002.drop 198
def leftRows003 : List (Nat × List Nat) := leftRows002.drop 198

def rightCached000 : List PairLightCachedVertex := PairLightPrepared24.rightCached
def rightRows000 : List (Nat × List Nat) := PairLightPrepared24.rightRows

def rightCached001 : List PairLightCachedVertex := rightCached000.drop 101
def rightRows001 : List (Nat × List Nat) := rightRows000.drop 101

def rightCached002 : List PairLightCachedVertex := rightCached001.drop 147
def rightRows002 : List (Nat × List Nat) := rightRows001.drop 147

def rightCached003 : List PairLightCachedVertex := rightCached002.drop 198
def rightRows003 : List (Nat × List Nat) := rightRows002.drop 198


end D1Bound5.PairLightAdaptivePrepared24
end


