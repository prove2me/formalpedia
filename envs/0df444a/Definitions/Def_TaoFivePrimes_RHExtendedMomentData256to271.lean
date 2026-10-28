-- Prove2me | Definitions.Def_TaoFivePrimes_RHExtendedMomentData256to271
-- name    : TaoFivePrimes_RHExtendedMomentData256to271
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:10:57.166881+00:00
-- url     : https://prove2.me/theorems/831d6be8-5f4e-40ac-9f63-f4fcc886647c
-- title:
--   Proposed scaled moments 256 through 271
-- statement:
--   This list contains sixteen proposed integer numerators $C_j$ indexed by $256\le j\le271$, each intended to represent a rational value with denominator $10^{64}$.
--
--   $$
--   C_{256},C_{257},\ldots,C_{271}.
--   $$
--
--   The entries are candidate data. Their relationship to the rational Mellin rule and to the true moments requires separate proof.
-- source:
--   Derived here from the exact theta-jet and Mellin quadrature framework of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham.

/- Proposed rounded Mellin moment numerators at indices 256--271.
The original theta-jet data are by sometik179; theta/Mellin foundations by
Gabewhigham. The integers are data only until independently certified. -/
import Mathlib.Data.Int.Basic
set_option autoImplicit false
@[noinline] def TaoFivePrimes_RHExtendedMomentData256to271 : List ℤ := [
  13015295653558874600194157113437569209871972075796599135223,
  2869729332451693515763601730951318875272446495548307654246,
  628870068591354499900042533737723291937946379244446711679,
  136969499441880753363186057628169562251462137997188621805,
  29651014797860799394749694748716919452071216175356212316,
  6379956588942096677331585657450607446429190266715191284,
  1364482603096423289073770385263208262044016972068378834,
  290068103658318677353131222664740679281255494468739467,
  61294731680544869889371934560742498738504248312074226,
  12874991666920937867657060821041451650256909773712437,
  2688318793011416067552782333355461494465083286854017,
  557999592034206295031974569338528587574472746227475,
  115137164059106731784976033466153655405954961496695,
  23617551600045761497188566999714233797750776972651,
  4816161195316505658320492980648008704843830544194,
  976389241216327964920085095917608446908937598938
]


