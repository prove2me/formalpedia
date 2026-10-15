-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighBinningMerge
-- name    : TaoFivePrimes_RHHighBinningMerge
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T04:11:37.296063+00:00
-- url     : https://prove2.me/theorems/86e28975-6b99-4dad-ae5d-3f5cc6c57bc8
-- title:
--   Exact consecutive-bin coefficient merging
-- statement:
--   Transparent list algorithm that combines consecutive equal frequency-bin indices by componentwise addition of coefficient lists. No sortedness, correctness, analytic approximation, sign, count or RH statement is asserted.
-- source:
--   Platt DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
set_option autoImplicit false
namespace RHHighBinningMerge
open RHHighDirichletBinning
noncomputable def auxiliary : Nat→List (Int×Int)→List (Nat×List (Int×Int))→List (Nat×List (Int×Int))
  | j,acc,[] => [(j,acc)]
  | j,acc,(m,a)::gs => if m=j then auxiliary j (add acc a) gs
      else (j,acc)::auxiliary m a gs
noncomputable def merge : List (Nat×List (Int×Int))→List (Nat×List (Int×Int))
  | [] => []
  | (j,a)::gs => auxiliary j a gs
end RHHighBinningMerge
noncomputable def TaoFivePrimes_RHHighBinningMerge : Nat := 24


