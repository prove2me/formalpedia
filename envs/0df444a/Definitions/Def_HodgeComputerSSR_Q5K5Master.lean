-- Prove2me | Definitions.Def_HodgeComputerSSR_Q5K5Master
-- name    : HodgeComputerSSR_Q5K5Master
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T22:10:26.903807+00:00
-- url     : https://prove2.me/theorems/b4f9c028-fba5-4a9b-a85f-fc71587765b6
-- title:
--   $K_5$ master cache `cacheK`, `Q5_pol_K5`/`Q7_pol_K5`, and rational weights `W_K5`/`W_K5_scaled`
-- statement:
--   Defines `Q5_pol_K5`, `Q7_pol_K5`, `W_K5`, `W_K5_scaled`, and `cacheK = evalSQCache k5Ops S_K Q_K` over $K_5$ without importing `CoverParams` or `SheetCalculus`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueQ5Alg.lean#L179-L756

import Definitions.Def_HodgeComputerSSR_Q5K5Geom
import Definitions.Def_HodgeComputerSSR_Q5Master
import Definitions.Def_HodgeComputerSSR_RQ5Data

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.Q5WeightsData
  SymmetricSexticResidual.LocalResidueData SymmetricSexticResidual.LocalResidueU0
  Polynomial
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len
open scoped BigOperators

def Q5_pol_K5 : K5[X] :=
  ∑ j : Fin 6, Polynomial.C (evalSQ_K5 (Q5_c j)) * Polynomial.X ^ j.val

def Q7_pol_K5 : K5[X] :=
  ∑ j : Fin 8, Polynomial.C (evalSQ_K5 (Q7_c j)) * Polynomial.X ^ j.val

def W_K5 (k : Fin 13) : K5 :=
  evalSQ_K5 (W_num_expr k) / ((D_int_all : K5) * evalSQ_K5 D_all_expr)

-- Scaled Q5 weight for `k5Params.Q5_z`, `k5Params.Q7_z`
def W_K5_scaled (k : Fin 13) : K5 :=
  ((sc5_den * sc7_den : ℤ) : K5) / ((sc5_num * sc7_num : ℤ) : K5) * W_K5 k


def cacheK : SQCache K5 := evalSQCache k5Ops S_K Q_K

end SymmetricSexticResidual.LocalResidueQ5


