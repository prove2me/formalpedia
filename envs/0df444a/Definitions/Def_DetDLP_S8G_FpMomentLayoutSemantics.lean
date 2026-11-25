-- Prove2me | Definitions.Def_DetDLP_S8G_FpMomentLayoutSemantics
-- name    : DetDLP_S8G_FpMomentLayoutSemantics
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T01:42:40.205872+00:00
-- url     : https://prove2.me/theorems/8de3b010-c831-475d-b874-2a8cc709b4ec
-- title:
--   DetDLP DetDLP_S8G_FpMomentLayoutSemantics
-- statement:
--   Layout semantics for DetDLP Stage I.
-- source:
--   DetDLP m8

import Definitions.Def_DetDLP_S8G_FpMomentGraph
import Definitions.Def_DetDLP_S8C_TagSpec
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

open S8C
open S8G.FpMoment

/-- Witness/count/budget packaging for `FpMoment.ofLayout`. -/
structure FpMomentLayoutSemantics (p : ℕ) [Fact p.Prime] (j : Fin 4) (T : ℕ) (η : List Bool) where
  A : w3_FactorLayout
  test : w3_factorTest A
  hg : Function.Surjective A.gate
  W : Type
  instW : Fintype W
  witness :
    {b : Fin A.nb → Bool // ∀ g, test g (fun e => b (A.bit e.1)) = true} ≃ W
  count : Fintype.card W = value p (blockCount (bitLen p)) T η j
  edges : 2 * A.ne < scale (blockCount (bitLen p)) (bitLen p)
  degree :
    ∀ v, (w3_factorGraph A).deg v ≤ max 12 (Nat.ceil (136 * ((bitLen p : ℝ) + 2) ^ ((3 : ℝ) / 4)))

end DetDLP


