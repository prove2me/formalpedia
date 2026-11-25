-- Prove2me | Definitions.Def_DetDLP_S8M_ECPairLayoutSemantics
-- name    : DetDLP_S8M_ECPairLayoutSemantics
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T01:43:51.360377+00:00
-- url     : https://prove2.me/theorems/ecafa003-02dc-4fab-827d-a49ac34172ad
-- title:
--   DetDLP DetDLP_S8M_ECPairLayoutSemantics
-- statement:
--   Layout semantics for DetDLP Stage I.
-- source:
--   DetDLP m8

import Definitions.Def_DetDLP_S8M_ECPairGraph
import Definitions.Def_DetDLP_S8C_TagSpec
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP.S8M.ECPair

open DetDLP.S8C

/-- Witness/count/budget packaging for `ECPair.ofLayout`. -/
structure ECPairLayoutSemantics (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point) (η : List Bool) where
  A : w3_FactorLayout
  test : w3_factorTest A
  hg : Function.Surjective A.gate
  W : Type
  instW : Fintype W
  witness :
    {b : Fin A.nb → Bool // ∀ g, test g (fun e => b (A.bit e.1)) = true} ≃ W
  count : Fintype.card W = value E T S X η
  edges : 2 * A.ne < scale (blockCount (bitLen p)) (bitLen p)
  degree :
    ∀ v, (w3_factorGraph A).deg v ≤ max 12 (Nat.ceil (136 * ((bitLen p : ℝ) + 2) ^ ((3 : ℝ) / 4)))

end DetDLP.S8M.ECPair


