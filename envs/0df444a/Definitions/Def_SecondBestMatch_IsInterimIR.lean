-- Prove2me | Definitions.Def_SecondBestMatch_IsInterimIR
-- name    : SecondBestMatch_IsInterimIR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:42.657825+00:00
-- url     : https://prove2.me/theorems/1b9d5991-46e1-4f65-9b5e-aea77a6db4fa
-- title:
--   Interim individual rationality
-- statement:
--   A mechanism is **interim individually rational** if $u_i(v;v)\ge 0$ and $u_j(c;c)\ge 0$ for every buyer $i$, seller $j$ and every type $v, c\in[0,1]$, where $u_i(v;v) = v\,x_i(v)-p_i(v)$ and $u_j(c;c) = r_j(c) - c\,y_j(c)$.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Definition 2.1, p.8

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_interimBuyerService
import Definitions.Def_SecondBestMatch_interimSellerService
import Definitions.Def_SecondBestMatch_interimPay
import Definitions.Def_SecondBestMatch_interimRecv

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- Interim individual rationality (Definition 2.1, Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), p.8): `uᵢ(v; v) ≥ 0` and
`uⱼ(c; c) ≥ 0` for every buyer `i`, seller `j` and every type in `[0, 1]`. -/
def IsInterimIR {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (A : Mechanism B S) : Prop :=
  (∀ i, ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ v * interimBuyerService m A.alloc i v - interimPay m A i v) ∧
  (∀ j, ∀ c ∈ Icc (0 : ℝ) 1, 0 ≤ interimRecv m A j c - c * interimSellerService m A.alloc j c)

end SecondBestMatch


