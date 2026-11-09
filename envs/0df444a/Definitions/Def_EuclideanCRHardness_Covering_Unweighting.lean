-- Prove2me | Definitions.Def_EuclideanCRHardness_Covering_Unweighting
-- name    : EuclideanCRHardness_Covering_Unweighting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:20:39.571658+00:00
-- url     : https://prove2.me/theorems/bbb3a41f-ad16-465b-8067-5fb776c5d100
-- title:
--   Deterministic floor-copy unweighting
-- statement:
--   For $K$ weighted equations set $L=128K$ and replace equation $i$ by $\lfloor Lw_i\rfloor$ copies. The resulting unweighted list is constructed from the actual weights, with the original variable indices unchanged.
--
--   The bit map first parses and checks a normalized nonnegative weighted instance. It emits the encoded copy list on valid inputs and the empty bit string otherwise. This check prevents invalid large weights from causing an exponential output; polynomial runtime on all bit strings remains a theorem conclusion.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), Lemma 3.3 and its proof, printed p. 5 / PDF p. 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf

import Definitions.Def_EuclideanCRHardness_Covering_Parity

namespace EuclideanCRHardness.Covering

def multiplicity (P : WeightedParity) (w : ℚ) : ℕ := ⌊(128 * P.eqs.length : ℕ) * w⌋₊
def unweight (P : WeightedParity) : ParityInstance :=
  ⟨P.n, P.eqs.flatMap (fun e => List.replicate (multiplicity P e.2) e.1)⟩
def weightedValidCheck (P : WeightedParity) : Bool :=
  !P.eqs.isEmpty && (P.eqs.all (fun e =>
    e.1.a < P.n && e.1.b < P.n && e.1.d < P.n && 0 ≤ e.2)) &&
    ((P.eqs.map Prod.snd).sum == 1)
def unweightBits (bits : List Bool) : List Bool :=
  match decodeWeighted bits with
  | none => []
  | some P => if weightedValidCheck P then encodeParity (unweight P) else []

end EuclideanCRHardness.Covering


