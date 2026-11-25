-- Prove2me | Definitions.Def_DetDLP_D3StoppedRaw
-- name    : DetDLP_D3StoppedRaw
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:44:23.525473+00:00
-- url     : https://prove2.me/theorems/fdb2a89f-c0d5-44bb-a2e1-f25dbe4aebf9
-- title:
--   Raw generator for the stopped schedule
-- statement:
--   A computable parser for BTN instance encodings that reads the starting depth, edge count, scale, and polynomial coefficient word, then writes the corresponding stopped-schedule encoding.

import Definitions.Def_DetDLP_D3StoppedSchedule
import Definitions.Def_DetDLP_W1_Queries

set_option autoImplicit false
namespace DetDLP.D3Stopped
open AppendixD4 Polynomial Groundwork.PolyT OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Encode the starting depth, polynomial coefficients, and an auxiliary payload. -/
def descOf (d₀ : ℕ) (f : ℤ[X]) (payload : Bits) : Bits :=
  Encoding.encodeList id [countWord d₀, polynomialBits f, payload]

def scheduleWords (C S M d₀ : ℕ) (fBits : Bits) : Bits :=
  let s := schedule C S M d₀
  Encoding.encodeList id [encodeNatListBin [s.H, s.start, s.D, s.cap, s.κ],
    encodeNatListBin (List.ofFn s.u), encodeNatListBin (List.ofFn s.a), fBits]

/-- Read the stopped-schedule parameters directly from their framed BTN input fields.
The polynomial coefficient word is copied from the descriptor without decoding it. -/
def scheduleRaw (C : ℕ) (inp : Bits) : Bits :=
  let desc := DetDLP_W1_Queries.first inp
  let graph := DetDLP_W1_Queries.second inp
  let S := bval (DetDLP_W1_Queries.third inp)
  let d₀ := bval (DetDLP_W1_Queries.first desc)
  let M := bval (DetDLP_W1_Queries.second graph)
  scheduleWords C S M d₀ (DetDLP_W1_Queries.second desc)

end DetDLP.D3Stopped

namespace DetDLP.D3Stopped
open AppendixD4 Groundwork Polynomial OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem scheduleRaw_spec (C d₀ S P l : ℕ) (payload : Bits) (G : Graph) (f : ℤ[X]) :
    scheduleRaw C (DetDLP.encodeBTNInstance (descOf d₀ f payload) G S P l) =
      (schedule C S G.nE d₀).bits f := by
  simp only [scheduleRaw, descOf, encodeBTNInstance, BipartiteMultigraph.encode,
    DetDLP_W1_Queries.third, DetDLP_W1_Queries.second, DetDLP_W1_Queries.first_cons,
    DetDLP_W1_Queries.more_cons, id_eq, DetDLP_W1_Queries.decode_count]
  rfl

end DetDLP.D3Stopped


