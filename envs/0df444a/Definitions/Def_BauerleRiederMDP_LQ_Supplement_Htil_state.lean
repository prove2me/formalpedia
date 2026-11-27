-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil_state
-- name    : BauerleRiederMDP_LQ_Supplement_Htil_state
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:56:25.502799+00:00
-- url     : https://prove2.me/theorems/3e5d7ef7-13ea-5d40-9d80-449716d261ea
-- title:
--   The current observable state $x_n$ of a history $\tilde{h}_n = (x_0, a_0, z_1, \dots , z_n, x_n) \in  \tilde{H}_n$
--   (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (201
-- statement:
--   The current observable state $x_n$ of a history $\tilde{h}_n = (x_0, a_0, z_1, \dots , z_n, x_n) \in  \tilde{H}_n$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §5.2, p.154, PDF 167).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §5.2, p.154, PDF 167

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil

namespace BauerleRiederMDP.LQ.Supplement

universe u

/-- The current observable state `x_n` of a history `h̃_n = (x_0, a_0, z_1, …, z_n, x_n) ∈ H̃_n`
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §5.2, p.154,
PDF 167). -/
def Htil.state {EX A Z : Type u} : (n : ℕ) → Htil EX A Z n → EX
  | 0, x => x
  | _ + 1, (_, _, _, x) => x

end BauerleRiederMDP.LQ.Supplement


