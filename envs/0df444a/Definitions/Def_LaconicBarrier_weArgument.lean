-- Prove2me | Definitions.Def_LaconicBarrier_weArgument
-- name    : LaconicBarrier_weArgument
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:10.957012+00:00
-- url     : https://prove2.me/theorems/ed245ee7-203e-4a95-872a-e332b7fcf225
-- title:
--   The two-message laconic argument from witness encryption
-- statement:
--   From a witness encryption scheme $(\mathrm{Enc}, \mathrm{Dec})$: on common input $x$ the verifier samples $\mu \leftarrow \{0,1\}$, sends $ct \leftarrow \mathrm{Enc}(1^\lambda, x, \mu)$ and keeps $vk = \mu$; given a witness $w$, the prover returns $\pi = \mathrm{Dec}(ct, w)$, read as one bit; the verifier accepts if $\pi = \mu$.
--
--   **Formalization Note** The prover's output $1$ stays $1$; every other output ($0$ or $\bot$) is sent as $0$, so the prover always sends exactly one bit.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §7.1, p.45

import Mathlib
import Definitions.Def_LaconicBarrier_WEScheme
import Definitions.Def_LaconicBarrier_LaconicArg

namespace LaconicBarrier

/-- A prover message read as one bit: `[1]` stays `[1]`; every other string (`[0]` or the failure
symbol `⊥`) becomes `[0]`. -/
def bitOf (o : List Bool) : List Bool := if o = [true] then [true] else [false]

/-- The **two-message laconic argument from witness encryption** (Jain, Mathialagan, Roy, STOC 2027
submission (manuscript sha256 1af78662…), §7.1, p.45: "On common input `x`, the verifier samples
`µ ← {0, 1}`, sends `ct ← Enc(1^λ, x, µ)`, and keeps `µ` private. Given a witness `w`, the prover
returns `π = Dec(ct, w)`, and the verifier accepts if `π = µ`"). The first coin of `V₁` is `µ`, the
others are `Enc`'s; `vk = [µ]`; the prover's output is read as one bit (`bitOf`). -/
def weArgument (E : WEScheme) : LaconicArg where
  vcoins lam x := E.ecoins lam x + 1
  V1 lam x ρ := (E.Enc lam x (ρ 0) (fun i => ρ i.succ), [ρ 0])
  pcoins pk _ w := E.dcoins pk w
  P pk _ w ρ := bitOf (E.Dec pk w ρ)
  V2 vk _ π := decide (π = vk)

end LaconicBarrier


