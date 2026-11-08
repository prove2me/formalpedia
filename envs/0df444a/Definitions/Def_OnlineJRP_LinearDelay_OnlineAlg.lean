-- Prove2me | Definitions.Def_OnlineJRP_LinearDelay_OnlineAlg
-- name    : OnlineJRP_LinearDelay_OnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:20.60368+00:00
-- url     : https://prove2.me/theorems/fdd1371c-7486-418c-a186-859002987739
-- title:
--   Deterministic online algorithms for joint replenishment (causal maps from request lists to purchase lists)
-- statement:
--   A **deterministic online algorithm** maps a request sequence to a list of purchases in such a way that its decisions up to time $T$ depend only on the requests released by time $T$: if two instances have the same requests with $t_r\le T$, the purchases made at times $\le T$ coincide.
--
--   This is the meaning of "request $r$ is revealed at time $t_r$" for a map defined on whole inputs. It is the condition that gives the competitive ratio its content: without it, the offline optimum would achieve ratio $1$.
--
--   **Formalization Note** The condition is imposed for instances agreeing as lists on the requests with $t_r\le T$, and it compares lists of purchases, so it fixes their order too.
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Sec. 1, p. 1 (the online setting)

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_OPT

namespace OnlineJRP.LinearDelay

/-- A deterministic online algorithm for online JRP (Sec. 1, p. 1: "In the online setting, request
`r` is revealed at time `t_r`").

**Formalization Note** Deterministic: `run` is a function of the input. Online (`causal`): on two
instances with the same requests released by time `T`, the purchases made at times `≤ T` coincide,
in the same order. Without this condition the offline optimum would be a witness with ratio `1`. -/
structure OnlineAlg (n : ℕ) where
  /-- The purchases made on an input. -/
  run : List (Req n) → List (Purchase n)
  causal : ∀ (σ σ' : List (Req n)) (T : ℝ), IsInstance σ → IsInstance σ' →
    σ.filter (fun r => r.t ≤ T) = σ'.filter (fun r => r.t ≤ T) →
    (run σ).filter (fun p => p.time ≤ T) = (run σ').filter (fun p => p.time ≤ T)

end OnlineJRP.LinearDelay


