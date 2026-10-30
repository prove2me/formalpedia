-- Prove2me | Definitions.Def_PermBlockchain_Transfers_revealed
-- name    : PermBlockchain_Transfers_revealed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:48:47.477099+00:00
-- url     : https://prove2.me/theorems/e3c0261b-fb5c-41d8-aa8f-b1869e628193
-- title:
--   What the blockchain reveals to a consumer
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   With the blockchain, "for each manufacturer $i$ on the blockchain, the signal observed by any consumer reveals the manufacturer's type exactly"; with transfers, a consumer sees this information only if she pays the access fee ($b_k=1$): $\mathbb P^{b_k}(\tilde q_{ik}=q_i\mid q_i,a_i)=\alpha+(1-\alpha)a_ib_k$. The revelation to a consumer with access decision $b$ at history $x$, under true assignment $\theta$, is
--   $$r_j=\begin{cases}\theta(j)&\text{if }b=1\text{ and }a_j=1,\\\text{nothing}&\text{otherwise.}\end{cases}$$
--
--   **Formalization Note** The main text takes $\alpha=1/2$ (p. 9): a signal not backed by the blockchain is then uninformative, so signals are encoded by this deterministic revelation.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.2, p. 12 (PDF p. 13); §4.2, p. 21 (PDF p. 22); α = 1/2, p. 9 (PDF p. 10)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_MType
import Definitions.Def_PermBlockchain_Transfers_Hist

namespace PermBlockchain.Transfers

/-- **What the blockchain reveals to a consumer with access decision `b`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.2, p. 12 (PDF p. 13): "for each manufacturer i on the blockchain, the signal observed
by any consumer k ∈ [0, 1] reveals the manufacturer's type exactly"; §4.2, p. 21 (PDF p. 22):
"P^{b_k}(q̃_ik = q_i | q_i, a_i) = α + (1 − α)a_i b_k = P^{b_k}(ξ̃_ik = ξ_i | ξ_i, a_i)".

`revealed b θ x j` is `some (θ j)` if the consumer paid for access (`b = true`) and manufacturer
`j` adopted in the history `x`, and `none` otherwise.

**Formalization Note.** The main text sets `α = 1/2` ("we restrict ourselves to α = 1/2 within
the main text of the paper", p. 9): a signal not backed by the blockchain is then uninformative,
and a signal backed by it is exact, so signals are encoded by this deterministic revelation. -/
def revealed {m : ℕ} (b : Bool) (θ : Mfr m → MType) (x : Hist m) : Mfr m → Option MType :=
  fun j => if (b && x.1 j) = true then some (θ j) else none

end PermBlockchain.Transfers


