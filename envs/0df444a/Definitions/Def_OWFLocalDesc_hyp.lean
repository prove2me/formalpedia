-- Prove2me | Definitions.Def_OWFLocalDesc_hyp
-- name    : OWFLocalDesc_hyp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:31.237542+00:00
-- url     : https://prove2.me/theorems/24eb8535-f8a8-41c7-ad6d-762b918b0443
-- title:
--   The hypothesis of a certificate on a public tape (Definition 2.5)
-- statement:
--   Fix a public tape $w\in\{0,1\}^t$. The **hypothesis** of a certificate with program $\beta$ and anchor list $L_A$ answers a query $z\in\{0,1\}^n$ by running $U(\beta,L_A,w,z)$ for at most $t$ steps. If the run halts within $t$ steps and its first output symbol is a bit, the hypothesis returns that bit; otherwise (timeout, no output, or a first output symbol that is not a bit) it returns $0$.
--
--   The hypothesis receives only $L_A$, $w$, $z$ and $\beta$: neither the other sample points, nor their indices, nor the sample size.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.5, p.12

import Mathlib
import Definitions.Def_OWFLocalDesc_Decoder
set_option autoImplicit false

namespace OWFLocalDesc

/-- **The hypothesis of a certificate.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Definition 2.5, p.12:
"Fix a public tape w ∈ {0,1}^t. The hypothesis of the certificate answers a query z ∈ {0,1}^n by
running U(β, L_A, w, z) for at most t steps. If the run halts within t steps and its first output
symbol is a bit, the hypothesis returns that bit; otherwise it returns zero."

`hyp U β L w z t` is the bit returned on query `z` by the program `β` with anchor list `L` on
the tape `w` at clock `t`; `false` is the bit `0`. It receives no sample size and no index. -/
def hyp (U : Decoder) (β L w z : List Bool) (t : ℕ) : Bool :=
  match U.run β L w z t with
  | some (some b) => b
  | _ => false

end OWFLocalDesc


