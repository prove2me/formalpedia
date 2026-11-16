-- Prove2me | Definitions.Def_QiOPoQ_Supplement_fig4Challenge
-- name    : QiOPoQ_Supplement_fig4Challenge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:46:13.364121+00:00
-- url     : https://prove2.me/theorems/d327147e-0bdb-4733-99e9-8df1f79fc1b1
-- title:
--   Figure 4: the challenge of the privately verifiable proof of quantumness
-- statement:
--   The challenger of Figure 4. On coins $r$ it reads independent uniform bits $b_1,\dots,b_t$ and then random tapes $r_1,\dots,r_t$, and outputs
--
--   $$\mathsf{chall}=(\hat C_1,\dots,\hat C_t),\qquad \hat C_i:=\mathrm{qiO}(1^\lambda,C_{b_i,\lambda};r_i).$$
--
--   **Formalization Note** The coin layout is that of the published Figure 6 challenge without the image $y$: the bits are the first $t(\lambda)$ coins and tape $r_i$ is the $i$-th block of `fig6Block` coins after them; the challenge is the tuple code of the $t$ descriptions.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Figure 4, p.17

import Mathlib
import Definitions.Def_QiOPoQ_fig6Challenge

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity QAdvFew.PoQOracle

variable {G : GateSet}

/-- **Figure 4, Challenge.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and
Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Figure 4, p.17:
"Challenge(1^λ; r): Parse r as independent uniform bits b_1, . . . , b_t followed by random tapes
r_1, . . . , r_t ∈ {0, 1}^{poly(λ)}. For all i ∈ [t], compute Ĉ_i := qiO(1^λ, C_{b_i,λ}; r_i).
Output chall = (Ĉ_1, . . . , Ĉ_t)."

**Formalization Note.** The layout is that of the published Figure 6 challenge
(`QiOPoQ.fig6Challenge`) without the image `y`: `b` is the first `t(λ)` bits of `r`; tape `r_i`
is the `i`-th block of `fig6Block` bits after them (the obfuscator reads the prefix it needs);
positions are `0`-based; the challenge is `tup [Ĉ_1, …, Ĉ_t]`. -/
def fig4Challenge (Obf : UPPT) (Cb : Bool → ℕ → Circ G) (t : ℕ → ℕ) (n : ℕ) (r : Str) : Str :=
  tup (List.ofFn fun i : Fin (t n) =>
    Obf.runWith (obfIn Cb ((r.take (t n)).getD i.val false) n)
      ((r.drop (t n + i.val * fig6Block Obf Cb n)).take (fig6Block Obf Cb n)))

end QiOPoQ.Supplement


