-- Prove2me | Definitions.Def_QiOPoQ_fig6Challenge
-- name    : QiOPoQ_fig6Challenge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:20.156441+00:00
-- url     : https://prove2.me/theorems/378610ac-547d-48c4-9560-a08dcae2f140
-- title:
--   Figure 6: Challenge
-- statement:
--   On coins $r$, $\mathrm{Challenge}(1^\lambda;r)$ parses $r$ as $b=(b_1,\dots,b_t)\in\{0,1\}^t$ followed by random tapes $r_1,\dots,r_t$, computes $\hat C_i:=\mathrm{qiO}(1^\lambda,C_{b_i,\lambda};r_i)$ for $i\in[t]$ and $y=f(b)$, and outputs
--
--   $$
--   \mathsf{chall}=(\hat C_1,\dots,\hat C_t,y).
--   $$
--
--   **Formalization Note** The paper's tapes have length $\mathrm{poly}(\lambda)$. Each tape here has the length of the larger of Obf's coin counts on the inputs $(1^\lambda,C_{0,\lambda})$ and $(1^\lambda,C_{1,\lambda})$; Obf reads the prefix it needs, and surplus coins are ignored. A coin polynomial $\ell$ is *adequate* when $\ell(\lambda)\ge t+t\cdot|r_i|$, and Definition 3.3's $\ell$ is any such polynomial.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Figure 6, p.21

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_UPPT

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity QAdvFew.PoQOracle

variable {G : GateSet}

/-- The obfuscator's input for `C_{b,λ}`: `(1^λ, C_{b,λ})`. -/
def obfIn (Cb : Bool → ℕ → Circ G) (b : Bool) (n : ℕ) : Str := pair (unary n) (encCirc (Cb b n))

/-- The length of each random tape `r_i` of Figure 6: the larger of the obfuscator's coin counts
on `(1^λ, C_{0,λ})` and `(1^λ, C_{1,λ})`. -/
def fig6Block (Obf : UPPT) (Cb : Bool → ℕ → Circ G) (n : ℕ) : ℕ :=
  max (Obf.coins.eval (obfIn Cb false n).length) (Obf.coins.eval (obfIn Cb true n).length)

/-- The coin polynomial `ℓ` of Figure 6 is adequate when `ℓ(λ) ≥ t + t·|r_i|`: room for the bits
`b_1, …, b_t` and the `t` random tapes. -/
def AdequateCoins (Obf : UPPT) (Cb : Bool → ℕ → Circ G) (t : ℕ → ℕ) (ℓ : Polynomial ℕ) : Prop :=
  ∀ n, t n + t n * fig6Block Obf Cb n ≤ ℓ.eval n

/-- **Figure 6, Challenge.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and
Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Figure 6,
p.21: "Challenge(1^λ; r): Parse r as b := (b_1, . . . , b_t) ∈ {0, 1}^t followed by random tapes
r_1, . . . , r_t ∈ {0, 1}^{poly(λ)}. For all i ∈ [t], compute Ĉ_i := qiO(1^λ, C_{b_i,λ}; r_i)
(i ∈ [t]). Compute y = f(b) and output chall = (Ĉ_1, . . . , Ĉ_t, y)."

**Formalization Note.** `b` is the first `t(λ)` bits of `r`; tape `r_i` is the `i`-th block of
`fig6Block` bits after them, of which the obfuscator reads the prefix it needs (surplus coins are
ignored); positions are `0`-based (`Ĉ_{i+1}` is entry `i`). `f := f_t` is `f` on the `t`-bit
string `b`. The challenge is `tup [Ĉ_1, …, Ĉ_t, y]`. -/
def fig6Challenge (Obf : UPPT) (Cb : Bool → ℕ → Circ G) (f : Str → Str) (t : ℕ → ℕ) (n : ℕ)
    (r : Str) : Str :=
  tup (List.ofFn (fun i : Fin (t n) =>
      Obf.runWith (obfIn Cb ((r.take (t n)).getD i.val false) n)
        ((r.drop (t n + i.val * fig6Block Obf Cb n)).take (fig6Block Obf Cb n))) ++
    [f (r.take (t n))])

end QiOPoQ


