-- Prove2me | Definitions.Def_QiOPoQ_Supplement_cvqcBlock
-- name    : QiOPoQ_Supplement_cvqcBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:51:56.160131+00:00
-- url     : https://prove2.me/theorems/2d6ca233-ea6b-4cf2-aa04-77f4984c0bab
-- title:
--   Length of the obfuscation tapes in Figures 7 and 9
-- statement:
--   The number of coins the obfuscator reads on $(1^\lambda,X)$, and the maximum of this number over the four possible inputs $X_0,X_1,X_0\circ C,X_1\circ C$ of Figures 7 and 9. Each position receives a tape of this length and reads the prefix it needs, so the obfuscations use independent uniform coins.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Figure 7, p.23; Figure 9, p.28

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_QiOPoQ_Supplement_postX

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity

variable {G : GateSet}

/-- The number of coins the obfuscator reads on `(1^λ, X)`. -/
def obfCoins (Obf : UPPT) (n : ℕ) (X : Circ G) : ℕ :=
  Obf.coins.eval (pair (unary n) (encCirc X)).length

/-- The length of each obfuscation tape in Figures 7 and 9 (Gheorghiu, Gupte, Havlíček, Liu,
arXiv:2609.40289, sha256 fe2f9210…, Figure 7, p.23 and Figure 9, p.28: "independently compute"):
the largest number of coins the obfuscator reads on the four possible inputs `X_0`, `X_1`,
`X_0 ∘ C`, `X_1 ∘ C`. Each entry reads the prefix of its tape it needs, so the entries use
independent uniform coins. -/
def cvqcBlock (Obf : UPPT) (Xp : Bool → ℕ × ℕ × ℕ × ℕ → Circ G) (n : ℕ) (C : Circ G) : ℕ :=
  max (max (obfCoins Obf n (Xp false (shape C))) (obfCoins Obf n (Xp true (shape C))))
    (max (obfCoins Obf n (postX false C)) (obfCoins Obf n (postX true C)))

end QiOPoQ.Supplement


