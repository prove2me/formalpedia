-- Prove2me | Definitions.Def_RestrictedDec_probeScheme
-- name    : RestrictedDec_probeScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:20.728237+00:00
-- url     : https://prove2.me/theorems/2164404d-9a84-4732-b819-97ab32ddf834
-- title:
--   The probe scheme (proof of Corollary 2)
-- statement:
--   Let $E$ be a scheme, $n$ a message length and $S_\lambda,T_\lambda$ coordinate sets; let $j$ be the least position of $T_\lambda\setminus S_\lambda$. The **probe scheme** keeps the keys of $E$ and sets
--
--   $$\mathrm{Enc}'_{pk}(m)=(0,\mathrm{Enc}^E_{pk}(m)),\qquad \mathrm{Dec}'_{sk}(0,c)=\mathrm{Dec}^E_{sk}(c),$$
--
--   $$\mathrm{Dec}'_{sk}(1,k)=\begin{cases}e_j,& \eta(sk)_k=1,\\ 0^n,& \eta(sk)_k=0,\end{cases}$$
--
--   for every probe index $k$, where $\eta(sk)$ is a fixed efficiently decodable encoding of the secret key; all other ciphertexts decrypt to $\perp$.
--
--   Since $q_S(0^n)=q_S(e_j)$ the probes leak nothing to a $q_S$-oracle, while a $q_T$-oracle reads off the secret key.
--
--   **Formalization Note** $(\beta,c)$ is the string $\beta c$ and the probe index is in unary. $\eta(sk)$ is the self-delimiting code `BeyondDS.selfDelim sk` (bits doubled, then $01$) followed by zeros, so every index is a probe and the set of probes is independent of the key. Where $T_\lambda\setminus S_\lambda=\emptyset$ every probe decrypts to $0^n$.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, p.22

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_RestrictedDec_PKE
import Definitions.Def_RestrictedDec_unitVec
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- The **probe scheme** of the first non-inclusion of Corollary 2, built from a scheme `E`: same
keys; `Enc′(m) = (0, Enc_E(m))`; `Dec′(0, c) = Dec_E(c)`; a probe ciphertext `(1, k)` decrypts to
`e_j` if the `k`-th bit of the encoding of `sk_E` is `1` and to `0ⁿ` if it is `0`, where `j` is
the least position of `T_λ \ S_λ`; all other ciphertexts decrypt to `⊥`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, p.22
("Keep its keys and encrypt m as (0, EncE(m)). Decrypt (0, c) using DecE(c). For probe ciphertexts
(1, k), with k ranging over the bits of a fixed, efficiently decodable encoding of skE, output 0n
or ej according to the k-th encoded secret-key bit. All other ciphertexts decrypt to ⊥.").

**Formalization Note.**
1. `(β, c)` is the string `β :: c`; the probe index `k` is `encNat k` (unary).
2. The encoding of `sk` is `BeyondDS.selfDelim sk` (each bit doubled, then `01`), read as
   followed by zeros: every `k` is a probe, and bits past the code read `0`. This keeps the set of
   probe ciphertexts and their `q_S`-answers independent of the secret key (a `⊥` past the end of
   the code would reveal `|sk|`).
3. `j = leastIdx (T_λ \ S_λ)`; where `T_λ \ S_λ = ∅`, `j = 0` and `e_0 = 0ⁿ`, so every probe
   decrypts to `0ⁿ` (the paper chooses `j` only where it exists). -/
def probeScheme (E : PKE) (n : ℕ → ℕ) (S T : ℕ → Finset ℕ) : PKE where
  keyCoins := E.keyCoins
  encCoins := E.encCoins
  keyGen := E.keyGen
  enc := fun lam pk m ρ => false :: E.enc lam pk m ρ
  dec := fun lam sk C =>
    match C with
    | false :: c => E.dec lam sk c
    | true :: w =>
      if encNat (BeyondDS.decNat w) = w then
        some (if (BeyondDS.selfDelim sk).getD (BeyondDS.decNat w) false
          then unitVec (n lam) (leastIdx (T lam \ S lam)) else zeros (n lam))
      else none
    | [] => none

end RestrictedDec


