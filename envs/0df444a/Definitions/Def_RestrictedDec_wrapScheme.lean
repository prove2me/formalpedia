-- Prove2me | Definitions.Def_RestrictedDec_wrapScheme
-- name    : RestrictedDec_wrapScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:53:21.105525+00:00
-- url     : https://prove2.me/theorems/cb351ff5-c97b-4162-b504-12df5726bdb2
-- title:
--   The wrap scheme (proof of Corollary 2)
-- statement:
--   Let $E$ be a scheme, $n$ a message length, $S_\lambda$ coordinate sets and $i$ the least position of $S_\lambda$. The **wrap scheme** keeps the keys of $E$ and sets
--
--   $$\mathrm{Enc}'_{pk}(m)=(0,\mathrm{Enc}^E_{pk}(m)),\qquad \mathrm{Dec}'_{sk}(0,c)=\mathrm{Dec}^E_{sk}(c),$$
--
--   $$\mathrm{Dec}'_{sk}(1,c)=\begin{cases}0^n,& \mathrm{Dec}^E_{sk}(c)=0^n,\\ e_i,& \text{otherwise};\end{cases}$$
--
--   all remaining ciphertext encodings decrypt to $\perp$.
--
--   After the challenge $(0,c^*)$, the distinct ciphertext $(1,c^*)$ reveals under $q_S$ whether $c^*$ encrypts $0^n$.
--
--   **Formalization Note** $(\beta,c)$ is the string $\beta c$; "otherwise" includes $\mathrm{Dec}^E_{sk}(c)=\perp$. Where $S_\lambda=\emptyset$, $e_i=0^n$.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, pp.22–23

import Mathlib
import Definitions.Def_RestrictedDec_PKE
import Definitions.Def_RestrictedDec_unitVec
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- The **wrap scheme** of the reverse non-inclusion of Corollary 2, built from a scheme `E`: same
keys; `Enc′(m) = (0, Enc_E(m))`; `Dec′(0, c) = Dec_E(c)`;
`Dec′(1, c) = 0ⁿ` if `Dec_E(c) = 0ⁿ`, and `e_i` otherwise (also when `Dec_E(c) = ⊥`), where `i` is
the least position of `S_λ`; all remaining ciphertext encodings decrypt to `⊥`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2,
pp.22–23 ("Again set Enc′(m) = (0, EncE(m)) and Dec′(0, c) = DecE(c), but now define
Dec′(1, c) = 0n if DecE(c) = 0n, ei otherwise. All remaining ciphertext encodings decrypt to ⊥.").

**Formalization Note.** `(β, c)` is the string `β :: c`; the only remaining encoding is the
empty string. `i = leastIdx S_λ`; where `S_λ = ∅`, `i = 0` and `e_0 = 0ⁿ` (the paper chooses `i`
only where it exists). -/
def wrapScheme (E : PKE) (n : ℕ → ℕ) (S : ℕ → Finset ℕ) : PKE where
  keyCoins := E.keyCoins
  encCoins := E.encCoins
  keyGen := E.keyGen
  enc := fun lam pk m ρ => false :: E.enc lam pk m ρ
  dec := fun lam sk C =>
    match C with
    | false :: c => E.dec lam sk c
    | true :: c =>
      some (if E.dec lam sk c = some (zeros (n lam)) then zeros (n lam)
        else unitVec (n lam) (leastIdx (S lam)))
    | [] => none

end RestrictedDec


