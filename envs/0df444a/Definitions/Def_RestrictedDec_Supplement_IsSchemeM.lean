-- Prove2me | Definitions.Def_RestrictedDec_Supplement_IsSchemeM
-- name    : RestrictedDec_Supplement_IsSchemeM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:20:44.928718+00:00
-- url     : https://prove2.me/theorems/3ed974f8-0159-45df-800b-acd985b420d3
-- title:
--   Efficient public-key encryption scheme over a message space $M$
-- statement:
--   A public-key encryption scheme $E=(\mathrm{KeyGen},\mathrm{Enc},\mathrm{Dec})$ with explicit coins is **efficient with message space $M$** if
--
--   1. its numbers of key-generation and encryption coins are polynomially bounded in $\lambda$;
--   2. $\mathrm{KeyGen}$, $\mathrm{Enc}$ (on generated public keys and messages $m\in M_\lambda$) and $\mathrm{Dec}$ (on generated secret keys and arbitrary ciphertexts) are computed by polynomial-time machines, uniformly in $\lambda$;
--   3. $\mathrm{Dec}$ outputs elements of $M_\lambda\cup\{\bot\}$: every plaintext it returns under a generated key lies in $M_\lambda$.
--
--   Every scheme the supplement asserts to exist is required to satisfy this predicate, and efficiency is kept separate from the security classes.
--
--   **Formalization Note** This is the published `RestrictedDec.PKE.IsScheme` with "length $n(\lambda)$" replaced by membership in $M_\lambda$; for $M_\lambda=\{0,1\}^{n(\lambda)}$ the two coincide.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.1, p.29; §2.1, pp.12–13

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_encOpt
import Definitions.Def_RestrictedDec_PKE
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- `E` is an **efficient public-key encryption scheme with message space `M = (M_λ)`**:
1. the numbers of key and encryption coins are polynomially bounded in `λ`;
2. `KeyGen`, `Enc` and `Dec` are each computed by one polynomial-time machine, uniformly in `λ`, on
   the inputs the scheme is used on: any key coins; any public key output by `KeyGen` with any
   message of `M_λ` and any coins; any secret key output by `KeyGen` with any string as
   ciphertext;
3. `Dec` outputs elements of `M_λ ∪ {⊥}`: every plaintext it returns under a generated secret key
   lies in `M_λ`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.1, p.29 ("A public-key
encryption scheme is a triple E = (KeyGen, Enc, Dec) with plaintext space Mλ … Decsk(c): output an
element of Mλ ∪ {⊥}"); §2.1, p.12; the PPT convention, p.13.

**Formalization Note.** This is the published `RestrictedDec.PKE.IsScheme` with the condition
`m.length = n λ` replaced by `M λ m`; for `M λ m := m.length = n λ` the two coincide. Machine inputs
are `BeyondDS.tup` codes, `λ` is `encNat λ`, an element of `M_⊥` is returned as `encOpt`. -/
def IsSchemeM (M : ℕ → Str → Prop) (E : PKE) : Prop :=
  NoisyOWMPC.PolyBounded E.keyCoins ∧ NoisyOWMPC.PolyBounded E.encCoins ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (E.keyCoins lam) → Bool),
    f (BeyondDS.tup [encNat lam, List.ofFn r]) =
      BeyondDS.tup [(E.keyGen lam r).1, (E.keyGen lam r).2]) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (E.keyCoins lam) → Bool) (m : Str)
    (ρ : Fin (E.encCoins lam) → Bool), M lam m →
    f (BeyondDS.tup [encNat lam, (E.keyGen lam r).1, m, List.ofFn ρ]) =
      E.enc lam (E.keyGen lam r).1 m ρ) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (E.keyCoins lam) → Bool) (c : Str),
    f (BeyondDS.tup [encNat lam, (E.keyGen lam r).2, c]) =
      encOpt (E.dec lam (E.keyGen lam r).2 c)) ∧
  (∀ lam (r : Fin (E.keyCoins lam) → Bool) (c m : Str),
    E.dec lam (E.keyGen lam r).2 c = some m → M lam m)

end Supplement

end RestrictedDec


