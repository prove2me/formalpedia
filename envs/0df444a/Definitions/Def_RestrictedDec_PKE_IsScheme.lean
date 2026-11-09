-- Prove2me | Definitions.Def_RestrictedDec_PKE_IsScheme
-- name    : RestrictedDec_PKE_IsScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:59.756741+00:00
-- url     : https://prove2.me/theorems/affdf35c-31e7-4349-b291-bd052c02b1c6
-- title:
--   Efficient scheme with message space $\{0,1\}^{n(\lambda)}$
-- statement:
--   A scheme $E$ is an **efficient public-key encryption scheme with message space $\mathcal M_\lambda=\{0,1\}^{n(\lambda)}$** if
--
--   1. the numbers of key coins and of encryption coins are polynomially bounded in $\lambda$;
--   2. $\mathrm{KeyGen}$, $\mathrm{Enc}$ and $\mathrm{Dec}$ are each computed by one polynomial-time machine, uniformly in $\lambda$ (given $1^\lambda$): key generation on all coins, encryption under every generated public key of every message in $\mathcal M_\lambda$ on all coins, and decryption under every generated secret key of every string;
--   3. $\mathrm{Dec}$ outputs elements of $\mathcal M_\lambda\cup\{\perp\}$: under a generated secret key every returned plaintext has length $n(\lambda)$.
--
--   Every scheme compared in Corollary 2 — the assumed IND-CCA2 scheme and both witnesses — is required to satisfy this predicate, so a scheme can never fall outside a security class merely for being inefficient.
--
--   **Formalization Note** Machine inputs are tuples coded by the published `BeyondDS.tup`; $\lambda$ is given in unary and a value of $\mathcal M_\perp$ is returned in the code of `RestrictedDec.encOpt`.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.1, p.29; Corollary 2, p.22; §2.1, p.12

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_encOpt
import Definitions.Def_RestrictedDec_PKE
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- `E` is an **efficient public-key encryption scheme with message space `M_λ = {0,1}^{n(λ)}`**:
1. the numbers of key and encryption coins are polynomially bounded in `λ`;
2. `KeyGen`, `Enc` and `Dec` are each computed by one polynomial-time machine, uniformly in `λ`
   (given `1^λ` in unary), on the inputs the scheme is used on: any key coins; any key pair output
   by `KeyGen` with any message of `M_λ` and any coins; any secret key output by `KeyGen` with any
   string as ciphertext;
3. `Dec` outputs elements of `M_λ ∪ {⊥}`: every plaintext it returns under a generated secret key
   has length `n(λ)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.1, p.29 ("Decsk(c):
output an element of Mλ ∪ {⊥}"); Corollary 2, p.22 ("the message space {0, 1}^{n(λ)}"); §2.1,
p.12 ("We treat Dec as a total function").

**Formalization Note.** Machine inputs are `BeyondDS.tup` codes; `λ` is `encNat λ`; a plaintext
of `M_⊥` is returned as `encOpt`. Efficiency is kept apart from the security classes `Sec`, so that
a scheme outside `Sec` is never outside merely for being inefficient. -/
def PKE.IsScheme (n : ℕ → ℕ) (E : PKE) : Prop :=
  NoisyOWMPC.PolyBounded E.keyCoins ∧ NoisyOWMPC.PolyBounded E.encCoins ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (E.keyCoins lam) → Bool),
    f (BeyondDS.tup [encNat lam, List.ofFn r]) =
      BeyondDS.tup [(E.keyGen lam r).1, (E.keyGen lam r).2]) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (E.keyCoins lam) → Bool) (m : Str)
    (ρ : Fin (E.encCoins lam) → Bool), m.length = n lam →
    f (BeyondDS.tup [encNat lam, (E.keyGen lam r).1, m, List.ofFn ρ]) =
      E.enc lam (E.keyGen lam r).1 m ρ) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (r : Fin (E.keyCoins lam) → Bool) (c : Str),
    f (BeyondDS.tup [encNat lam, (E.keyGen lam r).2, c]) =
      encOpt (E.dec lam (E.keyGen lam r).2 c)) ∧
  (∀ lam (r : Fin (E.keyCoins lam) → Bool) (c m : Str),
    E.dec lam (E.keyGen lam r).2 c = some m → m.length = n lam)

end RestrictedDec


