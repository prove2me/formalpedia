-- Prove2me | Definitions.Def_RestrictedDec_PKE
-- name    : RestrictedDec_PKE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:00.320632+00:00
-- url     : https://prove2.me/theorems/e3a51a3a-d334-4a82-b89f-4887921775ca
-- title:
--   Public-key encryption scheme $E=(\mathrm{KeyGen},\mathrm{Enc},\mathrm{Dec})$
-- statement:
--   A **public-key encryption scheme** $E=(\mathrm{KeyGen},\mathrm{Enc},\mathrm{Dec})$ consists of, for every security parameter $\lambda$,
--
--   1. $\mathrm{KeyGen}(1^\lambda)$: on uniform key coins, a key pair $(pk,sk)$;
--   2. $\mathrm{Enc}_{pk}(m;\rho)$: on a plaintext $m$ and uniform encryption coins $\rho$, a ciphertext $c$;
--   3. $\mathrm{Dec}_{sk}(c)\in\mathcal M_\lambda\cup\{\perp\}$, deterministic and total (it returns $\perp$ on invalid inputs).
--
--   The laws of $(pk,sk)\leftarrow\mathrm{KeyGen}(1^\lambda)$ and of $c\leftarrow\mathrm{Enc}_{pk}(m)$ are the images of the uniform distribution on the coins.
--
--   **Formalization Note** Keys, plaintexts and ciphertexts are bit strings; the numbers of key and encryption coins are functions of $\lambda$. The message space and efficiency are imposed separately by `PKE.IsScheme`.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.1, p.29; §2.1, p.12

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- A **public-key encryption scheme** `E = (KeyGen, Enc, Dec)`, one per security parameter `λ`.
`keyGen λ r` is the key pair `(pk, sk)` on key coins `r ∈ {0,1}^{keyCoins λ}`; `enc λ pk m ρ` is the
ciphertext of `m` on coins `ρ ∈ {0,1}^{encCoins λ}`; `dec λ sk c ∈ M_⊥` is deterministic and total
(`none` = `⊥`).
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A.1, p.29 ("KeyGen(1λ):
output a key pair (pk, sk). Encpk(m; r): on plaintext m ∈ Mλ and coins r, output a ciphertext
c ∈ Cλ. Decsk(c): output an element of Mλ ∪ {⊥}"); §2.1, p.12 ("We treat Dec as a total function
by returning ⊥ on invalid inputs").

**Formalization Note.** Keys, plaintexts and ciphertexts are bit strings `Str`; the message space
`M_λ = {0,1}^{n(λ)}` and efficiency are imposed by `PKE.IsScheme`. Randomness is an explicit
uniform coin vector. -/
structure PKE where
  keyCoins : ℕ → ℕ
  encCoins : ℕ → ℕ
  keyGen : (lam : ℕ) → (Fin (keyCoins lam) → Bool) → Str × Str
  enc : (lam : ℕ) → Str → Str → (Fin (encCoins lam) → Bool) → Str
  dec : ℕ → Str → Str → Option Str

/-- The law of the key pair `(pk, sk) ← KeyGen(1^λ)`: `keyGen` on uniform coins. -/
noncomputable def PKE.keyLaw (E : PKE) (lam : ℕ) : PMF (Str × Str) :=
  (PMF.uniformOfFintype (Fin (E.keyCoins lam) → Bool)).map (E.keyGen lam)

/-- The law of `c ← Enc_pk(m)`: `enc` on uniform coins. -/
noncomputable def PKE.encLaw (E : PKE) (lam : ℕ) (pk m : Str) : PMF Str :=
  (PMF.uniformOfFintype (Fin (E.encCoins lam) → Bool)).map (E.enc lam pk m)

end RestrictedDec


