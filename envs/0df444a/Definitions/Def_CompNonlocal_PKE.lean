-- Prove2me | Definitions.Def_CompNonlocal_PKE
-- name    : CompNonlocal_PKE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:14.48555+00:00
-- url     : https://prove2.me/theorems/a60bf222-2429-4c87-824e-f8915ab3c55d
-- title:
--   QCCC public-key encryption: syntax
-- statement:
--   A PKE scheme has three QPT algorithms: $\mathrm{KeyGen}(1^\kappa)\to(pk,sk)$ with classical $pk$ and a possibly quantum $sk$; $\mathrm{Enc}(pk,m)\to ct$ for $m\in\{0,1\}^\kappa$, classical $ct$; $\mathrm{Dec}(sk,ct)\to(m',sk')$ with $m'\in\{0,1\}^\kappa\cup\{\bot\}$ and an updated private state $sk'$.
--
--   **Formalization Note** A decryption output is a flag bit ($1$: a message follows) and $\kappa$ message bits.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 5, p.21

import Mathlib
import Definitions.Def_CompNonlocal_Family
import Definitions.Def_CompNonlocal_ICirc_branchOn
import Definitions.Def_CompNonlocal_ICirc_effectOn
import Definitions.Def_CompNonlocal_fit

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- QCCC public-key encryption schemes: the syntax. Głuch, Morimae, *From Computational Nonlocality
to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…),
Definition 5, p.21: "PKE.KeyGen(1^κ) → (pk, sk): The QPT key-generation algorithm outputs a
classical public key pk and a private state sk, which may be quantum. PKE.Enc(pk, m) → ct: The QPT
encryption algorithm takes a classical message m ∈ {0,1}^κ and outputs a classical ciphertext ct.
PKE.Dec(sk, ct) → (m′, sk′): The QPT decryption algorithm outputs a classical message
m′ ∈ {0,1}^κ ∪ {⊥} and an updated private state sk′."

The derived functions in this module: `sk κ pk`, the unnormalized secret state after `KeyGen` output
`pk` (trace `Pr[pk]`); `encProb κ pk m ct = Pr[Enc(pk, m) = ct]`; and `decMsg κ s`, the message (or
`⊥ = none`) encoded by a decryption output `s`.

**Formalization Note** `Enc` reads `pk ++ m` and keeps nothing; `Dec` reads `ct` and the secret state
on its quantum input and keeps `sk′` on its quantum output. A decryption output is a flag bit (`1`:
a message follows) and `κ` message bits. -/
structure PKE where
  /-- `KeyGen(1^κ) → (pk, sk)`. -/
  KeyGen : Family
  /-- `Enc(pk, m) → ct`. -/
  Enc : Family
  /-- `Dec(sk, ct) → (m′, sk′)`. -/
  Dec : Family

namespace PKE

/-- The unnormalized secret state after key generation outputs `pk`. -/
noncomputable def sk (E : PKE) (κ : ℕ) (pk : Str) :
    Matrix (Bits (E.KeyGen κ).outQ.length) (Bits (E.KeyGen κ).outQ.length) ℂ :=
  (E.KeyGen κ).branchOn 0 [] 1 (fun t => decide (t = pk))

/-- The probability that encrypting `m` under `pk` gives the ciphertext `ct`. -/
noncomputable def encProb (E : PKE) (κ : ℕ) (pk m ct : Str) : ℝ :=
  ((E.Enc κ).effectOn 0 (pk ++ m) (fun t => decide (t = ct))).trace.re

/-- The decrypted message: `some m′` (`m′ ∈ {0,1}^κ`) when the flag bit is `1`, `none` (`⊥`) else. -/
def decMsg (κ : ℕ) (s : Str) : Option Str :=
  if s.headD false then some (fit κ s.tail) else none

end PKE

end CompNonlocal


