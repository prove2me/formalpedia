-- Prove2me | Definitions.Def_RestrictedDec_runGame
-- name    : RestrictedDec_runGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:42.638456+00:00
-- url     : https://prove2.me/theorems/719b0881-5994-4a0a-80ad-d168defead94
-- title:
--   The interaction of an adversary with an indistinguishability game
-- statement:
--   Fix a scheme over $\{0,1\}^{n(\lambda)}$, a public key $pk$, a challenge bit $b$ and an oracle. The adversary first receives $pk$ and is then run as follows.
--
--   1. A query $(F,c)$ is answered by the oracle (which may refuse).
--   2. The first challenge $(m_0,m_1)$ is valid when $m_0,m_1\in\{0,1\}^{n(\lambda)}$; then $c^*\leftarrow\mathrm{Enc}_{pk}(m_b)$ is its next input, and the oracle is told $(m_0,m_1,c^*)$.
--   3. A guess $b'$ ends the run with output $b'$.
--
--   An invalid or second challenge, or running out of activations, ends the run with output $0$.
--
--   This one interaction underlies the functional decryption experiments (Definition 1) and the CPA experiment (Definition 2).
--
--   **Formalization Note** A run that ends without a proper guess outputs the fixed guess $0$, which is independent of $b$, so the experiment then succeeds with probability exactly $1/2$. A guess before the challenge is allowed, since nothing seen then depends on $b$.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 1, p.13, steps 1–5; Definition 2, p.29

import Mathlib
import Definitions.Def_RestrictedDec_encOpt
import Definitions.Def_RestrictedDec_PKE
import Definitions.Def_RestrictedDec_Adversary
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

/-- The **interaction of an adversary with an indistinguishability game** for the scheme `E`
with message space `{0,1}^{n(λ)}`, public key `pk` and challenge bit `b`, run for at most `fuel`
activations; the phase `ph` is `none` before the challenge and `some (m₀, m₁, c*)` after it. The
result is the adversary's guess `b′`.
1. A query `(d, c)` is answered with `encOpt (oracle ph d c)` (`none` = no answer).
2. The first challenge `(m₀, m₁)` is valid when `m₀, m₁ ∈ {0,1}^{n(λ)}`; then
   `c* ← Enc_pk(m_b)` is the adversary's next input. An invalid or repeated challenge ends the run
   with the guess `0`.
3. A guess `b′` ends the run. Running out of activations ends it with the guess `0`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 1, p.13, steps
1–5; Definition 2, p.29.

**Formalization Note.** A run that ends without a proper guess outputs the fixed guess `0`, which
is independent of `b`; a fixed output `0` of the experiment instead would make every security class
empty. A guess before the challenge is allowed: nothing seen then depends on `b`. -/
noncomputable def runGame (A : Adversary) (E : PKE) (n : ℕ → ℕ) (lam : ℕ) (pk : Str)
    (oracle : Option (Str × Str × Str) → Str → Str → Option Str) (b : Bool) :
    ℕ → Option (Str × Str × Str) → Str → Str → PMF Bool
  | 0, _, _, _ => PMF.pure false
  | fuel + 1, ph, s, input =>
    (A.activate lam s input).bind fun r =>
      match decMove r.2, ph with
      | .query d c, _ => runGame A E n lam pk oracle b fuel ph r.1 (encOpt (oracle ph d c))
      | .challenge m0 m1, none =>
          if m0.length = n lam ∧ m1.length = n lam then
            (E.encLaw lam pk (if b then m1 else m0)).bind fun cs =>
              runGame A E n lam pk oracle b fuel (some (m0, m1, cs)) r.1 cs
          else PMF.pure false
      | .challenge _ _, some _ => PMF.pure false
      | .guess b', _ => PMF.pure b'

end RestrictedDec


