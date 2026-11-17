-- Prove2me | Definitions.Def_RestrictedDec_Supplement_runGameM
-- name    : RestrictedDec_Supplement_runGameM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:22:12.130216+00:00
-- url     : https://prove2.me/theorems/1cf45bda-7f66-46fa-9bc1-5789923d2694
-- title:
--   The interaction of Definition 1 over a message space $M$
-- statement:
--   The interaction of an adversary with the indistinguishability game for a scheme $E$ over $M$, with public key $pk$, an oracle, a challenge bit $b$ and an activation budget:
--
--   1. a query $(F,c)$ is answered by the oracle (or refused);
--   2. the first challenge $(m_0,m_1)$ is valid when $m_0,m_1\in M_\lambda$ and $|m_0|=|m_1|$; the adversary then receives $c^*\leftarrow\mathrm{Enc}_{pk}(m_b)$; an invalid or repeated challenge ends the run with guess $0$;
--   3. a guess $b'$ ends the run; exhausting the budget ends it with guess $0$.
--
--   It is the game engine of the functional decryption experiments (Definition 1) and of the CPA experiment (Definition 2) over a general message space.
--
--   **Formalization Note** The published `RestrictedDec.runGame` with the challenge test "length $n(\lambda)$" replaced by "valid and of equal length".
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 1, p.13; Definition 2, p.29

import Mathlib
import Definitions.Def_RestrictedDec_encOpt
import Definitions.Def_RestrictedDec_PKE
import Definitions.Def_RestrictedDec_Adversary
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

open Classical in
/-- The **interaction of an adversary with an indistinguishability game** for the scheme `E` over
the message space `M`, with public key `pk`, oracle `oracle` and challenge bit `b`, run for at most
`fuel` activations; the phase `ph` is `none` before the challenge and `some (m₀, m₁, c*)` after it.
The result is the adversary's guess `b′`.
1. A query `(d, c)` is answered with `encOpt (oracle ph d c)` (`none` = no answer).
2. The first challenge `(m₀, m₁)` is valid when `m₀, m₁ ∈ M_λ` and `|m₀| = |m₁|`; then
   `c* ← Enc_pk(m_b)` is the adversary's next input. An invalid or repeated challenge ends the run
   with the guess `0`.
3. A guess `b′` ends the run. Running out of activations ends it with the guess `0`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 1, p.13, steps 1–5
("The adversary selects valid, equal-length messages m0, m1 ∈ M"); Definition 2, p.29.

**Formalization Note.** The published `RestrictedDec.runGame` with the challenge test
`|m₀| = |m₁| = n(λ)` replaced by `m₀, m₁ ∈ M_λ ∧ |m₀| = |m₁|`; otherwise identical. A run that ends
without a proper guess outputs the fixed guess `0`, independent of `b`. -/
noncomputable def runGameM (A : Adversary) (E : PKE) (M : ℕ → Str → Prop) (lam : ℕ) (pk : Str)
    (oracle : Option (Str × Str × Str) → Str → Str → Option Str) (b : Bool) :
    ℕ → Option (Str × Str × Str) → Str → Str → PMF Bool
  | 0, _, _, _ => PMF.pure false
  | fuel + 1, ph, s, input =>
    (A.activate lam s input).bind fun r =>
      match decMove r.2, ph with
      | .query d c, _ => runGameM A E M lam pk oracle b fuel ph r.1 (encOpt (oracle ph d c))
      | .challenge m0 m1, none =>
          if M lam m0 ∧ M lam m1 ∧ m0.length = m1.length then
            (E.encLaw lam pk (if b then m1 else m0)).bind fun cs =>
              runGameM A E M lam pk oracle b fuel (some (m0, m1, cs)) r.1 cs
          else PMF.pure false
      | .challenge _ _, some _ => PMF.pure false
      | .guess b', _ => PMF.pure b'

end Supplement

end RestrictedDec


