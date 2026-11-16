-- Prove2me | Definitions.Def_WICanon_Supplement_IsNUEfficient
-- name    : WICanon_Supplement_IsNUEfficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:55:03.41086+00:00
-- url     : https://prove2.me/theorems/8c0e8af2-d6ca-48d7-8c63-f0d7047af80a
-- title:
--   Interactive protocols with a non-uniform prover and verifier
-- statement:
--   An interactive protocol $(P,V)$ has a **non-uniform prover and verifier** when its number of rounds $k(n)$ and the coin counts of both parties are bounded by polynomials, and there is an advice sequence $\{a_n\}$ with $|a_n|$ polynomial in $n$ such that, on inputs $x$ of length $n$, the verifier's next-message function, the prover's next-message function and the verifier's decision are each computed in polynomial time from $a_n$ together with their usual inputs.
--
--   This is the setting of the "Moreover" clause of Theorem A.9.
--
--   **Formalization Note** It is the base mission's `Protocol.IsEfficient` with the advice $a_{|x|}$ prepended to the input of each of the three maps, and with round and coin counts only polynomially bounded, since a non-uniform machine reads them from its advice. One advice sequence serves both parties; two can be merged by pairing.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Theorem A.9, p.39 ("Moreover" clause); §2, p.11

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_WICanon_Protocol

set_option autoImplicit false

namespace WICanon.Supplement

open QAlgorithms.Complexity QAdvFew.PoQOracle QiOPoQ

/-- **Prover and verifier are non-uniform PPT** (Arnon, Mazor, Pass, Silbak, *Does Witness
Indistinguishability Require Cryptography?*, STOC 2027 submission manuscript, sha256 3f78ec3d…,
Theorem A.9, p.39: "the initial WI provided has a non-uniform prover and verifier"; §2, p.11): a
polynomial number of rounds and coins, and an advice sequence `a(n)` of polynomial length such that each
of the next-message and decision functions is polynomial-time given `a(|x|)`.

**Formalization Note.** This is the base `Protocol.IsEfficient` with the advice `a(|x|)` prepended to
the input of each of the three maps, and with the round and coin counts only polynomially bounded (a
non-uniform machine reads them from its advice). One advice sequence serves both parties; two would
be merged into one by pairing. -/
def IsNUEfficient (pv : Protocol) : Prop :=
  (∃ p : Polynomial ℕ, ∀ n, pv.rounds n ≤ p.eval n) ∧
  (∃ p : Polynomial ℕ, ∀ n, pv.coinsP n ≤ p.eval n) ∧
  (∃ p : Polynomial ℕ, ∀ n, pv.coinsV n ≤ p.eval n) ∧
  ∃ (a : ℕ → Str) (pa : Polynomial ℕ), (∀ n, (a n).length ≤ pa.eval n) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧
      ∀ x rV ms, g (pair (a x.length) (pair x (pair rV (tup ms)))) = pv.verMsg x rV ms) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧
      ∀ x w rP ρs, g (pair (a x.length) (pair x (pair w (pair rP (tup ρs))))) =
        pv.proverMsg x w rP ρs) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧
      ∀ x rV tr, g (pair (a x.length) (pair x (pair rV (tup tr)))) = bitStr (pv.accept x rV tr))

end WICanon.Supplement


