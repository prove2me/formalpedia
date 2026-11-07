-- Prove2me | Definitions.Def_CompNonlocal_PKE_reuseGood
-- name    : CompNonlocal_PKE_reuseGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:36.211078+00:00
-- url     : https://prove2.me/theorems/9bd7aefc-0de7-4df5-894d-5a630911eb8f
-- title:
--   Probability that successive decryptions are correct
-- statement:
--   With $sk_0=sk$, $ct_i\leftarrow\mathrm{Enc}(pk,m_i)$, $(m'_i,sk_i)\leftarrow\mathrm{Dec}(sk_{i-1},ct_i)$, and messages $m_i$ chosen adaptively from $pk$ and the previous ciphertexts, this is the probability that $m'_i=m_i$ for all $i\le n$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 5, p.22

import Mathlib
import Definitions.Def_CompNonlocal_PKE

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The probability that successive decryptions of freshly encrypted, adaptively chosen messages
are all correct. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and
Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 5, p.22: "a secret key
supports q(κ) successive decryptions of honestly generated ciphertexts with fresh independent
encryption randomness. Messages may be chosen adaptively after seeing the public key and previous
public ciphertexts. Writing sk_0 = sk and ct_i ← PKE.Enc(pk, m_i), (m′_i, sk_i) ← PKE.Dec(sk_{i−1}, ct_i)
…".

**Formalization Note** `reuseGood E κ ch pk n hist m σ` is the probability, starting from the
unnormalized secret state `σ` (on `m` qubits) after the ciphertexts `hist`, that the next `n`
decryptions all return the encrypted message, where message `i` is `fit κ (ch pk hist_i)` (the chooser
`ch` sees the public key and the previous ciphertexts). Each step sums over the ciphertext, weighs
by its encryption probability, and keeps the decryption branch with the correct message; after `n`
steps the trace of the remaining unnormalized state is the probability. -/
noncomputable def PKE.reuseGood (E : PKE) (κ : ℕ) (ch : Str → List Str → Str) (pk : Str) :
    ℕ → List Str → (m : ℕ) → Matrix (Bits m) (Bits m) ℂ → ℝ
  | 0, _, _, σ => σ.trace.re
  | n + 1, hist, m, σ =>
      ∑ ct : Bits (E.Enc κ).outC.length,
        E.encProb κ pk (fit κ (ch pk hist)) (List.ofFn ct) *
          PKE.reuseGood E κ ch pk n (hist ++ [List.ofFn ct]) (E.Dec κ).outQ.length
            ((E.Dec κ).branchOn m (List.ofFn ct) σ
              (fun s => decide (PKE.decMsg κ s = some (fit κ (ch pk hist)))))

end CompNonlocal


