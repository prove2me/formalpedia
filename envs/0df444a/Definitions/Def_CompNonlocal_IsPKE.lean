-- Prove2me | Definitions.Def_CompNonlocal_IsPKE
-- name    : CompNonlocal_IsPKE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:48:22.342307+00:00
-- url     : https://prove2.me/theorems/0071d159-56ec-4caa-bf58-625b6df4b878
-- title:
--   QCCC public-key encryption with key reuse
-- statement:
--   A PKE scheme is **secure and correct** if:
--
--   1. its algorithms are uniform QPT;
--   2. correctness: for every $m\in\{0,1\}^\kappa$, $\Pr[m'=m]\ge1-\mathsf{negl}(\kappa)$;
--   3. reuse: for every polynomial $q$, after $q(\kappa)$ successive decryptions of fresh honest encryptions of adaptively chosen messages, the probability that some $m'_i\ne m_i$ is negligible;
--   4. IND-CPA: for every pair of polynomial-size adversaries $(\mathcal A_1,\mathcal A_2)$ with a quantum register passed between them, $\Pr[b'=b]\le\frac12+\mathsf{negl}(\kappa)$.
--
--   **Formalization Note** In 2 and 3 one negligible bound serves all messages and all choosers (Reading 6); this is equivalent to the per-sequence form since at each $\kappa$ there are finitely many relevant behaviours.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 5, pp.21–22

import Mathlib
import Definitions.Def_CompNonlocal_PKE_reuseGood
import Definitions.Def_CompNonlocal_PKE_cpaWin
import Definitions.Def_CompNonlocal_Uniform
import Definitions.Def_CompNonlocal_Negligible

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- QCCC public-key encryption with secret-key reuse. Głuch, Morimae, *From Computational
Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256
e245edd7…), Definition 5, pp.21–22:

1. the three algorithms are QPT;
2. "Correctness: For every m ∈ {0,1}^κ, Pr[m′ = m | (pk, sk) ← PKE.KeyGen(1^κ), ct ← PKE.Enc(pk, m),
   (m′, sk′) ← PKE.Dec(sk, ct)] ≥ 1 − negl(κ)";
3. "Moreover, for every polynomial q, a secret key supports q(κ) successive decryptions of honestly
   generated ciphertexts … the probability that any m′_i ≠ m_i is negligible";
4. "IND-CPA security: For every pair of polynomial-size quantum adversaries (A_1, A_2) with
   classical advice, the following experiment has Pr[b′ = b] ≤ 1/2 + negl(κ)".

**Formalization Note** In 2 and 3 one negligible bound serves every message, resp. every adaptive
message chooser (Reading 6); at each `κ` there are finitely many relevant behaviours, so this is
equivalent to a bound per message sequence. Correctness is `reuseGood` with one decryption and a
constant chooser. In 4 the bound is chosen after the adversary. -/
def IsPKE (E : PKE) : Prop :=
  Uniform E.KeyGen ∧ Uniform E.Enc ∧ Uniform E.Dec ∧
    (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ κ (m : Bits κ),
      1 - μ κ ≤ ∑ pk : Bits (E.KeyGen κ).outC.length,
        E.reuseGood κ (fun _ _ => List.ofFn m) (List.ofFn pk) 1 [] (E.KeyGen κ).outQ.length
          (E.sk κ (List.ofFn pk))) ∧
    (∀ q : Polynomial ℕ, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ (ch : Str → List Str → Str) κ,
      1 - ∑ pk : Bits (E.KeyGen κ).outC.length,
          E.reuseGood κ ch (List.ofFn pk) (q.eval κ) [] (E.KeyGen κ).outQ.length
            (E.sk κ (List.ofFn pk)) ≤ μ κ) ∧
    (∀ A₁ A₂ : Family, PolySize A₁ → PolySize A₂ → ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ κ,
      E.cpaWin κ (A₁ κ) (A₂ κ) ≤ 1 / 2 + μ κ)

end CompNonlocal


