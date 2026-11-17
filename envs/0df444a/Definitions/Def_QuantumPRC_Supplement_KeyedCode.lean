-- Prove2me | Definitions.Def_QuantumPRC_Supplement_KeyedCode
-- name    : QuantumPRC_Supplement_KeyedCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:32:59.970996+00:00
-- url     : https://prove2.me/theorems/c3e966d5-ec30-42f9-a765-a19f60afff79
-- title:
--   Arbitrary keyed codes and their robustness (43)
-- statement:
--   A **keyed code** from $n_L$ to $n_P$ qubits consists, for every security parameter $\lambda$, of a finite set of keys $\mathcal K_\lambda$ with a probability distribution $(\pi_\lambda(k))_{k\in\mathcal K_\lambda}$ (nonnegative weights summing to $1$), and, for every key $k$, of quantum channels (CPTP maps)
--
--   $$
--   \mathrm{Enc}_{\lambda,k}:\ \mathsf L\big((\mathbb C^2)^{\otimes n_L(\lambda)}\big)\to \mathsf L\big((\mathbb C^2)^{\otimes n_P(\lambda)}\big),\qquad \mathrm{Dec}_{\lambda,k}:\ \mathsf L\big((\mathbb C^2)^{\otimes n_P(\lambda)}\big)\to \mathsf L\big((\mathbb C^2)^{\otimes n_L(\lambda)}\big).
--   $$
--
--   Given a noise family $\mathcal E=\{\mathcal E_\lambda\}$ of channels on $n_P(\lambda)$ qubits, the code is **robust to $\mathcal E$** (the condition (43) of Definition 4.3) if there is a negligible function $\nu$ with
--
--   $$
--   \Big\|\ \sum_{k}\pi_\lambda(k)\,\mathrm{Dec}_{\lambda,k}\circ\mathcal E_\lambda\circ\mathrm{Enc}_{\lambda,k}\ -\ \mathrm{id}\ \Big\|_\diamond\ \le\ \nu(\lambda)\qquad\text{for all }\lambda .
--   $$
--
--   No efficiency and no pseudorandomness are required. This is the class over which the impossibility result Theorem 4.7 is stated: every secret-key $\mathcal D$-QPRC of Definition 4.3, for every ideal distribution $\mathcal D$, is a keyed code (its key is a classical string of polynomial length, hence finitely distributed, and its encoder and decoder are CPTP maps), with the same key-averaged channel.
--
--   **Formalization Note** Channels are `WildeQIT.QChannel` values (finite Kraus families), and $\|\cdot\|_\diamond$ is the base mission's `diamondDist`, which includes the factor $\tfrac12$ of p.16.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Definition 4.3 (syntax, robustness (43)), p.25; Lemma 4.9, p.27

import Mathlib
import Definitions.Def_QuantumPRC_IsLocalNoise

open Matrix

namespace QuantumPRC.Supplement

/-- **Arbitrary keyed code from `nL` to `nP` qubits** (the class over which Theorem 4.7 is an
impossibility). Hsieh, Yamada, *Quantum Pseudorandom Error-Correcting Codes*, arXiv:2609.38986
(version of October 29, 2026, sha256 6901b59d…), Definition 4.3 (syntax and robustness (43)), p.25,
and Lemma 4.9, p.27 ("a tuple of algorithms satisfying the syntax of secret-key QPRCs").

For every `λ`: a finite key set `Key λ` with probabilities `prob λ k` (nonnegative, summing to `1`),
and for every key `k` CPTP maps `enc λ k` from `nL(λ)` to `nP(λ)` qubits and `dec λ k` back.

**Formalization Note.** No efficiency and no pseudorandomness are required, and the key
distribution is arbitrary (real weights). The key of a secret-key `D`-QPRC is a classical string of
polynomial length output by a QPT algorithm, so its distribution is a finite distribution, and its
`Enc_sk`, `Dec_sk` are CPTP maps (they have Kraus representations, `WildeQIT.QChannel`); hence every
secret-key `D`-QPRC, for every ideal distribution `D`, gives such a code with the same key-averaged
channel. -/
structure KeyedCode (nL nP : ℕ → ℕ) where
  Key : ℕ → Type
  [instFintype : ∀ lam, Fintype (Key lam)]
  prob : ∀ lam, Key lam → ℝ
  prob_nonneg : ∀ lam k, 0 ≤ prob lam k
  prob_sum : ∀ lam, ∑ k, prob lam k = 1
  enc : ∀ lam, Key lam → WildeQIT.QChannel (Bits (nL lam)) (Bits (nP lam))
  dec : ∀ lam, Key lam → WildeQIT.QChannel (Bits (nP lam)) (Bits (nL lam))

attribute [instance] KeyedCode.instFintype

namespace KeyedCode

variable {nL nP : ℕ → ℕ} (S : KeyedCode nL nP)

/-- `𝔼_{sk}(Dec_sk ∘ N ∘ Enc_sk)` for a map `N` on `nP(λ)` qubits. -/
noncomputable def avgDecNEnc (lam : ℕ) (N : Superop (Bits (nP lam)) (Bits (nP lam))) :
    Superop (Bits (nL lam)) (Bits (nL lam)) :=
  fun ρ => ∑ k, (S.prob lam k : ℂ) • (S.dec lam k).apply (N ((S.enc lam k).apply ρ))

/-- **Robustness (43)**, Definition 4.3, p.25:
`‖𝔼_{sk←KeyGen(1^λ)}(Dec_sk ∘ E_λ ∘ Enc_sk) − id‖⋄ ≤ negl(λ)` for the noise family `E`. -/
def Robust (E : ∀ lam, WildeQIT.QChannel (Bits (nP lam)) (Bits (nP lam))) : Prop :=
  ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
    diamondDist (S.avgDecNEnc lam (E lam).apply) id ≤ ν lam

end KeyedCode

end QuantumPRC.Supplement


