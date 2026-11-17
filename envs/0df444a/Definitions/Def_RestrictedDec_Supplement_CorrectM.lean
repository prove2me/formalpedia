-- Prove2me | Definitions.Def_RestrictedDec_Supplement_CorrectM
-- name    : RestrictedDec_Supplement_CorrectM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:21:20.551584+00:00
-- url     : https://prove2.me/theorems/5dabfa6d-a250-4d55-82d9-a39e6f4a3edf
-- title:
--   Ordinary negligible-error correctness over $M$ (Definition 3)
-- statement:
--   A function $\delta$ **bounds the honest-encryption decryption error** of $E$ over $M$ if for every $\lambda$ and every valid message $m\in M_\lambda$
--   $$\Pr_{(pk,sk)\leftarrow\mathrm{KeyGen}(1^\lambda),\ \rho}\big[\mathrm{Dec}_{sk}(\mathrm{Enc}_{pk}(m;\rho))\neq m\big]\le\delta(\lambda).$$
--   $E$ has **ordinary negligible-error correctness** (Definition 3) if some negligible $\delta_E$ bounds this error, uniformly over $m$.
--
--   Correctness is part of every security class $\mathrm{Sec}^t(\mathcal F)$, and the explicit bound $\delta_R$ appears in Theorem 11.
--
--   **Formalization Note** For $M_\lambda=\{0,1\}^{n(\lambda)}$ this is the published `RestrictedDec.Correct`.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 3, App. A.1, p.29

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_PKE
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

open Classical in
/-- `δ` **bounds the honest-encryption decryption error** of `E` over the message space `M`: for
every `λ` and every valid message `m ∈ M_λ`,
`Pr_{(pk,sk) ← KeyGen(1^λ), ρ}[Dec_sk(Enc_pk(m; ρ)) ≠ m] ≤ δ(λ)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 3, App. A.1, p.29.

**Formalization Note.** The probability is the mass of `true` of a `PMF Bool`; a bound that is
negative at some `λ` cannot hold there. -/
def ErrBound (M : ℕ → Str → Prop) (E : PKE) (δ : ℕ → ℝ) : Prop :=
  ∀ (lam : ℕ) (m : Str), M lam m →
    ((E.keyLaw lam).bind fun k =>
      (E.encLaw lam k.1 m).map fun c => decide (E.dec lam k.2 c ≠ some m)) true ≤
      ENNReal.ofReal (δ lam)

/-- **Ordinary negligible-error correctness** over the message space `M` (Definition 3): one
negligible function `δ_E` bounds the honest-encryption decryption error uniformly over `m ∈ M_λ`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 3, App. A.1, p.29
("there is a single negligible function δE(λ) such that, for every fixed valid message m ∈ Mλ …").

**Formalization Note.** For `M λ m := m.length = n λ` this is the published `RestrictedDec.Correct`.
`Negligible` is `NoisyOWMPC.Negligible`. -/
def CorrectM (M : ℕ → Str → Prop) (E : PKE) : Prop :=
  ∃ δ : ℕ → ℝ, NoisyOWMPC.Negligible δ ∧ ErrBound M E δ

end Supplement

end RestrictedDec


