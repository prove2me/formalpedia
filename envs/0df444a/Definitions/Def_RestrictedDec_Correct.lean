-- Prove2me | Definitions.Def_RestrictedDec_Correct
-- name    : RestrictedDec_Correct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:53:06.988917+00:00
-- url     : https://prove2.me/theorems/b50b5262-a67d-4707-9398-2864ab14f979
-- title:
--   Ordinary negligible-error correctness (Definition 3)
-- statement:
--   A scheme $E$ over $\mathcal M_\lambda=\{0,1\}^{n(\lambda)}$ has **negligible honest-encryption decryption error** if there is a single negligible function $\varepsilon_E$ such that for every $\lambda$ and every valid message $m\in\mathcal M_\lambda$,
--
--   $$\Pr_{(pk,sk)\leftarrow\mathrm{KeyGen}(1^\lambda),\ \rho}\bigl[\mathrm{Dec}_{sk}(\mathrm{Enc}_{pk}(m;\rho))\neq m\bigr]\le\varepsilon_E(\lambda).$$
--
--   The bound is uniform over plaintexts; the probability is over key generation and the encryption coins. Definition 1 builds this "ordinary correctness" into every security class.
--
--   **Formalization Note** Negligible is the published `NoisyOWMPC.Negligible` (nonnegative and eventually below $\lambda^{-c}$ for every $c>0$).
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 3, App. A.1, p.29

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_PKE
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- **Ordinary negligible-error correctness** (negligible honest-encryption decryption error,
Definition 3): there is one negligible function `ε_E` such that for every `λ` and every valid
message `m ∈ M_λ = {0,1}^{n(λ)}`,
`Pr_{(pk,sk) ← KeyGen(1^λ), ρ}[Dec_sk(Enc_pk(m; ρ)) ≠ m] ≤ ε_E(λ)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 3, App. A.1, p.29.

**Formalization Note.** `Negligible` is the published `NoisyOWMPC.Negligible` (nonnegative and
eventually below `λ^{−c}` for every `c > 0`); its sign clause is automatic for a bound on a
probability. The probability is the mass of `true` of a `PMF Bool`. -/
def Correct (n : ℕ → ℕ) (E : PKE) : Prop :=
  ∃ err : ℕ → ℝ, NoisyOWMPC.Negligible err ∧ ∀ (lam : ℕ) (m : Str), m.length = n lam →
    ((E.keyLaw lam).bind fun k =>
      (E.encLaw lam k.1 m).map fun c => decide (E.dec lam k.2 c ≠ some m)) true ≤
      ENNReal.ofReal (err lam)

end RestrictedDec


