-- Prove2me | Definitions.Def_QiOPoQ_IsTwoMsgPoQ
-- name    : QiOPoQ_IsTwoMsgPoQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:04:18.449469+00:00
-- url     : https://prove2.me/theorems/ad40de6f-3e00-4e3f-8bca-e1a987adacf9
-- title:
--   Definition 3.3: two-message proof of quantumness
-- statement:
--   Let $\ell$ be a polynomial. A **two-message proof of quantumness** is a tuple (Challenge, Prove, Verify) with:
--
--   1. **Syntax.** $\mathrm{Challenge}(1^\lambda;r)$ is a classical polynomial-time algorithm with coins $r\in\{0,1\}^{\ell(\lambda)}$; $\mathrm{Prove}(1^\lambda,\mathsf{chall})$ is a quantum polynomial-time prover returning a classical response; $\mathrm{Verify}(1^\lambda,r,\mathsf{chall},\mathsf{resp})$ is a classical polynomial-time decision algorithm.
--   2. **Completeness.** There is a negligible $\mu$ with $\Pr[\mathrm{Verify}=1]\ge1-\mu(\lambda)$ for all $\lambda$, for uniform $r$, $\mathsf{chall}=\mathrm{Challenge}(1^\lambda;r)$ and $\mathsf{resp}\leftarrow\mathrm{Prove}(1^\lambda,\mathsf{chall})$.
--   3. **Classical soundness.** For every classical PPT prover $A$ there is a negligible $\mu_A$ with $\Pr[\mathrm{Verify}=1]\le\mu_A(\lambda)$ for all $\lambda$, for uniform $r$, $\mathsf{chall}=\mathrm{Challenge}(1^\lambda;r)$ and $\mathsf{resp}\leftarrow A(1^\lambda,\mathsf{chall})$.
--
--   **Formalization Note** Prove is given by its classical generator (see `qptExpect`), so an arbitrary function from challenges to responses does not qualify. Provers $A$ are non-uniform, as everywhere in the paper.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.3, pp.14–15

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_NUPPT
import Definitions.Def_QiOPoQ_qptExpect

set_option autoImplicit false

namespace QiOPoQ

open QAdvFew.PoQOracle QAlgorithms.Complexity

/-- The efficiency clauses of Definition 3.3 (Gheorghiu, Gupte, Havlíček, Liu, *Verifiable
Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289, sha256
fe2f9210…, Definition 3.3, pp.14–15): "Challenge(1^λ; r) → chall is a classical polynomial-time
challenge algorithm with coins r ∈ {0, 1}^{ℓ(λ)}"; "Prove(1^λ, chall) → resp is a quantum
polynomial-time prover" (its classical generator `prove λ chall` is computed in polynomial time,
see `qptExpect`); "Verify(1^λ, r, chall, resp) → {0, 1} is a classical polynomial-time decision
algorithm". Each is a deterministic polynomial-time map on the encoded inputs. -/
def PoQEfficient (ℓ : Polynomial ℕ) (chal : ℕ → Str → Str) (prove : ℕ → Str → Str)
    (verify : ℕ → Str → Str → Str → Bool) : Prop :=
  (∃ g : Str → Str, PolyTimeComputable g ∧
      ∀ n (r : Str), r.length = ℓ.eval n → g (pair (unary n) r) = chal n r) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ n (c : Str), g (pair (unary n) c) = prove n c) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧
      ∀ n (r c s : Str), g (tup [unary n, r, c, s]) = bitStr (verify n r c s))

/-- Completeness (Definition 3.3, p.15): "There is a negligible function μ such that, for every
λ, Pr[Verify(1^λ, r, chall, resp) = 1 : r ← {0, 1}^{ℓ(λ)}, chall ← Challenge(1^λ; r),
resp ← Prove(1^λ, chall)] ≥ 1 − μ(λ)." -/
noncomputable def PoQComplete (G : GateSet) (ℓ : Polynomial ℕ) (chal : ℕ → Str → Str)
    (prove : ℕ → Str → Str) (verify : ℕ → Str → Str → Str → Bool) : Prop :=
  ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n, 1 - μ n ≤ avgCoins (ℓ.eval n) fun r =>
    qptExpect G (prove n (chal n r)) fun s => if verify n r (chal n r) s then 1 else 0

/-- Classical soundness (Definition 3.3, p.15): "for every classical probabilistic
polynomial-time prover A, there is a negligible function μ_A such that, for every λ,
Pr[Verify(1^λ, r, chall, resp) = 1 : r ← {0, 1}^{ℓ(λ)}, chall ← Challenge(1^λ; r),
resp ← A(1^λ, chall)] ≤ μ_A(λ)." Provers are non-uniform (§3, p.13). -/
def PoQSound (ℓ : Polynomial ℕ) (chal : ℕ → Str → Str)
    (verify : ℕ → Str → Str → Str → Bool) : Prop :=
  ∀ A : NUPPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n,
    avgCoins (ℓ.eval n) (fun r => A.expect n (chal n r) fun s =>
      if verify n r (chal n r) s then 1 else 0) ≤ μ n

/-- **Definition 3.3 (Two-message proof of quantumness).** arXiv:2609.40289, Definition 3.3,
pp.14–15: "Let ℓ be a polynomial. A two-message (one-round) proof of quantumness is a tuple of
algorithms (Challenge, Prove, Verify)" with the syntax of `PoQEfficient`, completeness
(`PoQComplete`) and classical soundness (`PoQSound`).

**Formalization Note.** `chal λ r` is the challenge on coins `r` (`|r| = ℓ(λ)`); `prove λ chall`
is the classical description (a tuple of circuit codes over `G`) that the quantum prover runs,
see `qptExpect`; `verify λ r chall resp` is the decision. Inputs are encoded with `pair` and
`tup`. -/
def IsTwoMsgPoQ (G : GateSet) (ℓ : Polynomial ℕ) (chal : ℕ → Str → Str)
    (prove : ℕ → Str → Str) (verify : ℕ → Str → Str → Str → Bool) : Prop :=
  PoQEfficient ℓ chal prove verify ∧ PoQComplete G ℓ chal prove verify ∧ PoQSound ℓ chal verify

end QiOPoQ


