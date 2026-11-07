-- Prove2me | Definitions.Def_QiOPoQ_IsQiOClassical
-- name    : QiOPoQ_IsQiOClassical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:14.227448+00:00
-- url     : https://prove2.me/theorems/939ed270-092e-445a-b5f4-6a1c127a9d0a
-- title:
--   Definition 3.2: qiO security against classical adversaries
-- statement:
--   An obfuscator Obf for $\mathcal C_{\mathsf{BQP}}$ has **indistinguishability-obfuscation security against classical adversaries** if for every two (not necessarily uniformly generated) polynomial-size families $\{C_{0,\lambda}\}$, $\{C_{1,\lambda}\}$ in the class with $\mathrm{shape}(C_{0,\lambda})=\mathrm{shape}(C_{1,\lambda})$ for every $\lambda$ and $\|C_{0,\lambda}-C_{1,\lambda}\|_\diamond\le\mathrm{negl}(\lambda)$, and for every non-uniform classical PPT adversary $A$,
--
--   $$
--   \big|\Pr[A(1^\lambda,\mathrm{Obf}(1^\lambda,C_{0,\lambda}))=1]-\Pr[A(1^\lambda,\mathrm{Obf}(1^\lambda,C_{1,\lambda}))=1]\big|\le\mathrm{negl}(\lambda).
--   $$
--
--   The families are arbitrary functions of $\lambda$; the last negligible function may depend on the families and on $A$. The probability is over the coins of Obf and of $A$ (`obfAcc`).
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.2, p.14

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_InCBQP
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_NUPPT

set_option autoImplicit false

namespace QiOPoQ

open QAdvFew.PoQOracle QAlgorithms.Complexity

variable {G : GateSet}

/-- `Pr[A(1^λ, Obf(1^λ, C)) = 1]`, over the coins of `Obf` and of `A`. -/
noncomputable def obfAcc (Obf : UPPT) (A : NUPPT) (n : ℕ) (C : Circ G) : ℝ :=
  Obf.expect (pair (unary n) (encCirc C)) fun s => A.acc n s


/-- **Definition 3.2 (Quantum iO), against classical adversaries.** arXiv:2609.40289,
Definition 3.2, p.14: "For every two (not necessarily uniformly generated) polynomial-size circuit
families {C_{0,λ}} and {C_{1,λ}} in C such that for every λ ∈ N, shape(C_{0,λ}) = shape(C_{1,λ})
and ∥C_{0,λ} − C_{1,λ}∥⋄ ≤ negl(λ), and every (non-uniform) polynomial-time adversary A,
|Pr[A(1^λ, Obf(1^λ, C_{0,λ})) = 1] − Pr[A(1^λ, Obf(1^λ, C_{1,λ})) = 1]| ≤ negl(λ). Depending on
whether we quantify A over all PPT or QPT algorithms, Obf is secure against classical or quantum
adversaries."

The families are arbitrary functions of `λ` in C_BQP (so polynomial-size); the adversaries are
non-uniform classical PPT (`NUPPT`); `μ` is chosen after the families and the adversary. -/
def IsQiOClassical (G : GateSet) (Obf : UPPT) : Prop :=
  ∀ C0 C1 : ℕ → Circ G, InCBQP C0 → InCBQP C1 → (∀ n, shape (C0 n) = shape (C1 n)) →
    (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n, circDist (C0 n) (C1 n) ≤ μ n) →
    ∀ A : NUPPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n,
      |obfAcc Obf A n (C0 n) - obfAcc Obf A n (C1 n)| ≤ μ n

end QiOPoQ


