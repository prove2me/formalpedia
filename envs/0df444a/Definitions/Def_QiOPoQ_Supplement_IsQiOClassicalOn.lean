-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsQiOClassicalOn
-- name    : QiOPoQ_Supplement_IsQiOClassicalOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:44:57.285073+00:00
-- url     : https://prove2.me/theorems/de282a60-bc5f-4989-8e7a-d212545fde14
-- title:
--   Definition 3.2: qiO security against classical adversaries for a circuit class
-- statement:
--   Definition 3.2 for an arbitrary class $\mathcal C$ of polynomial-size families. For every two families $\{C_{0,\lambda}\},\{C_{1,\lambda}\}$ in $\mathcal C$ with $\mathrm{shape}(C_{0,\lambda})=\mathrm{shape}(C_{1,\lambda})$ for every $\lambda$ and $\|C_{0,\lambda}-C_{1,\lambda}\|_\diamond\le\mathrm{negl}(\lambda)$, and every non-uniform classical PPT adversary $A$,
--
--   $$\big|\Pr[A(1^\lambda,\mathrm{Obf}(1^\lambda,C_{0,\lambda}))=1]-\Pr[A(1^\lambda,\mathrm{Obf}(1^\lambda,C_{1,\lambda}))=1]\big|\le\mathrm{negl}(\lambda).$$
--
--   **Formalization Note** For $\mathcal C=\mathcal C_{\mathsf{BQP}}$ it is, by definition, the published `QiOPoQ.IsQiOClassical`; the negligible bound is chosen after the families and the adversary.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.2, p.14

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QiOPoQ_IsQiOClassical

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle QAlgorithms.Complexity

/-- **Definition 3.2 (Quantum iO), against classical adversaries, for a circuit class.**
Gheorghiu, Gupte, Havlíček, Liu, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.2, p.14: "For
every two (not necessarily uniformly generated) polynomial-size circuit families {C_{0,λ}} and
{C_{1,λ}} in C such that for every λ ∈ N, shape(C_{0,λ}) = shape(C_{1,λ}) and
∥C_{0,λ} − C_{1,λ}∥⋄ ≤ negl(λ), and every (non-uniform) polynomial-time adversary A,
|Pr[A(1^λ, Obf(1^λ, C_{0,λ})) = 1] − Pr[A(1^λ, Obf(1^λ, C_{1,λ})) = 1]| ≤ negl(λ)."

Adversaries are non-uniform classical PPT (the published `NUPPT`); `obfAcc` is the published
acceptance probability. **Formalization Note.** The published `QiOPoQ.IsQiOClassical` is the
instance `cls = InCBQP` (definitionally); classes contain only polynomial-size families. -/
def IsQiOClassicalOn (G : GateSet) (cls : (ℕ → Circ G) → Prop) (Obf : UPPT) : Prop :=
  ∀ C0 C1 : ℕ → Circ G, cls C0 → cls C1 → (∀ n, shape (C0 n) = shape (C1 n)) →
    (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n, circDist (C0 n) (C1 n) ≤ μ n) →
    ∀ A : NUPPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n,
      |obfAcc Obf A n (C0 n) - obfAcc Obf A n (C1 n)| ≤ μ n

end QiOPoQ.Supplement


