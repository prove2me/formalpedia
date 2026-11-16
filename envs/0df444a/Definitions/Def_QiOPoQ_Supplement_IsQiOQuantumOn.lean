-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsQiOQuantumOn
-- name    : QiOPoQ_Supplement_IsQiOQuantumOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:45:41.153286+00:00
-- url     : https://prove2.me/theorems/2747b607-72fe-407b-b764-cef041aa86b3
-- title:
--   Definition 3.2: qiO security against non-uniform QPT adversaries
-- statement:
--   Definition 3.2 with the adversary quantified over non-uniform QPT algorithms ("Depending on whether we quantify $A$ over all PPT or QPT algorithms, Obf is secure against classical or quantum adversaries"). For every two same-shape families in the class with negligible diamond distance and every non-uniform QPT adversary $A$,
--
--   $$\big|\Pr[A(1^\lambda,\mathrm{Obf}(1^\lambda,C_{0,\lambda}))=1]-\Pr[A(1^\lambda,\mathrm{Obf}(1^\lambda,C_{1,\lambda}))=1]\big|\le\mathrm{negl}(\lambda).$$
--
--   `IsQiOQuantum` is the instance for $\mathcal C_{\mathsf{BQP}}$, the hypothesis of Theorems 5.2 and 5.9.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.2, p.14; §5 (Theorems 5.2, 5.9)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_InCBQP
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_QiOPoQ_Supplement_NUQPT

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle QAlgorithms.Complexity

/-- `Pr[A(1^λ, Obf(1^λ, C)) = 1]` for a quantum adversary `A`, over the coins of `Obf` and of `A`
and the measurements of `A`. -/
noncomputable def obfAccQ (G : GateSet) (Obf : UPPT) (A : NUQPT) (n : ℕ) (C : Circ G) : ℝ :=
  Obf.expect (pair (unary n) (encCirc C)) fun s => A.acc G n s

/-- **Definition 3.2 (Quantum iO), against quantum adversaries, for a circuit class.**
Gheorghiu, Gupte, Havlíček, Liu, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.2, p.14 (the
security condition quoted for `IsQiOClassicalOn`) with "QPT algorithms" in place of "PPT": "Depending
on whether we quantify A over all PPT or QPT algorithms, Obf is secure against classical or
quantum adversaries."

For every two families in the class with equal shapes for every `λ` and negligible diamond
distance, and every non-uniform QPT adversary `A` (`NUQPT`), the acceptance probabilities on
obfuscations of the two families differ by a negligible function (chosen after the families and
`A`). Classes contain only polynomial-size families. -/
def IsQiOQuantumOn (G : GateSet) (cls : (ℕ → Circ G) → Prop) (Obf : UPPT) : Prop :=
  ∀ C0 C1 : ℕ → Circ G, cls C0 → cls C1 → (∀ n, shape (C0 n) = shape (C1 n)) →
    (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n, circDist (C0 n) (C1 n) ≤ μ n) →
    ∀ A : NUQPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n,
      |obfAccQ G Obf A n (C0 n) - obfAccQ G Obf A n (C1 n)| ≤ μ n

/-- qiO security for `C_BQP` against non-uniform QPT adversaries (§5: "an obfuscation scheme for
C_BQP satisfying qiO security against QPT adversaries", Theorems 5.2 and 5.9). -/
def IsQiOQuantum (G : GateSet) (Obf : UPPT) : Prop :=
  IsQiOQuantumOn G InCBQP Obf

end QiOPoQ.Supplement


