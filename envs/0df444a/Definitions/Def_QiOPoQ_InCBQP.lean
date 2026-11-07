-- Prove2me | Definitions.Def_QiOPoQ_InCBQP
-- name    : QiOPoQ_InCBQP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:04:07.5242+00:00
-- url     : https://prove2.me/theorems/8a44c3c2-0598-45e6-b649-05124cf7d4ab
-- title:
--   The class $\mathcal C_{\mathsf{BQP}}$ of BQP circuits
-- statement:
--   The paper defines $\mathcal C_{\mathsf{BQP}}$ to be the circuits with $n_{\mathrm{in}}=n_{\mathrm{out}}=1$ such that for every $C\in\mathcal C_{\mathsf{BQP}}$ of description length $\lambda$ there is a bit $b_C$ with $\|C-X^{b_C}(\cdot)\|_\diamond\le\mathrm{negl}(\lambda)$. A family $\{C_\lambda\}$ is in the class here if it is polynomial-size, every $C_\lambda$ has one input and one output qubit, and there is one negligible $\mu$ with
--
--   $$
--   \forall\lambda\ \exists b:\quad \|C_\lambda-X^{b}(\cdot)\|_\diamond\le\mu(\lambda).
--   $$
--
--   **Formalization Note** "$\le\mathrm{negl}(\lambda)$" only has a meaning for a family, so membership is defined for families indexed by the security parameter, with one negligible function per family. Polynomial size is what Definition 3.2 asks of its families.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.1, p.13

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QiOPoQ_diamond
import Definitions.Def_QiOPoQ_bitFlip

set_option autoImplicit false

namespace QiOPoQ

open QAdvFew.PoQOracle

variable {G : GateSet}

/-- **The class C_BQP of BQP circuits (§3.1).** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable
Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256
fe2f9210…), §3.1, p.13: "We define the class C_BQP to be circuits with n_in = n_out = 1, such
that for every C ∈ C_BQP of description length λ, there is a bit b_C such that
∥C − X^{b_C}(·)∥⋄ ≤ negl(λ)."

A family `{C_λ}` is in C_BQP if it is polynomial-size, every `C_λ` has one input and one output
qubit, and for one negligible `μ` every `C_λ` is within `μ(λ)` in diamond distance of `X^b(·)`
for some bit `b = b_{C_λ}`.

**Formalization Note.** "≤ negl(λ)" is a statement about families, so membership is defined for
families indexed by the security parameter, with one negligible function per family. The
families are polynomial-size, as in every use of C_BQP in §3–4 (Definition 3.2 requires it; the
paper indexes by description length, which ties size polynomially to λ). Negligible is the
published `QAdvFew.PoQOracle.Negligible`. -/
def InCBQP (Cf : ℕ → Circ G) : Prop :=
  PolySize Cf ∧ (∀ n, (Cf n).nin = 1) ∧ (∀ n, (Cf n).out.length = 1) ∧
    ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n, ∃ b : Bool, diamond (chanAs (Cf n) 1 1) (bitFlip b) ≤ μ n

end QiOPoQ


