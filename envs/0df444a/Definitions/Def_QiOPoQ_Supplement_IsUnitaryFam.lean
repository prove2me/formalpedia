-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsUnitaryFam
-- name    : QiOPoQ_Supplement_IsUnitaryFam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:02:42.838747+00:00
-- url     : https://prove2.me/theorems/bdb69439-6bf5-47e2-9b93-4dde49b5669f
-- title:
--   Unitary circuit families
-- statement:
--   A family $\{C_\lambda\}$ is unitary if every $C_\lambda$ has $n_{\mathrm{in}}=n_{\mathrm{out}}$ and, for one negligible $\mu$, there are unitaries $U_\lambda$ on $n_{\mathrm{in}}$ qubits with
--
--   $$\|C_\lambda-U_\lambda(\cdot)U_\lambda^\dagger\|_\diamond\le\mu(\lambda).$$
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.1, p.13

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QiOPoQ_diamond

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle QAlgorithms

/-- **Unitary circuits (§3.1).** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage
and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), §3.1,
p.13: "A circuit C is unitary if there is a unitary U on n_in = n_out qubits such that
∥C − U∥⋄ ≤ negl(λ), where U(ρ) := UρU†. We denote this class of circuits by C_unitary."

A family is unitary if every member has `n_in = n_out` and, for one negligible `μ`, each `C_λ` is
within `μ(λ)` in diamond distance of the channel `ρ ↦ UρU†` of some unitary `U` on `n_in` qubits.
-/
def IsUnitaryFam {G : GateSet} (Cf : ℕ → Circ G) : Prop :=
  (∀ n, (Cf n).nin = (Cf n).out.length) ∧
    ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n, ∃ U ∈ Matrix.unitaryGroup (Fin (Cf n).nin → Bool) ℂ,
      diamond (chanAs (Cf n) (Cf n).nin (Cf n).nin) (conjSuperop U) ≤ μ n

end QiOPoQ.Supplement


