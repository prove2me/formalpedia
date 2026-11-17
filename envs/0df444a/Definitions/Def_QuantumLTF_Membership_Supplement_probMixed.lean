-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
-- name    : QuantumLTF_Membership_Supplement_probMixed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:41:36.472817+00:00
-- url     : https://prove2.me/theorems/2a4c1b76-6c38-403c-a107-8926d697e8fe
-- title:
--   Outcome probability of a mixed state after a unitary
-- statement:
--   For a unitary $U$, a density matrix $\rho$ and a set $P$ of computational-basis outcomes,
--   $$\Pr[P]=\sum_{z\in P}\mathrm{Re}\,(U\rho U^\dagger)_{zz}$$
--   is the probability that measuring $U\rho U^\dagger$ in the computational basis gives an outcome in $P$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 5.6, p. 70 (PDF p. 71)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QuantumLTF.Membership.Supplement

open QAlgorithms

/-- **Outcome probability of a mixed state after a unitary.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 5.6, p. 70 (PDF p. 71):
the success probability of the tomography procedure on the input `ρ_K`. The probability that a
computational-basis measurement of `U ρ U†` gives an outcome satisfying `P`:
`Σ_{z ∈ P} Re (U ρ U†)(z, z)`. -/
noncomputable def probMixed {ι : Type} [Fintype ι] [DecidableEq ι] (U ρ : Matrix ι ι ℂ)
    (P : ι → Prop) [DecidablePred P] : ℝ :=
  ∑ z ∈ Finset.univ.filter P, ((U * ρ * U.conjTranspose) z z).re

end QuantumLTF.Membership.Supplement


