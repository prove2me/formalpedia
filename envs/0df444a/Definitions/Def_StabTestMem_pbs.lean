-- Prove2me | Definitions.Def_StabTestMem_pbs
-- name    : StabTestMem_pbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:06.39026+00:00
-- url     : https://prove2.me/theorems/18d2e573-cebc-4383-8a07-defa2f0713dd
-- title:
--   Partial Bell sampling distribution $q^k_\psi$
-- statement:
--   For a pure state $\psi$ on $k+m$ qubits, the probability that partial Bell sampling (Algorithm 1) returns $(a,r)$ is
--
--   $$q^k_\psi(a,r)=\operatorname{Tr}\big[E_{a,r}\,(|\psi\rangle\langle\psi|\otimes|\psi\rangle\langle\psi|)\big],$$
--
--   with $E_{a,r}$ the POVM element of Eq. (25).
--
--   **Formalization Note** Defined from the measurement, not from the formula of Lemma 3.2.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Algorithm 1, p. 18; Lemma 3.2, p. 17

import Definitions.Def_StabTestMem_pbsElem
import Definitions.Def_ObliviousRSP_pureState

namespace StabTestMem

open QAlgorithms
open scoped Kronecker

/-- **Partial Bell sampling distribution `q^k_ψ(a, r)` (Algorithm 1).** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Algorithm 1,
p. 18, and Lemma 3.2, p. 17: "Let q^k_ψ denote the distribution induced on (a, r), where
a ∈ F_2^{2k} and r ∈ F_2^{n−k}, by partial Bell sampling from a pure state ψ."

`pbs ψ (a, r) = Re Tr[E_{a,r} (|ψ⟩⟨ψ| ⊗ |ψ⟩⟨ψ|)]`, the Born probability of outcome `(a, r)` for
the POVM element `E_{a,r}` = `pbsElem a r` of Eq. (25) on two copies of `ψ`.

**Formalization Note.** Defined operationally from the measurement, not from the formula of
Lemma 3.2. -/
noncomputable def pbs {k m : ℕ} (ψ : EuclideanSpace ℂ (Qubits (k + m)))
    (p : CutRankSched.Pauli k × (Fin m → ZMod 2)) : ℝ :=
  (Matrix.trace (pbsElem p.1 p.2 * (ObliviousRSP.pureState ψ ⊗ₖ ObliviousRSP.pureState ψ))).re

end StabTestMem


