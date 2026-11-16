-- Prove2me | Definitions.Def_StabTestMem_Supplement_phaseIdProb
-- name    : StabTestMem_Supplement_phaseIdProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:41:34.887195+00:00
-- url     : https://prove2.me/theorems/5f83774f-c5a2-4ba3-930c-3e7b2a052a68
-- title:
--   Average identification probability over degree-2 phase states
-- statement:
--   For an upper-triangular matrix $A\in\mathbb F_2^{n\times n}$ (diagonal included), the degree-2 phase state is $|\psi_A\rangle=2^{-n/2}\sum_x(-1)^{x^\top Ax}|x\rangle$. Let $U$ be the set of the $2^{n(n+1)/2}$ upper-triangular matrices. For a non-adaptive learner $L$ that outputs an estimate $\hat A$ of $A$ from $t$ copies of $|\psi_A\rangle$, its **average identification probability** is
--   $$p_{\mathrm{id}}(L)=\frac1{|U|}\sum_{A\in U}\Pr_{L,\psi_A}[\hat A=A],$$
--   the success probability when $A$ is uniform on $U$.
--
--   This is the success notion of Theorem 6.6. Distinct upper-triangular $A$ give states that differ even up to a global phase, so identifying $|\psi_A\rangle$ and identifying $A$ are the same task.
--
--   **Formalization Note** $|\psi_A\rangle$ is the published `StabTestMem.phaseState` and $U$ the published `StabTestMem.IsUpperTri`; the normalizing count is computed as the number of such matrices.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Theorem 6.6 and proof, pp. 56–57; §3.2, p. 19

import Definitions.Def_StabTestMem_Supplement_NALearner
import Definitions.Def_StabTestMem_phaseState
import Definitions.Def_StabTestMem_IsUpperTri

namespace StabTestMem.Supplement

open QAlgorithms

/-- **Average identification probability over the degree-2 phase-state ensemble.** Arunachalam,
Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444
(version of 2 Nov 2026), Theorem 6.6 and its proof, pp. 56–57: "A non-adaptive learner that
identifies an unknown state from the ensemble {|ψ_A⟩} with probability ≥ 2/3 … Let Â be a final
estimate of A from the learning protocol … A itself is uniformly distributed over upper-triangular
matrices in F_2^{n×n}."

For a learner `L` whose output is an estimate `Â` of the matrix, `phaseIdProb L` is
`(#U)⁻¹ Σ_{A ∈ U} Pr[Â = A]` with `U` the upper-triangular `F₂` matrices (the published
`StabTestMem.IsUpperTri`, diagonal included, `#U = 2^{n(n+1)/2}`) and the input `t` copies of the
published `StabTestMem.phaseState A` (`|ψ_A⟩ = 2^{−n/2} Σ_x (−1)^{xᵀAx}|x⟩`), as the pure state
`ObliviousRSP.pureState`.

**Formalization Note.** On upper-triangular matrices `A ↦ ψ_A` is injective, even up to a global
phase (the polynomials `Σ_i A_ii x_i + Σ_{i<j} A_ij x_i x_j` are distinct and vanish at `x = 0`),
so identifying the state is identifying `A`, and the learner outputs `Â` directly. -/
noncomputable def phaseIdProb {n k t : ℕ} {X : Type} [Fintype X]
    (L : NALearner n k t X (Matrix (Fin n) (Fin n) (ZMod 2))) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) (ZMod 2) => IsUpperTri A)).card : ℝ)⁻¹ *
    ∑ A ∈ Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) (ZMod 2) => IsUpperTri A),
      L.prob (ObliviousRSP.pureState (phaseState A)) (fun Â => Â = A)

end StabTestMem.Supplement


