-- Prove2me | Definitions.Def_MarkovIdentityTest_Reversible_Discrepancy
-- name    : MarkovIdentityTest_Reversible_Discrepancy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:37:17.446601+00:00
-- url     : https://prove2.me/theorems/dd82a526-e8fe-4c4a-a2f1-3b663c48435f
-- title:
--   Squared Hellinger distance (no ½), the affinity matrix $A(P,Q)$, the spectral discrepancy $\Delta(P,Q)=1-\rho(A(P,Q))$, reversibility, the occupation energy $O_P(u)$ and the geometric symmetrization
-- statement:
--   States are $[n]$, written $\mathrm{Fin}\,n$ (0-based). A transition matrix is a real $n\times n$ matrix; it is **stochastic** (the referenced `CEPolytopeHard.IsStochastic`) when its entries are nonnegative and every row sums to one.
--
--   - For vectors $\mu,\nu$ on a finite set the **squared Hellinger distance** is $H^2(\mu,\nu)=1-\sum_a\sqrt{\mu_a\nu_a}$, *without* a factor $\tfrac12$ (p. 7). $H^2(P_i,Q_i)$ is the distance between row $i$ of $P$ and row $i$ of $Q$.
--   - The **affinity matrix** is $A(P,Q)_{ij}=\sqrt{P_{ij}Q_{ij}}$, and the **spectral discrepancy** is
--   $$\Delta(P,Q)=1-\rho(A(P,Q)),$$
--   where $\rho$ is the spectral radius over the *complex* spectrum (the referenced `RobustToDynamics.specRadius`: the supremum of $|z|$ over the complex eigenvalues).
--   - $P$ is **reversible with respect to $\pi$** when $\pi_i>0$ for all $i$, $\sum_i\pi_i=1$ and $\pi_iP_{ij}=\pi_jP_{ji}$ for all $i,j$ (detailed balance; together with stochasticity it makes $\pi$ stationary). $P$ is **reversible** when such a $\pi$ exists. No irreducibility, aperiodicity or lower bound on $\pi$ is part of the notion.
--   - The **square-root occupation energy** of a vector $u$ (Eq. (6.1)) is $O_P(u)=\tfrac12\sum_{i,j}\big(\sqrt{u_iP_{ij}}-\sqrt{u_jP_{ji}}\big)^2$; it is computed from $P$ and $u$ only.
--   - The **geometric symmetrization** of a square matrix $A$ is $\tilde A_{ij}=\sqrt{A_{ij}A_{ji}}$ (§6.2).
--
--   **Formalization Note.** `Real.sqrt` returns $0$ on negative input; every use has nonnegative arguments (stochastic matrices, $u\ge0$, nonnegative $A$).
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 6 (Markov chains, classes of chains), p. 7 (Hellinger affinity, A(P, Q), Eq. (2.2)), p. 31 Eq. (6.1), p. 32 (geometric symmetrization)

import Mathlib
import Definitions.Def_RobustToDynamics_specRadius
import Definitions.Def_CEPolytopeHard_IsStochastic

set_option autoImplicit false

open Finset

namespace MarkovIdentityTest.Reversible

/-- Squared Hellinger distance of two vectors on a finite set, **without** the factor `1/2`
(Jia, p. 7 / PDF 9): `H²(μ, ν) = 1 - ∑ₐ √(μ a · ν a)`. Applied to probability vectors, e.g. to
the rows `P i` and `Q i` of two stochastic matrices. -/
noncomputable def hellingerSq {α : Type*} [Fintype α] (μ ν : α → ℝ) : ℝ :=
  1 - ∑ a, Real.sqrt (μ a * ν a)

/-- The affinity matrix `A(P, Q)ᵢⱼ = √(Pᵢⱼ Qᵢⱼ)` (p. 7 / PDF 9). -/
noncomputable def affinityMatrix {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.sqrt (P i j * Q i j)

/-- The spectral discrepancy `∆(P, Q) = 1 - ρ(A(P, Q))` (Eq. (2.2), p. 7 / PDF 9), with `ρ` the
spectral radius over the complex spectrum (`RobustToDynamics.specRadius`). -/
noncomputable def discrepancy {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  1 - RobustToDynamics.specRadius (affinityMatrix P Q)

/-- `P` is reversible with respect to `π` (p. 6 / PDF 8): `π` is a strictly positive probability
vector and detailed balance `πᵢ Pᵢⱼ = πⱼ Pⱼᵢ` holds for all `i, j`. -/
def IsReversibleWrt {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) : Prop :=
  (∀ i, 0 < π i) ∧ ∑ i, π i = 1 ∧ ∀ i j, π i * P i j = π j * P j i

/-- `P` is reversible with respect to some strictly positive (stationary) distribution. -/
def IsReversible {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ π : Fin n → ℝ, IsReversibleWrt P π

/-- The square-root occupation energy (Eq. (6.1), p. 31 / PDF 33):
`O_P(u) = (1/2) ∑ᵢ ∑ⱼ (√(uᵢ Pᵢⱼ) - √(uⱼ Pⱼᵢ))²`. -/
noncomputable def occupationEnergy {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, (Real.sqrt (u i * P i j) - Real.sqrt (u j * P j i)) ^ 2

/-- The geometric symmetrization `Ãᵢⱼ = √(Aᵢⱼ Aⱼᵢ)` of a square matrix (§6.2, p. 32 / PDF 34). -/
noncomputable def geometricSymmetrization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.sqrt (A i j * A j i)

end MarkovIdentityTest.Reversible


