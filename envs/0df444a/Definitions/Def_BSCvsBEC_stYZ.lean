-- Prove2me | Definitions.Def_BSCvsBEC_stYZ
-- name    : BSCvsBEC_stYZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:34:30.060252+00:00
-- url     : https://prove2.me/theorems/89fe9bcf-4a17-4db8-a8bd-a06a9926652a
-- title:
--   Quantum side information and the marginals $\sigma_{YZ},\sigma_{XZ},\sigma_Z,\sigma_{X_RZ}$
-- statement:
--   **Quantum side information** on a register $Z=\mathbb C^\zeta$ is a family $(P_x)_x$ of positive semidefinite matrices on $Z$ with
--   $$\operatorname{Tr}\Big(\sum_x P_x\Big)=1$$
--   (the total trace is $1$; individual traces are not normalized). Together with channel output vectors $|v_x\rangle$ it defines the state
--   $$\sigma_{XYZ}=\sum_x|x\rangle\langle x|\otimes|v_x\rangle\langle v_x|\otimes P_x,$$
--   whose marginals are
--   $$\sigma_{YZ}=\sum_x|v_x\rangle\langle v_x|\otimes P_x,\qquad \sigma_{XZ}=\sum_x|x\rangle\langle x|\otimes P_x,\qquad \sigma_Z=\sum_x P_x,$$
--   and, when $x\in\Omega^n$ and $R\subseteq[n]$, $\sigma_{X_RZ}=\sum_x|x_R\rangle\langle x_R|\otimes P_x$.
--
--   For the $n$-fold pure state channel the labels are $x\in\Omega^n$ and $v_x=|\omega_x\rangle$; for one symbol (Theorem 4.2, Claim 4.3) the labels are the symbols and $v_b=|\omega_b\rangle$. The case of a one-dimensional $Z$ is the basic scenario $\sigma_{XY}$.
--
--   **Formalization Note** Tensor products are Kronecker products in the order $X$, $Y$, $Z$; the marginals are written directly as these sums.
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), §2.3, eq. (27), p.7; Theorem 4.2, eq. (99), p.19; §4.1, p.20

import Mathlib
import Definitions.Def_BSCvsBEC_condEntPSC

open scoped ComplexOrder

namespace BSCvsBEC

/-- Quantum side information on a register `Z = ℂ^ζ`: a family `(P_x)_x` of positive semidefinite
matrices with `Tr(∑ₓ P_x) = 1`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.3, eq. (27), p.7:
"`P_x ⪰ 0, Tr(∑_{x∈Ωⁿ} P_x) = 1`".

**Formalization Note.** The trace condition is on the sum (total trace `1`), not on each `P_x`. -/
def IsSideInfo {L ζ : Type*} [Fintype L] [Fintype ζ] (P : L → Matrix ζ ζ ℂ) : Prop :=
  (∀ x, (P x).PosSemidef) ∧ (∑ x, P x).trace = 1

/-- The marginal `σ_YZ = ∑ₓ |v_x⟩⟨v_x| ⊗ P_x` of the side-information state
`σ_XYZ = ∑ₓ |x⟩⟨x| ⊗ |v_x⟩⟨v_x| ⊗ P_x` (eq. (27), p.7; eq. (99), p.19).

**Formalization Note.** For the `n`-fold channel, labels are `x : Fin n → Ω` and `v = pscVec ω`;
for one symbol (Theorem 4.2, Claim 4.3) labels are the symbols and `v x = ω x`. -/
noncomputable def stYZ {L κ ζ : Type*} [Fintype L] (v : L → κ → ℂ) (P : L → Matrix ζ ζ ℂ) :
    Matrix (κ × ζ) (κ × ζ) ℂ :=
  ∑ x, Matrix.kronecker (ketbra (v x)) (P x)

/-- The marginal `σ_XZ = ∑ₓ |x⟩⟨x| ⊗ P_x` of `σ_XYZ` (eq. (27), p.7). -/
noncomputable def stXZ {L ζ : Type*} [Fintype L] [DecidableEq L] (P : L → Matrix ζ ζ ℂ) :
    Matrix (L × ζ) (L × ζ) ℂ :=
  ∑ x, Matrix.kronecker (Matrix.diagonal (Pi.single x 1)) (P x)

/-- The marginal `σ_Z = ∑ₓ P_x` of `σ_XYZ` (eq. (27), p.7). -/
noncomputable def stZ {L ζ : Type*} [Fintype L] (P : L → Matrix ζ ζ ℂ) : Matrix ζ ζ ℂ :=
  ∑ x, P x

/-- The marginal `σ_{X_R Z} = ∑ₓ |x_R⟩⟨x_R| ⊗ P_x` of `σ_XYZ` on the coordinates `R ⊆ [n]` of `X`
and on `Z` (Lemma 2.3, eq. (29), p.8). -/
noncomputable def stXRZ {Ω ζ : Type*} [Fintype Ω] [DecidableEq Ω] {n : ℕ} (R : Finset (Fin n))
    (P : (Fin n → Ω) → Matrix ζ ζ ℂ) : Matrix ((↥R → Ω) × ζ) ((↥R → Ω) × ζ) ℂ :=
  ∑ x, Matrix.kronecker (Matrix.diagonal (Pi.single (fun i : ↥R => x i) 1)) (P x)

end BSCvsBEC


