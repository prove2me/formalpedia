-- Prove2me | Definitions.Def_LindbladShallow_transducer
-- name    : LindbladShallow_transducer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:10:22.666283+00:00
-- url     : https://prove2.me/theorems/d256f7c3-716b-49b0-bc3c-08f19225dafb
-- title:
--   The weighted Cayley transducer $S_\Theta$ and its catalyst
-- statement:
--   For a cell space $\mathcal H$, Hermitian $K$ and $0\preceq\Theta\preceq I$, with the private space $\mathbb C^2_Q\otimes\mathcal H$:
--   $$O=\begin{pmatrix}K&\sqrt{I-K^2}\\\sqrt{I-K^2}&-K\end{pmatrix},\quad q_0=\begin{pmatrix}I\\0\end{pmatrix},\quad P=q_0q_0^\dagger,\quad t=(I-\Theta)(I+\Theta)^{-1},\quad b=2\sqrt\Theta(I+\Theta)^{-1},$$
--   $$R_\Theta=\begin{pmatrix}t&-ibq_0^\dagger\\q_0b&i(I-P+q_0tq_0^\dagger)\end{pmatrix},\quad S_\Theta=R_\Theta(I\oplus O),$$
--   $$H_\Theta=\sqrt\Theta K\sqrt\Theta,\quad D_\Theta=I+iH_\Theta,\quad V_\Theta=(I-iH_\Theta)D_\Theta^{-1},\quad \gamma=(I+iO)q_0\sqrt\Theta D_\Theta^{-1}.$$
--
--   These are the objects of Lemma 4.1, the transducer that realizes a physical Cayley gate on vacuum and occupied baths.
--
--   **Formalization Note** $\mathbb C^2_Q\otimes\mathcal H$ is written $\mathcal H\oplus\mathcal H$ (first summand $Q=0$). Square roots are by continuous functional calculus.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), §4.1, pp.23–24

import Mathlib

open scoped Matrix ComplexOrder

namespace LindbladShallow

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The positive square root `√A` of a matrix by continuous functional calculus (`cfc Real.sqrt`). -/
noncomputable def msqrt (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc Real.sqrt A

/-- The reflection `O := [[K, √(I − K²)], [√(I − K²), −K]]` on the private space `ℂ²_Q ⊗ ℋ_cell`
(arXiv:2610.05362, held version sha256 8f4637ef…, §4.1, p.23).

**Formalization Note** `ℂ²_Q ⊗ ℋ_cell` is written as `ℋ_cell ⊕ ℋ_cell`, the first summand being
`Q = 0` (`|0⟩_Q ⊗ x ↦ inl x`). -/
noncomputable def transO (K : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks K (msqrt (1 - K * K)) (msqrt (1 - K * K)) (-K)

/-- `q₀ := (I; 0)`, `q₀x = |0⟩_Q ⊗ x` (p.23). -/
def q0 : Matrix (ι ⊕ ι) ι ℂ := Matrix.fromRows 1 0

/-- `t := (I − Θ)(I + Θ)^{−1}` (p.23). -/
noncomputable def transT (Θ : Matrix ι ι ℂ) : Matrix ι ι ℂ := (1 - Θ) * (1 + Θ)⁻¹

/-- `b := 2√Θ(I + Θ)^{−1}` (p.23). -/
noncomputable def transB (Θ : Matrix ι ι ℂ) : Matrix ι ι ℂ := (2 : ℂ) • msqrt Θ * (1 + Θ)⁻¹

/-- `R_Θ := [[t, −ib q₀†], [q₀ b, i(I − P + q₀ t q₀†)]]`, `P := q₀q₀†`, on public ⊕ private (p.24). -/
noncomputable def transR (Θ : Matrix ι ι ℂ) : Matrix (ι ⊕ (ι ⊕ ι)) (ι ⊕ (ι ⊕ ι)) ℂ :=
  let Q : Matrix (ι ⊕ ι) ι ℂ := q0
  let Qd : Matrix ι (ι ⊕ ι) ℂ := Matrix.conjTranspose Q
  Matrix.fromBlocks (transT Θ) ((-Complex.I) • (transB Θ * Qd)) (Q * transB Θ)
    (Complex.I • ((1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) - Q * Qd + Q * transT Θ * Qd))

/-- The weighted Cayley transducer `S_Θ := R_Θ (I ⊕ O)` (p.24). -/
noncomputable def transS (K Θ : Matrix ι ι ℂ) : Matrix (ι ⊕ (ι ⊕ ι)) (ι ⊕ (ι ⊕ ι)) ℂ :=
  transR Θ * Matrix.fromBlocks 1 0 0 (transO K)

/-- `H_Θ := √Θ K √Θ` (p.24). -/
noncomputable def transH (K Θ : Matrix ι ι ℂ) : Matrix ι ι ℂ := msqrt Θ * K * msqrt Θ

/-- `D_Θ := I + iH_Θ` (p.24). -/
noncomputable def transD (K Θ : Matrix ι ι ℂ) : Matrix ι ι ℂ := 1 + Complex.I • transH K Θ

/-- `V_Θ := (I − iH_Θ) D_Θ^{−1}` (Lemma 4.1, p.24). -/
noncomputable def transV (K Θ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 - Complex.I • transH K Θ) * (transD K Θ)⁻¹

/-- The catalyst `γ := (I + iO) q₀ √Θ D_Θ^{−1}` (p.24). -/
noncomputable def transGamma (K Θ : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) ι ℂ :=
  let Q : Matrix (ι ⊕ ι) ι ℂ := q0
  ((1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) + Complex.I • transO K) * Q * msqrt Θ * (transD K Θ)⁻¹

end LindbladShallow


