-- Prove2me | Definitions.Def_MultiParamQEC_SDP
-- name    : MultiParamQEC_SDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:38:45.521535+00:00
-- url     : https://prove2.me/theorems/4fbbbfaa-d7c8-4ddf-ae7c-c5c21c809b37
-- title:
--   The code matrix $Q$ (25), the program (26) and the corrected SDP (8)
-- statement:
--   Let $\mathbb 1_d/\sqrt d,\{G_i\}_{i=1}^P,\{S_i\}_{i=1}^m,\{R_i\}_{i=1}^r$ be Hermitian $d\times d$ matrices and let the reference space $\mathcal H_R=\mathrm{span}\{|0\rangle,\dots,|P\rangle\}$ have indices $0,\dots,P$.
--
--   1. For Hermitian $(P+1)\times(P+1)$ matrices $G^R_1,\dots,G^R_P$, $B_1,\dots,B_r$ and reals $\nu_1,\dots,\nu_m$, the **code matrix** on $\mathcal H_R\otimes\mathcal H_S$ is
--   $$Q=\mathbb 1_{P+1}\otimes\frac{\mathbb 1_d}{d}+\sum_{i=1}^P(G^R_i)^T\otimes G_i+\sum_{i=1}^m\nu_i\,\mathbb 1_{P+1}\otimes S_i+\sum_{i=1}^rB_i\otimes R_i ,$$
--   and $(G^R,B,\nu)$ is **feasible** when $Q\ge0$.
--   2. $\Gamma$ is the real $P\times P$ matrix $\Gamma_{ij}=\mathrm{Im}[G^R_j]_{i0}$, $i,j=1,\dots,P$.
--   3. The **program (26)** has values $\mathrm{Tr}(W(\Gamma^T\Gamma)^{-1})$ over feasible points with $\Gamma$ invertible.
--   4. The **corrected SDP (8)** has values $\mathrm{Tr}\,Y$ over feasible $(G^R,B,\nu)$ and real $P\times P$ matrices $K,Y$ with
--   $$\begin{pmatrix}Y&K\\K&\mathbb 1_P\end{pmatrix}\ge0,\qquad\begin{pmatrix}K&\mathbb 1_P\\\mathbb 1_P&\Gamma\sqrt{W^{-1}}\end{pmatrix}\ge0 .$$
--   The printed (8) has the block $w\mathbb 1_P$ in place of $Y$ and the value $P\cdot w$ in place of $\mathrm{Tr}\,Y$.
--   5. For a real $P\times P$ matrix $O$, the **reference rotation** $\mathbb 1\oplus O$ fixes $|0\rangle$ and acts by $O$ on $|1\rangle,\dots,|P\rangle$; a matrix $A$ on $\mathcal H_R$ is rotated to $(\mathbb 1\oplus O)A(\mathbb 1\oplus O)^T$.
--
--   These objects turn the optimization over codes and input states into a semidefinite program.
--
--   **Formalization Note** $Q$ is indexed by `Fin (P+1) × Fin d`, reference space first, and carries the transposes $(G^R_i)^T$, not the adjoints. Index $0$ of `Fin (P+1)` is the input state and parameter index $i\in\{1,\dots,P\}$ is `Fin.succ i`. The matrix $\sqrt{W^{-1}}$ enters as an argument `Rw`; the theorems require it to be the positive semidefinite square root. In (3) $\Gamma$ is required invertible so that $(\Gamma^T\Gamma)^{-1}$ is a genuine inverse.
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Theorem 2, p.4–5, display (8); Sec. 4.2.2, p.8, Eqs. (25)–(26); Sec. 4.2.3, p.9

import Mathlib
import Definitions.Def_MultiParamQEC_JNTQEC

open scoped ComplexOrder Matrix Kronecker

namespace MultiParamQEC

/-!
# The code matrix `Q`, the pre-SDP (26) and the corrected SDP (8)

Górecki–Zhou–Jiang–Demkowicz-Dobrzański, *Optimal probes and error-correction schemes in
multi-parameter quantum metrology*, arXiv:1901.00896v4, Theorem 2 (p.4, display (8) on p.5),
Eqs. (25)–(26) (p.8) and Sec. 4.2.3 (p.9).

The reference space `H_R = span{|0⟩, …, |P⟩}` has index `Fin (P + 1)`; index `0` is the input
state `|c_0⟩`, and the parameter index `i ∈ {1, …, P}` is `Fin.succ i` for `i : Fin P`. The
matrix `Q` acts on `H_R ⊗ H_S`, index `Fin (P + 1) × Fin d`, **reference space first**, and
carries the transposes `(G^R_i)ᵀ` (not the adjoints).

**Formalization Note.** `Γ_ij = Im[G^R_j]_{i0}` for `i, j = 1, …, P` is
`gammaMatrix GR i j = (GR j i.succ 0).im`. The matrix `√(W⁻¹)` is passed as an argument `Rw`
which the theorems require to be the positive semidefinite square root (`Rw.PosSemidef`,
`Rw * Rw = W⁻¹`); that root is unique. In the corrected SDP the scalar block `w 1_P` of the
printed (8) is replaced by a real `P × P` matrix `Y` and the objective `P · w` by `Tr Y`.
-/

variable {d P m r : ℕ}

/-- The code matrix of Eq. (25) (arXiv:1901.00896v4, p.8; first constraint of (8), p.5):
`Q = 1_{P+1} ⊗ 1_d/d + Σ_i (G^R_i)ᵀ ⊗ G_i + Σ_i ν_i 1_{P+1} ⊗ S_i + Σ_i B_i ⊗ R_i`. -/
noncomputable def qMatrix (G : Fin P → Matrix (Fin d) (Fin d) ℂ)
    (S : Fin m → Matrix (Fin d) (Fin d) ℂ) (R : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (GR : Fin P → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ)
    (B : Fin r → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ) (ν : Fin m → ℝ) :
    Matrix (Fin (P + 1) × Fin d) (Fin (P + 1) × Fin d) ℂ :=
  (1 : Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ) ⊗ₖ (((d : ℂ)⁻¹) • (1 : Matrix (Fin d) (Fin d) ℂ)) +
  ∑ i, (GR i)ᵀ ⊗ₖ G i +
  ∑ i, ((ν i : ℝ) : ℂ) • ((1 : Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ) ⊗ₖ S i) +
  ∑ i, B i ⊗ₖ R i

/-- `(G^R, B, ν)` is feasible for (25)/(26): `G^R_i` and `B_i` Hermitian `(P+1) × (P+1)` matrices,
`ν_i ∈ ℝ`, and `Q ≥ 0`. -/
def IsCodeFeasible (G : Fin P → Matrix (Fin d) (Fin d) ℂ) (S : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (R : Fin r → Matrix (Fin d) (Fin d) ℂ) (GR : Fin P → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ)
    (B : Fin r → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ) (ν : Fin m → ℝ) : Prop :=
  (∀ i, (GR i).IsHermitian) ∧ (∀ i, (B i).IsHermitian) ∧ (qMatrix G S R GR B ν).PosSemidef

/-- `Γ_ij = Im[G^R_j]_{i0}`, `i, j = 1, …, P` (arXiv:1901.00896v4, (8) p.5 and (26) p.8). -/
def gammaMatrix (GR : Fin P → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ) : Matrix (Fin P) (Fin P) ℝ :=
  Matrix.of fun i j => (GR j i.succ 0).im

/-- The values `Tr(W(ΓᵀΓ)⁻¹)` of the program (26) (arXiv:1901.00896v4, p.8) over feasible
`(G^R, B, ν)` with `Γ` invertible (so that `(ΓᵀΓ)⁻¹` is a genuine inverse, not the junk `0`). -/
noncomputable def preSdpSet (G : Fin P → Matrix (Fin d) (Fin d) ℂ)
    (S : Fin m → Matrix (Fin d) (Fin d) ℂ) (R : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (W : Matrix (Fin P) (Fin P) ℝ) : Set ℝ :=
  {t | ∃ (GR : Fin P → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ)
      (B : Fin r → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ) (ν : Fin m → ℝ),
      IsCodeFeasible G S R GR B ν ∧ (gammaMatrix GR).det ≠ 0 ∧
      t = (W * ((gammaMatrix GR)ᵀ * gammaMatrix GR)⁻¹).trace}

/-- The objective values `Tr Y` of the **corrected** SDP (8) (arXiv:1901.00896v4, p.5): over
feasible `(G^R, B, ν)` and real `P × P` matrices `K, Y` with
`[[Y, K], [K, 1_P]] ≥ 0` and `[[K, 1_P], [1_P, Γ√(W⁻¹)]] ≥ 0`; `Rw` stands for `√(W⁻¹)`.
The printed (8) has `w 1_P` in place of `Y` and objective `P · w`. -/
def sdpSet (G : Fin P → Matrix (Fin d) (Fin d) ℂ) (S : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (R : Fin r → Matrix (Fin d) (Fin d) ℂ) (Rw : Matrix (Fin P) (Fin P) ℝ) : Set ℝ :=
  {t | ∃ (GR : Fin P → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ)
      (B : Fin r → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ) (ν : Fin m → ℝ)
      (K Y : Matrix (Fin P) (Fin P) ℝ),
      IsCodeFeasible G S R GR B ν ∧ (Matrix.fromBlocks Y K K 1).PosSemidef ∧
      (Matrix.fromBlocks K 1 1 (gammaMatrix GR * Rw)).PosSemidef ∧ t = Y.trace}

/-- The real orthogonal rotation `1 ⊕ O` of the reference basis that fixes `|0⟩` and acts by `O`
on `|1⟩, …, |P⟩` (arXiv:1901.00896v4, Sec. 4.2.3, p.9). -/
def refRotation (O : Matrix (Fin P) (Fin P) ℝ) : Matrix (Fin (P + 1)) (Fin (P + 1)) ℝ :=
  Matrix.of fun k l =>
    Fin.cases (motive := fun _ => ℝ) (Fin.cases (motive := fun _ => ℝ) 1 (fun _ => 0) l)
      (fun i => Fin.cases (motive := fun _ => ℝ) 0 (fun j => O i j) l) k

/-- A reference-space matrix after the rotation: `A ↦ (1 ⊕ O) A (1 ⊕ O)ᵀ`. -/
noncomputable def rotateRef (O : Matrix (Fin P) (Fin P) ℝ)
    (A : Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ) : Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ :=
  (refRotation O).map (fun x : ℝ => (x : ℂ)) * A * ((refRotation O).map (fun x : ℝ => (x : ℂ)))ᵀ

end MultiParamQEC


