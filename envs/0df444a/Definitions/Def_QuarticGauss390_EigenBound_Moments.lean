-- Prove2me | Definitions.Def_QuarticGauss390_EigenBound_Moments
-- name    : QuarticGauss390_EigenBound_Moments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:37.873597+00:00
-- url     : https://prove2.me/theorems/6313cfdc-84be-4e35-9f49-633a9bd7bb76
-- title:
--   Def. 2.1–2.2 — quadratic moments $\mu^X$, quartic moment matrix $M^X$, $Q_x$, $H_A$, variance, coefficient matrix $C^R$
-- statement:
--   Let $E=\{(i,j):1\le i<j\le d\}$, $m=\binom d2$, and $q_{ij}=i\,c_ic_j$. For $x\in\mathbb R^E$ and a real symmetric $m\times m$ coefficient matrix $A$,
--   $$Q_x=\sum_{p\in E}x_pq_p,\qquad H_A=\sum_{p,r\in E}A_{pr}\,q_pq_r .$$
--   For a Hermitian operator $X$ on $\mathcal H$, the **quadratic moments** and the **quartic moment matrix** are
--   $$\mu^X=(\operatorname{Tr}[Xq_p])_{p\in E},\qquad M^X=(\operatorname{Re}\operatorname{Tr}[Xq_pq_r])_{p,r\in E}.$$
--   For a density matrix $\rho$ the **variance** of $Q$ is $\operatorname{Var}_\rho(Q)=\langle(Q-\langle Q\rangle_\rho I)^2\rangle_\rho$; for a state, $\rho=|\psi\rangle\langle\psi|$.
--
--   For a homogeneous quartic $R$, the **coefficient matrix** is
--   $$C^R=M^{2^{-n}R}.$$
--
--   Moment matrices are dual to coefficient matrices through the trace pairing; they carry the paper's main approximation argument.
--
--   **Formalization Note.** $E$ is the subtype of pairs $(i,j)$ in `Fin (2n) × Fin (2n)` with $i<j$. $\mu^X$ and the variance take real parts; both are real for Hermitian arguments. The Lean formulas also define $H_A$ for nonsymmetric $A$ and moments for non-Hermitian $X$; the source and the theorems use symmetric $A$ and Hermitian $X$. The identities $s^2=\sum r_S^2$ and $H_{C^R}/6=R$ are not part of the definition (Claim 2.3 states them).
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.6, Definition 2.1, eq. (2.2); p.7, eq. (2.5), Definition 2.2

import Mathlib
import Definitions.Def_QuarticGauss390_EigenBound_CAR

open Matrix

namespace QuarticGauss390.EigenBound

/-- Def. 2.1, p.6: the index set `E = {(i, j) : i < j}` of Majorana pairs (`m = C(d, 2)`
elements). -/
abbrev Pair (n : ℕ) := {p : Fin (2 * n) × Fin (2 * n) // p.1 < p.2}

/-- Def. 2.1, p.6: quadratic Majorana operators `q_{ij} = i c_i c_j`. -/
noncomputable def qOp {n : ℕ} (C : CAR n) (p : Pair n) : Op n :=
  Complex.I • (C.c p.1.1 * C.c p.1.2)

/-- eq. (2.2), p.6: `Q_x = ∑_p x_p q_p` for `x ∈ ℝ^E`. -/
noncomputable def quadHam {n : ℕ} (C : CAR n) (x : Pair n → ℝ) : Op n :=
  ∑ p, (x p : ℂ) • qOp C p

/-- eq. (2.2), p.6: `H_A = qᵀ A q = ∑_{p,r} A_{pr} q_p q_r` for an `m × m` coefficient matrix. -/
noncomputable def coefHam {n : ℕ} (C : CAR n) (A : Matrix (Pair n) (Pair n) ℝ) : Op n :=
  ∑ p, ∑ r, (A p r : ℂ) • (qOp C p * qOp C r)

/-- Def. 2.1, p.6: vector of quadratic moments `μ^X = (Tr[X q_p])_p` (real part taken; the
trace is real for Hermitian `X`). -/
noncomputable def quadMoments {n : ℕ} (C : CAR n) (X : Op n) : Pair n → ℝ :=
  fun p => (X * qOp C p).trace.re

/-- Def. 2.1, p.6: quartic moment matrix `M^X = (Re Tr[X q_p q_r])_{p,r}`. -/
noncomputable def momentMatrix {n : ℕ} (C : CAR n) (X : Op n) : Matrix (Pair n) (Pair n) ℝ :=
  Matrix.of fun p r => (X * qOp C p * qOp C r).trace.re

/-- eq. (2.5), p.7: `Var_ρ(Q) = ⟨(Q - ⟨Q⟩_ρ I)²⟩_ρ` (real part taken). -/
noncomputable def variance {n : ℕ} (ρ Q : Op n) : ℝ :=
  (expect ρ ((Q - expect ρ Q • (1 : Op n)) * (Q - expect ρ Q • (1 : Op n)))).re

/-- Def. 2.2, p.7: coefficient matrix `C^R = M^{2^{-n} R}`. -/
noncomputable def coefMatrix {n : ℕ} (C : CAR n) (R : Op n) : Matrix (Pair n) (Pair n) ℝ :=
  momentMatrix C (((2 : ℂ) ^ n)⁻¹ • R)

end QuarticGauss390.EigenBound


