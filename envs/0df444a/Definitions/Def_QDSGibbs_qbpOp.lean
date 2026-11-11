-- Prove2me | Definitions.Def_QDSGibbs_qbpOp
-- name    : QDSGibbs_qbpOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:35:28.839562+00:00
-- url     : https://prove2.me/theorems/ce8f5d08-be70-440c-9a8e-58054abcca76
-- title:
--   Block reset $\mathcal R_B$, QBP kernel $p_\beta$, transform $\mathcal F_K$, and the QBP operator $O_B$
-- statement:
--   For a block $B$, the **reset** replaces the state on $B$ by the local Gibbs state $\sigma^B_\beta=e^{-\beta H_B}/\mathrm{Tr}\,e^{-\beta H_B}$:
--
--   $$
--   \mathcal R_B(X)=\sigma^B_\beta\otimes\mathrm{Tr}_BX .
--   $$
--
--   Its Hilbert–Schmidt adjoint is $\mathcal R_B^*(Y)=\mathbb 1_B\otimes\mathrm{Tr}_B(\sigma^B_\beta Y)$. The **QBP kernel** and **transform** are
--
--   $$
--   p_\beta(t)=\frac{4}{\beta\pi}\log\coth\frac{\pi|t|}{\beta}\ (t\ne0),\qquad \mathcal F_K(A)=\int_{\mathbb R}p_\beta(t)\,e^{itK}Ae^{-itK}\,dt .
--   $$
--
--   The **QBP operator** $O_B(u)$ solves
--
--   $$
--   O_B'(u)=-\frac\beta4\,\mathcal F_{H_\Omega-(1-u)W_{\partial B}}(W_{\partial B})\,O_B(u),\qquad O_B(0)=\mathbb 1,
--   $$
--
--   and $O_B=O_B(1)$. For $\Omega=\Lambda$ the path is $H^0_B+uW_{\partial B}$ (the paper's (3.6)); for $\Omega=C_u(B)$ it is the localized path of p.41, giving $O_{B,u}$.
--
--   **Formalization Note** $\mathcal R_B(X)=(\dim\mathcal H_{B^c}/\mathrm{Tr}E)\,E\,\mathrm{ptr}_B(X)$ with $E=e^{-\beta H_B}\otimes\mathbb 1$. The integral is the entrywise Bochner integral. The ODE solution is chosen with `Classical.epsilon` among solutions on all of $\mathbb R$; it exists and is unique (continuous coefficients). The kernel's value at $t=0$ is immaterial.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), (3.1), p.15; (3.2), p.16; (3.6), p.17; p.41

import Mathlib
import Definitions.Def_QDSGibbs_Interaction

open scoped Matrix

namespace QDSGibbs

/-- The **block reset** `R_B(X) = σ^B_β ⊗ Tr_B X`, `σ^B_β = e^{−βH_B} / Tr e^{−βH_B}`
(arXiv:2610.03578, held file sha256 ede55815…, (3.1), p.15).

**Formalization Note** With `E = e^{−βH_B} ⊗ 1_{B^c}` (the exponential of the full-space `H_B`),
`Tr E = Tr(e^{−βH_B}) · dim H_{B^c}`, so `σ^B_β ⊗ 1_{B^c} = (dim H_{B^c} / Tr E) · E` and
`R_B(X) = (dim H_{B^c} / Tr E) · E · ptr B X`. -/
noncomputable def resetMap {N : ℕ} {d : Fin N → ℕ} (β : ℝ) (I : Interaction d) (B : Finset (Fin N))
    (X : Op d) : Op d :=
  (((dimOf d Bᶜ : ℕ) : ℂ) / (NormedSpace.exp ((-β) • hamOn I B)).trace) •
    (NormedSpace.exp ((-β) • hamOn I B) * ptr B X)

/-- The Hilbert–Schmidt adjoint `R_B^*(Y) = 1_B ⊗ Tr_B(σ^B_β Y)` of the reset (arXiv:2610.03578,
proof of Lemma 3.5, p.20; proof of Lemma 5.5, p.42), in the full-space form
`(dim H_{B^c} / Tr E) · ptr B (Y E)`. -/
noncomputable def resetAdj {N : ℕ} {d : Fin N → ℕ} (β : ℝ) (I : Interaction d) (B : Finset (Fin N))
    (Y : Op d) : Op d :=
  (((dimOf d Bᶜ : ℕ) : ℂ) / (NormedSpace.exp ((-β) • hamOn I B)).trace) •
    ptr B (Y * NormedSpace.exp ((-β) • hamOn I B))

/-- The **QBP kernel** `p_β(t) = (4/(βπ)) log coth(π|t|/β)` (arXiv:2610.03578, (3.2), p.16), for
`t ≠ 0`.

**Formalization Note** `coth = cosh / sinh`. The value at `t = 0` (here `0`) is immaterial: the kernel
is only integrated. -/
noncomputable def qbpKernel (β t : ℝ) : ℝ :=
  4 / (β * Real.pi) *
    Real.log (Real.cosh (Real.pi * |t| / β) / Real.sinh (Real.pi * |t| / β))

/-- The **QBP transform** `F_K(A) = ∫_ℝ p_β(t) τ^K_t(A) dt`, `τ^K_t(A) = e^{itK} A e^{−itK}`
(arXiv:2610.03578, (3.2), p.16; (2.6), p.11).

**Formalization Note** The Bochner integral is taken entrywise (ℂ-valued); this is the matrix
integral. The integrand is integrable for `β > 0` and Hermitian `K` (unitary conjugation, integrable
kernel). -/
noncomputable def qbpF {n : Type} [Fintype n] [DecidableEq n] (β : ℝ) (K A : Matrix n n ℂ) :
    Matrix n n ℂ :=
  Matrix.of fun x y => ∫ t : ℝ, (qbpKernel β t : ℂ) *
    (NormedSpace.exp ((Complex.I * (t : ℂ)) • K) * A * NormedSpace.exp ((-(Complex.I * (t : ℂ))) • K)) x y

/-- The **QBP interpolation path** `H_Ω − (1 − u) W_∂B` (arXiv:2610.03578, (3.6), p.17; Figure 1
caption, p.4; p.41).

**Formalization Note** `Ω = univ` gives `H − (1−u)W_∂B = H⁰_B + u W_∂B = H_B(u)`; `Ω = C_u(B)` gives
the localized path `H_{C_u(B)} − (1−θ) W_∂B` of p.41. -/
noncomputable def qbpPath {N : ℕ} {d : Fin N → ℕ} (I : Interaction d) (B Ω : Finset (Fin N))
    (u : ℝ) : Op d :=
  hamOn I Ω - (1 - u) • cross I B

/-- The **QBP operator path** `u ↦ O_B(u)`: the solution of
`O′(u) = −(β/4) F_{path(u)}(W_∂B) O(u)`, `O(0) = 1` (arXiv:2610.03578, (3.6), p.17), with
`path = qbpPath I B Ω`.

**Formalization Note** Chosen by `Classical.epsilon` among the solutions on all of `ℝ` (derivatives
entrywise). The coefficient is continuous in `u`, so this linear ODE has a unique global solution,
whose restriction to `[0,1]` is the paper's. -/
noncomputable def qbpPathOp {N : ℕ} {d : Fin N → ℕ} (β : ℝ) (I : Interaction d)
    (B Ω : Finset (Fin N)) : ℝ → Op d :=
  Classical.epsilon fun O : ℝ → Op d => O 0 = 1 ∧
    ∀ (u : ℝ) (x y : Cfg d), HasDerivAt (fun s => O s x y)
      (((-(β / 4)) • qbpF β (qbpPath I B Ω u) (cross I B) * O u) x y) u

/-- The **QBP operator** `O_B = O_B(1)` (arXiv:2610.03578, (3.6), p.17); with `Ω = C_u(B)` it is the
localized operator `O_{B,u}` of p.41. -/
noncomputable def qbpOp {N : ℕ} {d : Fin N → ℕ} (β : ℝ) (I : Interaction d) (B Ω : Finset (Fin N)) :
    Op d :=
  qbpPathOp β I B Ω 1

end QDSGibbs


