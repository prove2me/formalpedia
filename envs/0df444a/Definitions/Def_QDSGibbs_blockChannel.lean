-- Prove2me | Definitions.Def_QDSGibbs_blockChannel
-- name    : QDSGibbs_blockChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:36:24.43884+00:00
-- url     : https://prove2.me/theorems/dafb8bff-c483-4bd9-96d1-b4e9d41b4a32
-- title:
--   Jump map $\mathcal T_B$, loss operator $S_B$, coherent term $G_B$, Bohr calculus, block generator $\mathcal K_B$ and block channel $\Phi_B(T)$
-- statement:
--   With the QBP operator $O=O_B$, the **jump map** and **loss operator** are
--
--   $$
--   \mathcal T_B=\mathrm{Ad}_{O}\circ\mathcal R_B\circ\mathrm{Ad}_{O^{-1}},\qquad S_B=\mathcal T_B^*(\mathbb 1)=O^{-*}\mathcal R_B^*(O^*O)O^{-1},
--   $$
--
--   where $\mathrm{Ad}_D(X)=DXD^*$. For Hermitian $K$, the **Bohr calculus** is $q(\mathrm{ad}_K)(A)=\sum_{E,E'}q(E-E')P_EAP_{E'}$ and the **coherent map** is $\mathcal G_K(A)=\frac i2\tanh(\frac\beta4\mathrm{ad}_K)(A)$. The **coherent term** is $G_B=\mathcal G_H(S_B)$, the **block generator**
--
--   $$
--   \mathcal K_B(X)=\mathcal T_B(X)-\tfrac12\{S_B,X\}-i[G_B,X],
--   $$
--
--   and the **smoothed heat-bath block update** is $\Phi_B(T)=e^{T\mathcal K_B}$. With the region $\Omega=C_u(B)$ in place of $\Lambda$ (in the QBP path and in $\mathcal G_{H_\Omega}$) the same formulas give the localized $\mathcal T_{B,u}$, $S_{B,u}$, $G_{B,u}$, $\mathcal K_{B,u}$, $\Phi_{B,u}(T)$ of §5.2.
--
--   **Formalization Note** The jump map is written basis-free; it equals $\sum_aL_{B,a}XL_{B,a}^*$ by (3.13). The closed form of $S_B$ is the Hilbert–Schmidt adjoint of $\mathcal T_B$ at $\mathbb 1$ (checked in a verification file: $\mathrm{Tr}(S_BX)=\mathrm{Tr}\,\mathcal T_B(X)$). The Bohr calculus is computed in an eigenbasis and does not depend on it. Matrix inverse is Mathlib's (zero on singular matrices; $O_B$ is invertible by Proposition 3.2).
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), (2.7), p.12; p.18; (3.14), p.19; p.42; (5.13), p.43

import Mathlib
import Definitions.Def_QDSGibbs_qbpOp
import Definitions.Def_QDSGibbs_IsChannel

open scoped Matrix

namespace QDSGibbs

/-- The **jump map** `T_B = Ad_{O_B} ∘ R_B ∘ Ad_{O_B^{-1}}`, `Ad_D(X) = D X D^*` (arXiv:2610.03578,
held file sha256 ede55815…, (3.14), p.19; `T_{B,u}` of p.42 for `Ω = C_u(B)`), with
`O = qbpOp β I B Ω`.

**Formalization Note** The basis-free form `X ↦ O R_B(O^{-1} X O^{-*}) O^*`; it equals
`Σ_a L_{B,a} X L_{B,a}^*` by (3.13). `⁻¹` is Mathlib's matrix inverse (`0` for a singular matrix;
`O_B` is invertible, Proposition 3.2). -/
noncomputable def jumpMap {N : ℕ} {d : Fin N → ℕ} (β : ℝ) (I : Interaction d) (B Ω : Finset (Fin N))
    (X : Op d) : Op d :=
  qbpOp β I B Ω * resetMap β I B ((qbpOp β I B Ω)⁻¹ * X * ((qbpOp β I B Ω)⁻¹)ᴴ) * (qbpOp β I B Ω)ᴴ

/-- The **loss operator** `S_B = T_B^*(1) = O^{-*} R_B^*(O^* O) O^{-1}` (arXiv:2610.03578, (3.14),
p.19; proof of Lemma 3.5, p.20; `S_{B,u}` of p.42 for `Ω = C_u(B)`).

**Formalization Note** The closed form of the Hilbert–Schmidt adjoint of `T_B` evaluated at `1`, from
`Tr[Y T_B(X)] = Tr[T_B^*(Y) X]`. -/
noncomputable def sOp {N : ℕ} {d : Fin N → ℕ} (β : ℝ) (I : Interaction d) (B Ω : Finset (Fin N)) :
    Op d :=
  ((qbpOp β I B Ω)⁻¹)ᴴ * resetAdj β I B ((qbpOp β I B Ω)ᴴ * qbpOp β I B Ω) * (qbpOp β I B Ω)⁻¹

/-- The **Bohr-frequency functional calculus** `q(ad_K)(A) = Σ_{E,E′} q(E − E′) P_E A P_{E′}`
(arXiv:2610.03578, (2.7), p.12) of a Hermitian `K`.

**Formalization Note** Computed in an eigenbasis `K = U diag(λ) U^*`:
`U [q(λ_a − λ_b) (U^* A U)_{ab}] U^*`; the result does not depend on the eigenbasis. For a
non-Hermitian `K` the value is `0` (never used: it is applied only to Hermitian Hamiltonians). -/
noncomputable def bohrCalc {n : Type} [Fintype n] [DecidableEq n] (K : Matrix n n ℂ) (q : ℝ → ℂ)
    (A : Matrix n n ℂ) : Matrix n n ℂ :=
  if hK : K.IsHermitian then
    (hK.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.of (fun a b => q (hK.eigenvalues a - hK.eigenvalues b) *
        (((hK.eigenvectorUnitary : Matrix n n ℂ))ᴴ * A * (hK.eigenvectorUnitary : Matrix n n ℂ)) a b) *
      ((hK.eigenvectorUnitary : Matrix n n ℂ))ᴴ
  else 0

/-- The **coherent map** `G_K(A) = (i/2) tanh((β/4) ad_K)(A)` (arXiv:2610.03578, p.18). -/
noncomputable def qbpG {n : Type} [Fintype n] [DecidableEq n] (β : ℝ) (K A : Matrix n n ℂ) :
    Matrix n n ℂ :=
  bohrCalc K (fun ω => Complex.I / 2 * (Real.tanh (β / 4 * ω) : ℂ)) A

/-- The **coherent term** `G_B = G_H(S_B)` (arXiv:2610.03578, (3.14), p.19) for `Ω = univ`
(`H_Λ = H`), and `G_{B,u} = G_{H_{C_u(B)}}(S_{B,u})` (p.42) for `Ω = C_u(B)`. -/
noncomputable def gOp {N : ℕ} {d : Fin N → ℕ} (β : ℝ) (I : Interaction d) (B Ω : Finset (Fin N)) :
    Op d :=
  qbpG β (hamOn I Ω) (sOp β I B Ω)

/-- The **block generator** `K_B(X) = T_B(X) − ½{S_B, X} − i[G_B, X]` (arXiv:2610.03578, (3.14),
p.19; for `Ω = C_u(B)` the localized `K_{B,u}` of (5.13), p.43). -/
noncomputable def blockGen {N : ℕ} {d : Fin N → ℕ} (β : ℝ) (I : Interaction d)
    (B Ω : Finset (Fin N)) (X : Op d) : Op d :=
  jumpMap β I B Ω X - (1 / 2 : ℂ) • (sOp β I B Ω * X + X * sOp β I B Ω) -
    Complex.I • (gOp β I B Ω * X - X * gOp β I B Ω)

/-- The **smoothed heat-bath block update** `Φ_B(T) = e^{T K_B}` (arXiv:2610.03578, (3.14), p.19;
`Φ_{B,u}(T) = e^{T K_{B,u}}` of (5.13) for `Ω = C_u(B)`). -/
noncomputable def blockChannel {N : ℕ} {d : Fin N → ℕ} (β : ℝ) (I : Interaction d)
    (B Ω : Finset (Fin N)) (T : ℝ) : Op d → Op d :=
  sexp (blockGen β I B Ω) T

end QDSGibbs


