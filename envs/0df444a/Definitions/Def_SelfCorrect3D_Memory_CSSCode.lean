-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_CSSCode
-- name    : SelfCorrect3D_Memory_CSSCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:49.782101+00:00
-- url     : https://prove2.me/theorems/d4438d15-a924-445b-9345-a34053d0c4ac
-- title:
--   CSS code with parity checks $H_x,H_z$; stabilizers, achievable syndromes, one logical qubit
-- statement:
--   A **CSS code** on $n$ qubits is given by two parity-check matrices over $\mathbb F_2$,
--
--   $$H_x:\mathbb F_2^n\to\mathbb F_2^{m_x},\qquad H_z:\mathbb F_2^n\to\mathbb F_2^{m_z},\qquad H_xH_z^{T}=0 .$$
--
--   Row $a$ of $H_x$ gives the $X$-type stabilizer $S^X_a=X^{(H_x)_a}$ and row $b$ of $H_z$ the $Z$-type stabilizer $S^Z_b=Z^{(H_z)_b}$; the condition $H_xH_z^T=0$ makes all of them commute. Rows may be linearly dependent or zero.
--
--   The **achievable syndromes** are $\sigma_Z\in\operatorname{im}H_x$ (pattern of violated $X$-checks, caused by $Z$ errors) and $\sigma_X\in\operatorname{im}H_z$ (violated $Z$-checks, caused by $X$ errors). The code **encodes one logical qubit** when $n-\operatorname{rank}H_x-\operatorname{rank}H_z=1$, the number of encoded qubits $\dim C_x-\dim C_z^\perp$.
--
--   **Formalization Note** The CSS condition is written $H_xH_z^T=0$, the transpose of the paper's $H_zH_x^T=0$. Ranks are over $\mathbb F_2$, and the logical-qubit count is stated as $\operatorname{rank}H_x+\operatorname{rank}H_z+1=n$ to avoid truncated subtraction.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, §2.1, eq. (8), p. 10; §2.5, p. 20; Theorem 3.16 (2), p. 40

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_pauliX
import Definitions.Def_SelfCorrect3D_Memory_pauliZ
open Matrix

namespace SelfCorrect3D.Memory

/-- **CSS code given by parity-check matrices.** Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, §2.1,
eq. (8), p. 10: parity-check matrices `H_x : 𝔽₂ⁿ → 𝔽₂^{m_x}`, `H_z : 𝔽₂ⁿ → 𝔽₂^{m_z}` with
`H_z H_xᵀ = 0`; the X-type stabilizers are the rows of `H_x` and the Z-type stabilizers the rows
of `H_z`.

**Formalization Note.** The field `css` is `H_x H_zᵀ = 0`, the transpose of the paper's
`H_z H_xᵀ = 0` (equivalent). Rows may be linearly dependent or zero; no rank condition is imposed. -/
structure CSSCode (n mX mZ : ℕ) : Type where
  /-- The X parity-check matrix `H_x` (rows = X-type stabilizers). -/
  HX : Matrix (Fin mX) (Fin n) (ZMod 2)
  /-- The Z parity-check matrix `H_z` (rows = Z-type stabilizers). -/
  HZ : Matrix (Fin mZ) (Fin n) (ZMod 2)
  /-- CSS condition `H_x H_zᵀ = 0`. -/
  css : HX * HZᵀ = 0

namespace CSSCode

variable {n mX mZ : ℕ}

/-- The X-type stabilizer `S^X_a = X^{(row a of H_x)}` (§2.1, p. 10). -/
def stabX (C : CSSCode n mX mZ) (a : Fin mX) : Op n := pauliX (C.HX a)

/-- The Z-type stabilizer `S^Z_b = Z^{(row b of H_z)}` (§2.1, p. 10). -/
def stabZ (C : CSSCode n mX mZ) (b : Fin mZ) : Op n := pauliZ (C.HZ b)

/-- The achievable syndromes `σ_Z ∈ im H_x ⊆ 𝔽₂^{m_x}` of Z-type errors (violated X-checks), as a
finite set (§2.5, p. 20). -/
def achX (C : CSSCode n mX mZ) : Finset (Fin mX → ZMod 2) :=
  Finset.univ.image C.HX.mulVec

/-- The achievable syndromes `σ_X ∈ im H_z ⊆ 𝔽₂^{m_z}` of X-type errors (violated Z-checks), as a
finite set (§2.1, p. 10: "its syndrome is δ¹e_X"). -/
def achZ (C : CSSCode n mX mZ) : Finset (Fin mZ → ZMod 2) :=
  Finset.univ.image C.HZ.mulVec

/-- **The code encodes exactly one logical qubit**: `n − rank H_x − rank H_z = 1` (§2.1, p. 10:
"The number of encoded qubits is k = dim C_x − dim C_z^⊥"; Theorem 3.16 (2), p. 40).

**Formalization Note.** Ranks over `ZMod 2`; stated additively to avoid truncated subtraction. -/
def OneLogicalQubit (C : CSSCode n mX mZ) : Prop :=
  C.HX.rank + C.HZ.rank + 1 = n

end CSSCode

end SelfCorrect3D.Memory


