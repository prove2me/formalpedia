-- Prove2me | Definitions.Def_BoundEntPPT_partialTransposeRect
-- name    : BoundEntPPT_partialTransposeRect
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:24:26.370805+00:00
-- url     : https://prove2.me/theorems/98524c1b-922c-4e83-a912-44dd45b9bfa8
-- title:
--   Partial transpose $Y^{T_B}$ on Bob's factor of an operator between different spaces (Eq. (3), footnote [20])
-- statement:
--   For an operator $Y:\mathcal H_{A,2}\otimes\mathcal H_{B,2}\to\mathcal H_{A,1}\otimes\mathcal H_{B,1}$, written as a matrix in product bases, its **partial transpose on Bob's factor** is the operator $Y^{T_B}:\mathcal H_{A,2}\otimes\mathcal H_{B,1}\to\mathcal H_{A,1}\otimes\mathcal H_{B,2}$ with entries
--
--   $$
--   \big(Y^{T_B}\big)_{(m,\nu),(n,\mu)} \;=\; Y_{(m,\mu),(n,\nu)} .
--   $$
--
--   For a square $Y$ on $\mathcal H_A\otimes\mathcal H_B$ this is the partial transposition of Eq. (3), $\varrho^{T_B}_{m\mu,n\nu}=\varrho_{m\nu,n\mu}$. The rectangular form is needed to state footnote [20], which concerns arbitrary operators $A,B,C,D$ (not necessarily square).
--
--   **Formalization Note** Taken in the computational product basis. On square matrices it agrees by definition with the published `Information100.P04.gamma`.
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, p.2, Eq. (3); p.4, footnote [20]

import Mathlib
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, p.2, Eq. (3)
(`ϱ^{T_B}_{mμ,nν} = ϱ_{mν,nμ}`) and p.4, footnote [20] ("for any operators A, B, C, D"): the
partial transposition on Bob's (second) factor of an operator
`Y : H_{A,2} ⊗ H_{B,2} → H_{A,1} ⊗ H_{B,1}` between possibly different spaces,
`Y^{T_B}_{(i, j), (i', j')} = Y_{(i, j'), (i', j)}`, an operator
`H_{A,2} ⊗ H_{B,1} → H_{A,1} ⊗ H_{B,2}`.

**Formalization Note.** Taken in the computational product basis. On square matrices it is the
published `Information100.P04.gamma` (Eq. (3)) by definition; the rectangular form is needed to
state footnote [20] for arbitrary, non-square `A, B, C, D`. -/
def partialTransposeRect {I₁ I₂ J₁ J₂ : Type*} (Y : Matrix (I₁ × J₁) (I₂ × J₂) ℂ) :
    Matrix (I₁ × J₂) (I₂ × J₁) ℂ :=
  Matrix.of fun i j => Y (i.1, j.2) (j.1, i.2)

end BoundEntPPT


