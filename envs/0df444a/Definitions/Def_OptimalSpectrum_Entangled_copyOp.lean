-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_copyOp
-- name    : OptimalSpectrum_Entangled_copyOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:54.671178+00:00
-- url     : https://prove2.me/theorems/a3fb04ac-06a0-4e27-ab37-aa2448c5dd5b
-- title:
--   Operator acting on one copy, $I\otimes\cdots\otimes A\otimes\cdots\otimes I$
-- statement:
--   For a copy index $i\in[n]$ and a matrix $A$ on $\mathbb C^\iota$, $A_i$ is the operator on $(\mathbb C^\iota)^{\otimes n}$ that acts as $A$ on copy $i$ and as the identity on the others. With $A=\overline\Pi$ this is the operator $\overline\Pi_i$ of the moment observables.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.1.2, p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_kronFamily

namespace OptimalSpectrum.Entangled

/-- **An operator acting on one copy.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.1.2, printed p. 21 (PDF p. 23): "Let Π̄_i denote Π̄ acting on copy i and the identity
elsewhere."

`copyOp i A` is `I ⊗ ⋯ ⊗ A ⊗ ⋯ ⊗ I` on `(ℂ^ι)^{⊗n}`, with `A` in factor `i`. -/
def copyOp {ι : Type*} [DecidableEq ι] {n : ℕ} (i : Fin n) (A : Matrix ι ι ℂ) :
    Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  kronFamily fun j => if j = i then A else 1

end OptimalSpectrum.Entangled


