-- Prove2me | Definitions.Def_AutoQMem_Lindblad_LogicalQubit_PhiX__43fab1
-- name    : AutoQMem_Lindblad_LogicalQubit_PhiX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:37.383432+00:00
-- url     : https://prove2.me/theorems/43fab170-f1dc-475c-a0a7-154f69f469a3
-- title:
--   Classical representation maps $\Phi_X$, $\Phi_Z$ and logical-error phases $\Lambda_X$, $\Lambda_Z$
-- statement:
--   With the bare logical functions $x_{\mathrm{bare}}(e)=(-1)^{\ell_X\cdot e}$ and $z_{\mathrm{bare}}(e)=(-1)^{\ell_Z\cdot e}$, the **classical representation maps** send sector-subspace operators to functions on error vectors:
--   $$[\Phi_X(\bar XA)](e)=x_{\mathrm{bare}}(e)\,A(H_Xe),\qquad [\Phi_Z(\bar ZB)](e)=z_{\mathrm{bare}}(e)\,B(H_Ze),$$
--   for $A\in\mathcal A_X$, $B\in\mathcal A_Z$, extended linearly. The **logical-error phases** are $\Lambda_X=\Phi_X(T_X)$ and $\Lambda_Z=\Phi_Z(T_Z)$.
--
--   **Formalization Note** $\Phi_X(O)(e)$ is defined for every operator as $(-1)^{\ell_X\cdot e}\,(\bar XO)(H_Xe)$ with $(\cdot)(s)$ the syndrome eigenvalue; on $O=\bar XA$ this is the formula above because $\bar X^2=I$. Values are complex: $\mathcal A_X$ is a complex algebra, and on Hermitian $A$ the values are real (the paper writes $\mathbb R^{\Omega_X}$).
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definitions 4.7–4.9, eqs. (89)–(91), (94), p. 35 (PDF p. 37)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_TX
import Definitions.Def_AutoQMem_Lindblad_CSSCode_eigX
open Matrix

namespace AutoQMem.Lindblad

namespace LogicalQubit

variable {n' mX mZ : ℕ} {C : CSSCode (n' + 1) mX mZ}

/-- **Classical representation map `Φ_X`.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definitions 4.7–4.8, eqs. (89)–(90), p. 35
(PDF 37): `x_bare(e) := (−1)^{ℓ_X·e}` and `[Φ_X(X̄A)](e) = x_bare(e) A(H_X e)` for `A ∈ A_X`,
"and extend linearly".

**Formalization Note.** `Φ_X(O)(e) := (−1)^{ℓ_X·e} · (X̄ O)(H_X e)`, with `(·)(s)` the syndrome
eigenvalue `eigX`. On `O = X̄A`, `A ∈ A_X`, this is `x_bare(e) A(H_X e)` because `X̄² = I`; it
is linear in `O`. The values are complex (the paper writes `ℝ^{Ω_X}`; `A_X` is a complex algebra
and `Φ_X` is extended linearly; on Hermitian `A` the values are real). -/
noncomputable def PhiX (Q : LogicalQubit C) (O : Op (n' + 1)) (e : Fin (n' + 1) → ZMod 2) : ℂ :=
  (-1 : ℂ) ^ (Q.lX ⬝ᵥ e).val * C.eigX (pauliX Q.lX * O) (C.HX *ᵥ e)

/-- **Classical representation map `Φ_Z`** (Definitions 4.7–4.8, eqs. (89), (91)):
`Φ_Z(O)(e) := (−1)^{ℓ_Z·e} · (Z̄ O)(H_Z e)`, i.e. `z_bare(e) B(H_Z e)` on `O = Z̄B`, `B ∈ A_Z`. -/
noncomputable def PhiZ (Q : LogicalQubit C) (O : Op (n' + 1)) (e : Fin (n' + 1) → ZMod 2) : ℂ :=
  (-1 : ℂ) ^ (Q.lZ ⬝ᵥ e).val * C.eigZ (pauliZ Q.lZ * O) (C.HZ *ᵥ e)

/-- **Logical-error phase** `Λ_X := Φ_X(T_X)` (Definition 4.9, eq. (94), p. 35). -/
noncomputable def LambdaX (Q : LogicalQubit C) (DX : Decoder C.HX) (e : Fin (n' + 1) → ZMod 2) : ℂ :=
  Q.PhiX (Q.TX DX) e

/-- **Logical-error phase** `Λ_Z := Φ_Z(T_Z)` (Definition 4.9, eq. (94), p. 35). -/
noncomputable def LambdaZ (Q : LogicalQubit C) (DZ : Decoder C.HZ) (e : Fin (n' + 1) → ZMod 2) : ℂ :=
  Q.PhiZ (Q.TZ DZ) e

end LogicalQubit

end AutoQMem.Lindblad


