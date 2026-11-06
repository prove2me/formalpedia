-- Prove2me | Definitions.Def_AutoQMem_Lindblad_hsAdj
-- name    : AutoQMem_Lindblad_hsAdj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:51.086553+00:00
-- url     : https://prove2.me/theorems/93106148-880c-431c-8d35-1515367704fe
-- title:
--   Heisenberg (trace-pairing) adjoint $K^*$ of a superoperator
-- statement:
--   For a superoperator $K$ from operators on one space to operators on another, the **Heisenberg adjoint** $K^*$ is defined by
--   $$\operatorname{Tr}\bigl(O\,K(\rho)\bigr)=\operatorname{Tr}\bigl(K^*(O)\,\rho\bigr)\quad\text{for all }\rho,O .$$
--   Here $K^*(O)$ is given entrywise by $K^*(O)_{yx}=\operatorname{Tr}\bigl(O\,K(|x\rangle\langle y|)\bigr)$, which is that adjoint whenever $K$ is linear.
--
--   It yields the Heisenberg propagator $\mathcal W^*(t,0)=\mathcal W_*(t,0)^*$ (eq. (43)) and the adjoint effective channel $\mathcal E_L^*$. It is not the conjugate transpose of a matrix.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), §2.2.1, p. 22 (PDF p. 24); Definition 2.18, p. 18

import Mathlib
open Matrix

namespace AutoQMem.Lindblad

/-- **Heisenberg adjoint of a superoperator.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), §2.2.1, p. 22 (PDF 24): "For a superoperator K on
B(H), its adjoint K* is defined by Tr(O K(ρ)) = Tr(K*(O) ρ) for all ρ, O."

**Formalization Note.** `hsAdj T O` has entry `(y, x)` equal to `Tr(O T(|x⟩⟨y|))`. For a
`ℂ`-linear `T` this is the unique map with `Tr(O T(ρ)) = Tr(T*(O) ρ)` for all `ρ, O` (the
trace-pairing adjoint, not the conjugate transpose of a matrix). It is also used for the Heisenberg
propagator `W^*(t, 0) := W_*(t, 0)^*` (eq. (43)) and for `E_L^*` (Definition 2.18). -/
def hsAdj {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (T : Matrix ι ι ℂ → Matrix κ κ ℂ) (O : Matrix κ κ ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun y x => (O * T (Matrix.single x y 1)).trace

end AutoQMem.Lindblad


