-- Prove2me | Definitions.Def_AutoQMem_Lindblad_flipProb
-- name    : AutoQMem_Lindblad_flipProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:25.845282+00:00
-- url     : https://prove2.me/theorems/478a3e53-e016-4ed6-a448-5475720ece6e
-- title:
--   Logical-flip probability $\Pr[b(\xi_a)\neq b(\xi_0)]$ of a sector error process
-- statement:
--   A sector process $(\chi_t)$ starts at a stored codeword $w_0$; its **error process** is $\xi_t=\chi_t\oplus w_0$, so $\xi_0=0$, and $b(\xi_t)$ is the logical-error indicator. With backward transition operator $M$, $M(a,0)_{w_0,y}=\Pr[\chi_a=y\mid\chi_0=w_0]$, the probability of a logical flip by time $a$ is
--   $$\Pr[b(\xi_a)\neq b(\xi_0)]=\sum_yM(a,0)_{w_0,y}\,\mathbf 1\bigl[b(y\oplus w_0)\neq b(0)\bigr].$$
--
--   **Formalization Note** Reading R2: the process enters only through its one-time law (50); the stored codeword $w_0$ is an explicit argument.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definitions 2.28, 2.31–2.32, eqs. (50), (52), pp. 22–24 (PDF pp. 24–26)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_decodedValue
open Matrix

namespace AutoQMem.Lindblad

/-- **Logical-flip probability of a sector error process** `Pr[b(ξ_a) ≠ b(ξ_0)]`. Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03),
Definitions 2.28, 2.31–2.32, eqs. (50), (52), pp. 22–24 (PDF 24–26): the sector process `χ_t` starts
at the stored codeword `w_0`, the error process is `ξ_t := χ_t ⊕ w_0` (so `ξ_0 = 0`), and
`b(ξ_t)` is the logical-error indicator.

**Formalization Note (Reading R2).** The process enters only through its one-time law: with `M` the
backward transition operator (`M a w₀ y = Pr[χ_a = y | χ_0 = w₀]`, eq. (50)),
`Pr[b(ξ_a) ≠ b(ξ_0)] = Σ_y M a w₀ y · [b(y + w₀) ≠ b(0)]`. One definition serves both sectors. -/
def flipProb {m n : ℕ} (M : ℝ → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ)
    (H : Matrix (Fin m) (Fin n) (ZMod 2)) (l : Fin n → ZMod 2) (D : Decoder H)
    (w0 : Fin n → ZMod 2) (a : ℝ) : ℝ :=
  ∑ y, M a w0 y * if decodedValue H l D (y + w0) ≠ decodedValue H l D 0 then 1 else 0

end AutoQMem.Lindblad


