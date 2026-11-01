-- Prove2me | Definitions.Def_PfisterCEP_heisenbergGen
-- name    : PfisterCEP_heisenbergGen
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:07.584997+00:00
-- url     : https://prove2.me/theorems/a7c9dcad-4ede-412c-a968-34ca1f8cb577
-- title:
--   Heisenberg generator $x\mapsto \frac{i}{\hbar}[H,x]$
-- statement:
--   For a Hamiltonian $H$ in a complex algebra and a real $\hbar$, the **Heisenberg generator** is the map
--
--   $$x\longmapsto \frac{i}{\hbar}\,[H,x]=\frac{i}{\hbar}(Hx-xH).$$
--
--   The Heisenberg equation of motion of an operator $x$ is $\dot x=\frac{i}{\hbar}[H,x]$.
--
--   **Formalization Note** Every statement that uses the generator assumes $\hbar\neq0$.
-- source:
--   Pfister, Graph states and carrier-envelope phase squeezing, arXiv:quant-ph/0701104v2, Sec. b, p.2, left column ("the Heisenberg equations for the modes")

import Mathlib

namespace PfisterCEP

/-- **Heisenberg generator `x ↦ (i/ħ)[H, x]`.**
O. Pfister, *Graph states and carrier-envelope phase squeezing*, arXiv:quant-ph/0701104v2, Sec. b, p.2, left column ("the Heisenberg equations for the modes {an}1...N"): the
Heisenberg equation of motion is `dx/dt = (i/ħ)[H, x]`.

**Formalization Note** `ħ` is real; statements that use the generator assume `ħ ≠ 0` (at `ħ = 0`
Lean's division gives `0`). -/
noncomputable def heisenbergGen {A : Type*} [Ring A] [Algebra ℂ A] (ħ : ℝ) (H x : A) : A :=
  (Complex.I / (ħ : ℂ)) • (H * x - x * H)

end PfisterCEP


