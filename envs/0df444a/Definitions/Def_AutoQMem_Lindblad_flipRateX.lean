-- Prove2me | Definitions.Def_AutoQMem_Lindblad_flipRateX
-- name    : AutoQMem_Lindblad_flipRateX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:50.305834+00:00
-- url     : https://prove2.me/theorems/f1a2afc6-8831-48e3-9471-e4b03767fba3
-- title:
--   Flip-rate operators $\Gamma^{(X)}_i$, $\Gamma^{(Z)}_i$
-- statement:
--   For a family of syndrome functions $f_{P,i,\alpha}$ (Pauli label $P$, qubit $i$, finite index $\alpha$), the **flip-rate operators** are
--   $$\Gamma^{(X)}_i=\sum_\alpha\bigl(f_{Z,i,\alpha}^\dagger f_{Z,i,\alpha}+f_{Y,i,\alpha}^\dagger f_{Y,i,\alpha}\bigr),\qquad \Gamma^{(Z)}_i=\sum_\alpha\bigl(f_{X,i,\alpha}^\dagger f_{X,i,\alpha}+f_{Y,i,\alpha}^\dagger f_{Y,i,\alpha}\bigr).$$
--   $\Gamma^{(X)}_i$ collects the jumps that flip qubit $i$ in the X sector (Pauli factor $Z_i$ or $Y_i$); a $Y_i$ jump enters both.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.22, eq. (32), p. 20 (PDF p. 22)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Op
import Definitions.Def_AutoQMem_Lindblad_Pauli1
open Matrix

namespace AutoQMem.Lindblad

/-- **X-sector flip-rate operator** `Γ^{(X)}_i := Σ_α (f_{Z,i,α}† f_{Z,i,α} + f_{Y,i,α}† f_{Y,i,α})`.
Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.22, eq. (32), p. 20 (PDF 22). The X sector is flipped by physical Z and Y jumps.

**Formalization Note.** `f i P α` is the syndrome function `f_{P,i,α}` (at a fixed time). -/
noncomputable def flipRateX {n : ℕ} {ι : Type} [Fintype ι] (f : Fin n → Pauli1 → ι → Op n)
    (i : Fin n) : Op n :=
  ∑ α, ((f i .Z α)ᴴ * f i .Z α + (f i .Y α)ᴴ * f i .Y α)

/-- **Z-sector flip-rate operator** `Γ^{(Z)}_i := Σ_α (f_{X,i,α}† f_{X,i,α} + f_{Y,i,α}† f_{Y,i,α})`
(Definition 2.22, eq. (32)). -/
noncomputable def flipRateZ {n : ℕ} {ι : Type} [Fintype ι] (f : Fin n → Pauli1 → ι → Op n)
    (i : Fin n) : Op n :=
  ∑ α, ((f i .X α)ᴴ * f i .X α + (f i .Y α)ᴴ * f i .Y α)

end AutoQMem.Lindblad


