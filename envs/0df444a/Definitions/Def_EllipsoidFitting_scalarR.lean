-- Prove2me | Definitions.Def_EllipsoidFitting_scalarR
-- name    : EllipsoidFitting_scalarR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:02.680328+00:00
-- url     : https://prove2.me/theorems/b5303445-f9f0-4981-984f-8b11806aa903
-- title:
--   The Woodbury scalars $r$, $s$, $u$
-- statement:
--   With $A$ and $\eta$ as above,
--   $$
--   r=\frac{\mathbf 1_m^\top A^{-1}\mathbf 1_m}{d},\qquad s=1+\frac{\eta^\top A^{-1}\mathbf 1_m}{d},\qquad u=-1+\frac{\eta^\top A^{-1}\eta}{d}.
--   $$
--   They are the entries of the $2\times2$ matrix $C^{-1}+U^\top A^{-1}U$ in the Woodbury identity for $M=A+UCU^\top$.
--
--   **Formalization Note** $A^{-1}$ is Lean's total matrix inverse (zero when $A$ is singular).
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Lemma 2.18, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_EllipsoidFitting_matA

set_option autoImplicit false

namespace EllipsoidFitting

open Matrix

/-- **The Woodbury scalars `r`, `s`, `u`.** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase
Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), Lemma 2.18, p.24:
"r := 1T_m A−1 1m / d , s := 1 + ηT A−1 1m / d , u := −1 + ηT A−1 η / d".

`scalarR v` is `r = 1_mᵀ A⁻¹ 1_m / d`.

**Formalization Note** `A⁻¹` is Mathlib's `Matrix.inv` (`0` when `A` is singular). -/
noncomputable def scalarR {m d : ℕ} (v : Fin m → Fin d → ℝ) : ℝ :=
  ((fun _ => (1 : ℝ)) ⬝ᵥ ((matA v)⁻¹ *ᵥ fun _ => (1 : ℝ))) / (d : ℝ)

/-- `scalarS v` is `s = 1 + ηᵀ A⁻¹ 1_m / d`. -/
noncomputable def scalarS {m d : ℕ} (v : Fin m → Fin d → ℝ) : ℝ :=
  1 + (eta v ⬝ᵥ ((matA v)⁻¹ *ᵥ fun _ => (1 : ℝ))) / (d : ℝ)

/-- `scalarU v` is `u = −1 + ηᵀ A⁻¹ η / d`. -/
noncomputable def scalarU {m d : ℕ} (v : Fin m → Fin d → ℝ) : ℝ :=
  -1 + (eta v ⬝ᵥ ((matA v)⁻¹ *ᵥ eta v)) / (d : ℝ)

end EllipsoidFitting


