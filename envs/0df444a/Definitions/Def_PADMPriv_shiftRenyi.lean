-- Prove2me | Definitions.Def_PADMPriv_shiftRenyi
-- name    : PADMPriv_shiftRenyi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:04.761939+00:00
-- url     : https://prove2.me/theorems/b3592ff6-d414-4f49-81ac-7d82f9468ff7
-- title:
--   Shifted Rényi divergence $R_\alpha(P_z,a)$ (Definition A2)
-- statement:
--   For a distribution $P_z$ on $\mathbb R^m$, $\alpha>1$ and $a\ge0$,
--   $$
--   R_\alpha(P_z,a) = \sup_{\|r\|_2\le a} D_\alpha(z+r\,\|\,z),\qquad z\sim P_z.
--   $$
--   It measures how much a shift of size at most $a$ can be detected through the noise; for $N(0_m,\frac{\sigma^2}{4}I_m)$ it equals $2\alpha a^2/\sigma^2$.
--
--   **Formalization Note** The law of $z+r$ is the image of $P_z$ under $z\mapsto z+r$; the supremum is taken in the extended reals.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Definition A2, p.23

import Mathlib
import Definitions.Def_PADMPriv_renyiDiv

namespace PADMPriv

open MeasureTheory

/-- The shifted Rényi divergence `R_α(P_z, a) = sup_{‖r‖₂ ≤ a} D_α(z + r ‖ z)`, `z ∼ P_z`,
Definition A2 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.23.

**Formalization Note** The law of `z + r` is the image of `P_z` under `z ↦ z + r`; the supremum is
taken in `EReal`. -/
noncomputable def shiftRenyi {m : ℕ} (α : ℝ) (Pz : Measure (EuclideanSpace ℝ (Fin m))) (a : ℝ) :
    EReal :=
  ⨆ (r : EuclideanSpace ℝ (Fin m)) (_ : ‖r‖ ≤ a), renyiDiv α (Pz.map (fun z => z + r)) Pz

end PADMPriv


