-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_ftruncBar
-- name    : GradSuffice_Thm8Data_ftruncBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:45.517213+00:00
-- url     : https://prove2.me/theorems/c536c505-5e61-494c-88a9-8f9d79b7bf2f
-- title:
--   Averaged truncations $\bar f_{t,k}=\mathbb E_Z[f_{t,k}]$
-- statement:
--   The averaged truncation is $\bar f_{t,k}(w):=\mathbb E_Z[f_{t,k}(w)]$, the expectation over the auxiliary noise. Lemma 1 compares it with $\bar f$, and the sessions of §7.2 answer queries with $(\bar f_{t,k},\nabla\bar f_{t,k})$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7.2, pp.20–21

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data_ftrunc
import Definitions.Def_GradSuffice_Thm8Data_noiseLaw

namespace GradSuffice

/-- **The averaged truncations `f̄_{t,k} := E_Z[f_{t,k}]`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7.2, pp.20–21 (Lemma 1 and
the sessions use `f̄_{t,k}`, the noise average of `f_{t,k}`). -/
noncomputable def Thm8Data.ftruncBar {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) (t : Fin c.D) (k : Fin c.κ)
    (w : X) : ℝ :=
  ∫ Z, c.ftrunc t k Z w ∂c.noiseLaw

end GradSuffice


