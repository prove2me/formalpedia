-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_ftrunc
-- name    : GradSuffice_Thm8Data_ftrunc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:27.219501+00:00
-- url     : https://prove2.me/theorems/60cb6e70-171b-4572-a146-4daac285f587
-- title:
--   Truncations $f_{t,k}$
-- statement:
--   For a noise realization,
--   $$f_{t,k}(w):=\max_{j\le k}\max\Big\{\max_{\substack{1\le q\le D\\ j<k\text{ or }q\le t}}\Big(\frac1{16}\eta_{q,j}\cdot y_j(w)+b_{q,j}+Z_{q,j}\Big)s^{j-1},\ s^{j-1}H_j(y_j(w))\Big\}.$$
--   Thus $f_{t,k}$ keeps all pieces of the copies $j<k$, the barrier of copy $k$, and the affine pieces $q\le t$ of copy $k$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7.2, p.20

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data_affinePiece
import Definitions.Def_GradSuffice_Thm8Data_barrier
import Definitions.Def_GradSuffice_thm8S

namespace GradSuffice

/-- **The truncations `f_{t,k}`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7.2, p.20:
`f_{t,k}(w) := max_{j≤k} max{ max_{1≤q≤D, j<k or q≤t} ((1/16) η_{q,j} · y_j(w) + b_{q,j} + Z_{q,j}) s^{j−1},
s^{j−1} H_j(y_j(w)) }` — "`f_{t,k}` keeps all pieces of the copies `j < k`, the barrier of the copy
`k`, and the affine pieces `u ≤ t` of the copy `k`".

**Formalization Note.** 0-based `t`, `k`, `j`, `q`; the finite maxima over the filtered index
sets (nonempty: they contain `k`, resp. `t`) are `Finset.sup'`. -/
noncomputable def Thm8Data.ftrunc {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) (t : Fin c.D) (k : Fin c.κ)
    (Z : c.NoiseIdx → ℝ) (w : X) : ℝ :=
  (Finset.univ.filter (fun j : Fin c.κ => j ≤ k)).sup' ⟨k, by simp⟩ (fun j =>
    max ((Finset.univ.filter (fun q : Fin c.D => j < k ∨ q ≤ t)).sup' ⟨t, by simp⟩
        (fun q => c.affinePiece q j Z w * thm8S c.θ ^ (j : ℕ)))
      (thm8S c.θ ^ (j : ℕ) * c.barrier j Z w))

end GradSuffice


