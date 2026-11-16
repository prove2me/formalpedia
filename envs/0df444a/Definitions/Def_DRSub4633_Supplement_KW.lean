-- Prove2me | Definitions.Def_DRSub4633_Supplement_KW
-- name    : DRSub4633_Supplement_KW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:31:15.888333+00:00
-- url     : https://prove2.me/theorems/60d7551b-0263-47be-acba-50e11233d75c
-- title:
--   The width-normalized set $K_W$, Eq. (100)
-- statement:
--   Let $w_i$ be the coordinate widths of $K\subseteq[0,1]^n$. The paper deletes the coordinates of zero width, keeps the remaining $n'$, sets $W=\operatorname{diag}(w_1,\dots,w_{n'})$ and defines
--   $$K_W=\{z\in[0,1]^{n'} : Wz\in K\},$$
--   with deleted coordinates reinserted as zeros in $Wz$. Here $K_W$ is represented inside $\mathbb R^n$ as
--   $$\{z\in[0,1]^n : z_i=0\text{ whenever }w_i=0,\ (w_1z_1,\dots,w_nz_n)\in K\}.$$
--
--   **Formalization Note** The deleted coordinates are kept and fixed at $0$ instead of being removed. The Euclidean projection onto this set is the paper's projection onto $K_W$ on the kept coordinates, and $0$ on the deleted ones.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 6.2, Eq. (100), pp.35–36

import Mathlib
import Definitions.Def_DRSub4633_Supplement_width

namespace DRSub4633.Supplement

/-- **The width-normalized set `K_W`, Eq. (100).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 6.2, Eq. (100), pp.35–36:
"fixes the coordinates of zero width at zero, relabels the remaining `n′` coordinates, and sets
`W = diag(w₁, …, w_{n′})`, `K_W = {z ∈ [0, 1]^{n′} : Wz ∈ K}` … where deleted coordinates
are reinserted as zeros in `Wz`."

`KW K` is the set of `z ∈ [0,1]ⁿ` whose zero-width coordinates vanish and with
`(w₁z₁, …, wₙzₙ) ∈ K`.

**Formalization Note.** The paper's `K_W` lives in `[0,1]^{n′}` after deleting the `n − n′`
zero-width coordinates. Here it is embedded in `ℝⁿ` with those coordinates fixed at `0`; the
map `Wz` with zero rows for deleted coordinates is `(wᵢzᵢ)ᵢ`. The Euclidean projection onto this
embedded set is the paper's projection onto `K_W` on the kept coordinates and `0` on the deleted
ones, so a projection oracle for one gives the other with free scalar computation. -/
noncomputable def KW {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {z | (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ (∀ i, width K i = 0 → z i = 0) ∧
    WithLp.toLp 2 (fun i => width K i * z i) ∈ K}

end DRSub4633.Supplement


