-- Prove2me | Definitions.Def_UCalibDirichlet_dir
-- name    : UCalibDirichlet_dir
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:18.959992+00:00
-- url     : https://prove2.me/theorems/acd760ae-5c0b-468b-8c5e-9aabee3ea253
-- title:
--   Dirichlet law $\mathrm{Dir}(a)$ with the zero-parameter convention
-- statement:
--   For a parameter vector $a\in\mathbb R^K_{\ge 0}$, $\mathrm{Dir}(a)$ is the Dirichlet distribution on the probability simplex
--   $$\Delta_K=\{p\in\mathbb R^K_{\ge0}:\ \|p\|_1=1\}.$$
--   When all $a_j>0$ it is the law of $(X_j/\sum_k X_k)_{j}$ for independent $X_j\sim\mathrm{Gamma}(a_j,1)$. When some coordinates of $a$ vanish, the paper's convention applies: sample from the lower-dimensional Dirichlet distribution of the nonzero coordinates and set the remaining coordinates of $P$ to $0$. In particular $\mathrm{Dir}(a_{-i})$, where $a_{-i}$ replaces the $i$-th coordinate of $a$ by $0$, is a law on the face $\{r\in\Delta_K: r_i=0\}$.
--
--   This is the forecast law of Algorithm 1 and the law under which the Dirichlet potential $\Lambda_F$ and the curvature $W^i_F$ are averaged.
--
--   **Formalization Note** The law is built from the published Dirichlet law `NestedCRP.dirichletMeasure` on the index set $\{j: a_j>0\}$, pushed forward to $\mathbb R^K$ by extension by zero. The wrapper is needed because Mathlib's Gamma law with shape $0$ is the zero measure. The value at $a=0$ is irrelevant (never used).
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), §1.1, p.2 (zero-parameter convention); Algorithm 1, p.3

import Mathlib
import Definitions.Def_NestedCRP_dirichletMeasure

open MeasureTheory

namespace UCalibDirichlet

/-- **The Dirichlet law `Dir(a)` for a parameter vector `a ∈ ℝ^K_{≥0}`, with the paper's
zero-parameter convention.** Frongillo, Luo, Mehta & Schneider, *Near-Optimal Regret in
U-Calibration for Every Proper Loss* (manuscript, STOC 2027 submission), §1.1, p.2: "when
`a ∈ ℝ_{≥0}` has some components equal to 0, we use the convention that sampling `P ∼ Dir(a)`
means sampling from the lower-dimensional Dirichlet distribution induced from the non-zero
components of `a` and then setting the other coordinates of `P` to zero." Used in Algorithm 1
(p.3), in (7) (p.4) and, with `a_{−i}`, in (11) (p.5).

`dir a` is the published law `NestedCRP.dirichletMeasure` (the law of normalized independent
`Gamma(a_j, 1)` variables) over the index set `{j // 0 < a j}`, pushed forward to `Fin K → ℝ` by
extension by zero.

**Formalization Note.** For `a` with all coordinates positive this is `Dir(a)` on the simplex
`Δ_K ⊆ Fin K → ℝ`. The wrapper exists because Mathlib's `gammaMeasure 0 1` is the zero measure, so
the published law applied directly to a vector with a zero coordinate would be the zero measure.
`Dir(a_{−i})` is `dir (Function.update a i 0)`. The value at `a = 0` (all coordinates zero) is the
Dirac mass at `0`, which is not a law on the simplex; the paper never uses `Dir(0)`, and no
statement of this development does. -/
noncomputable def dir {K : ℕ} (a : Fin K → ℝ) : Measure (Fin K → ℝ) :=
  (NestedCRP.dirichletMeasure (fun j : {j : Fin K // 0 < a j} => a j)).map
    (fun x j => if h : 0 < a j then x ⟨j, h⟩ else 0)

end UCalibDirichlet


