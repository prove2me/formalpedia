-- Prove2me | Definitions.Def_EuclidDiamStream_diamGap
-- name    : EuclidDiamStream_diamGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:25.70043+00:00
-- url     : https://prove2.me/theorems/a52e8278-698f-4dd9-971e-489d47cf784a
-- title:
--   Support, diameter $\mathrm{diam}(v)$ and the partial function $\mathrm{diam}_{r,c,n}(v)\in\{0,1,*\}$
-- statement:
--   For a frequency vector $v$ on the grid, $\mathrm{supp}(v)$ is the set of points $x$ with $v_x\ne0$, and the **diameter** is
--   $$\mathrm{diam}(v)=\max\{\|x-y\|_2:x,y\in\mathrm{supp}(v)\}.$$
--   The partial function $\mathrm{diam}_{r,c,n}$ takes the value $0$ if $\mathrm{diam}(v)\le r$ and $|\mathrm{supp}(v)|\le n$, the value $1$ if $\mathrm{diam}(v)\ge cr$ and $|\mathrm{supp}(v)|\le n$, and the value $*$ otherwise.
--
--   This function is the decision problem that both streaming algorithms and linear sketches must solve.
--
--   **Formalization Note** The value $*$ is `none` and the bits are `some false` and `some true`. The first test takes precedence, which matters only outside $r>0$, $c>1$, where the mission never evaluates it. On the zero vector the maximum ranges over the empty set, and the diameter is $0$.
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), pp.6–7, Def. 2.1

import Mathlib
import Definitions.Def_EuclidDiamStream_Point

namespace EuclidDiamStream

/-- The support `supp(v)` of a frequency vector, its non-zero coordinates: Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), §2, p.6. -/
def supp {d Δ : ℕ} (v : Point d Δ → ℤ) : Finset (Point d Δ) :=
  Finset.univ.filter (fun x => v x ≠ 0)

/-- The diameter `diam(v) = max{‖x − y‖₂ : x, y ∈ supp(v)}`, §2, p.6.

**Formalization Note.** The real `sSup` is over a finite set, so it is the maximum when the support is
nonempty. On the zero vector the source's maximum ranges over the empty set; the `sSup` returns `0`, the
usual diameter of the empty set. -/
noncomputable def diam {d Δ : ℕ} (v : Point d Δ → ℤ) : ℝ :=
  sSup ((fun p : Point d Δ × Point d Δ => euclidDist p.1 p.2) '' (↑(supp v ×ˢ supp v) : Set _))

open Classical in
/-- The partial function `diam_{r,c,n}(v) ∈ {0, 1, ∗}` of Definition 2.1, pp.6–7: `some false` (= 0) if
`diam(v) ≤ r` and `|supp(v)| ≤ n`; `some true` (= 1) if `diam(v) ≥ cr` and `|supp(v)| ≤ n`; `none` (= ∗)
otherwise.

**Formalization Note.** The first test takes precedence. For `r > 0` and `c > 1`, the only values used
in the mission, the two tests exclude each other, so the order does not matter there. -/
noncomputable def diamGap {d Δ : ℕ} (r c : ℝ) (n : ℕ) (v : Point d Δ → ℤ) : Option Bool :=
  if diam v ≤ r ∧ (supp v).card ≤ n then some false
  else if c * r ≤ diam v ∧ (supp v).card ≤ n then some true
  else none

end EuclidDiamStream


