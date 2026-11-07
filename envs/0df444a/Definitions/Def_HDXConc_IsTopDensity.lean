-- Prove2me | Definitions.Def_HDXConc_IsTopDensity
-- name    : HDXConc_IsTopDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:22.066128+00:00
-- url     : https://prove2.me/theorems/519739f1-8ab9-4e3d-b6ca-f8a6937788c2
-- title:
--   Top density $\pi_d$ and the induced measures $\pi_k$
-- statement:
--   Let $X$ be a pure $d$-dimensional complex (`SteurerHDX.IsPure`), with levels $X(k)$ (`SteurerHDX.faces`), where the dimension of a face is its number of vertices. A **top density** is a probability density $\pi_d$ on $X(d)$ with $\pi_d(s)>0$ for every $s\in X(d)$. It induces on each level the measure obtained by sampling $t\sim\pi_d$ and then a uniformly random $k$-subset $s\subseteq t$:
--
--   $$\pi_k(s)=\frac{1}{\binom{d}{k}}\sum_{t\in X(d),\,t\supseteq s}\pi_d(t).$$
--
--   These measures, in particular the vertex marginal $\pi_1$ and the edge marginal $\pi_2$, give the means and the walk operators used in the mission.
--
--   **Formalization Note.** A density is a function on all of `Finset V` that is only read on $X(d)$. The paper's codomain $(0,1]$ follows from positivity and total mass one. Total mass one also makes $X(d)$ nonempty, which excludes the empty collection that `SteurerHDX.IsPure` allows on its own.
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), §2.2 "Probability density over a simplicial complex", p.12

import Mathlib
import Definitions.Def_SteurerHDX_faces

namespace HDXConc

/-!
# The top density `π_d` and the induced measures `π_k`

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission
(manuscript sha256 ea5bee5f…), §2.2 "Probability density over a simplicial complex", p.12.

**Formalization Note.** A density is a function `Finset V → ℝ` that is only ever read on `X(d)`. The paper
writes `π_d : X(d) → (0, 1]`; the bound by `1` follows from positivity and total mass `1`.
Total mass `1` also makes `X(d)` nonempty, which excludes the empty collection that `SteurerHDX.IsPure` allows.
-/

/-- `π` is a probability density on the top level `X(d)`, positive at every top face (p.12). -/
structure IsTopDensity {V : Type*} (X : Finset (Finset V)) (d : ℕ) (π : Finset V → ℝ) : Prop where
  /-- `π_d(s) > 0` for `s ∈ X(d)`. -/
  pos : ∀ s ∈ SteurerHDX.faces X d, 0 < π s
  /-- `π_d` has total mass `1` on `X(d)`. -/
  sum_eq_one : ∑ s ∈ SteurerHDX.faces X d, π s = 1

/-- The induced measure `π_k(s) = (1 / (d choose k)) ∑_{t ∈ X(d), t ⊇ s} π_d(t)` (p.12). -/
noncomputable def faceMeasure {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ)
    (π : Finset V → ℝ) (k : ℕ) (s : Finset V) : ℝ :=
  (1 / (d.choose k : ℝ)) * ∑ t ∈ (SteurerHDX.faces X d).filter (fun t => s ⊆ t), π t

end HDXConc


