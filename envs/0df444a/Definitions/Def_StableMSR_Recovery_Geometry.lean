-- Prove2me | Definitions.Def_StableMSR_Recovery_Geometry
-- name    : StableMSR_Recovery_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:16.629862+00:00
-- url     : https://prove2.me/theorems/0f7f381f-a4e7-4b9b-a16b-7b55b6c861ea
-- title:
--   Closed balls, components, and derived recovery scales
-- statement:
--   For an original finite metric $d$, the ball $B(x,s)$ contains exactly the points at distance at most $s$. The graph $G_s[W]$ joins distinct points of $W$ at distance at most $s$. Connected components are nonempty subsets of $W$.
--
--   Set distance and the analysis scales are
--   $$
--   \operatorname{dist}(A,B)=\min_{a\in A,b\in B}d(a,b),\quad
--   R=\max_{C\in\mathcal O}r(C),\quad b=\varepsilon R/4,
--   $$
--   $$
--   \mathcal T=\{C\in\mathcal O:r(C)\ge b\},\quad
--   M=\sum_{C\in\mathcal T}r(C),\quad \rho=\varepsilon M/4.
--   $$
--   Small clusters have radius strictly less than $b$. The meeting operator counts clusters intersecting a set. All scales are computed from the analysis partition; none is input advice to an algorithm.
--
--   These definitions support separation, component recovery, and density estimates. **Formalization Note** Set distance takes values in `EReal` and is $+\infty$ if either set is empty. Empty diameter is zero. Finite maxima have a zero convention on the empty family; structural applications have a nonempty feasible optimum. The graph tests both orientations, which coincide on every metric input.
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), pp. 4, 6–7, §3 notation and §3.2; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Model

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

noncomputable def ball {n : ℕ} (d : Point n → Point n → ℝ) (x : Point n) (s : ℝ) : Cluster n :=
  Finset.univ.filter (fun y => d x y ≤ s)

/-- Complete-lattice infimum: +infinity if either set is empty. -/
noncomputable def setDistance {n : ℕ} (d : Point n → Point n → ℝ)
    (A B : Cluster n) : EReal :=
  sInf {v : EReal | ∃ x ∈ A, ∃ y ∈ B, v = (d x y : EReal)}

noncomputable def diameter {n : ℕ} (d : Point n → Point n → ℝ) (W : Cluster n) : ℝ :=
  if h : W.Nonempty then W.sup' h (eccentricity d W) else 0

/-- For a symmetric array these are exactly the source's induced threshold edges. -/
noncomputable def thresholdGraph {n : ℕ} (d : Point n → Point n → ℝ)
    (s : ℝ) (W : Cluster n) : SimpleGraph (Point n) where
  Adj x y := x ≠ y ∧ x ∈ W ∧ y ∈ W ∧ d x y ≤ s ∧ d y x ≤ s
  symm := ⟨by intro x y h; exact ⟨Ne.symm h.1, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

noncomputable def component {n : ℕ} (d : Point n → Point n → ℝ)
    (s : ℝ) (W : Cluster n) (x : Point n) : Cluster n :=
  W.filter (fun y => (thresholdGraph d s W).Reachable x y)

noncomputable def components {n : ℕ} (d : Point n → Point n → ℝ)
    (s : ℝ) (W : Cluster n) : Partition n := W.image (component d s W)

noncomputable def largestRadius {n : ℕ} (d : Point n → Point n → ℝ) (O : Partition n) : ℝ :=
  if h : O.Nonempty then O.sup' h (radius d) else 0

noncomputable def smallThreshold {n : ℕ} (d : Point n → Point n → ℝ)
    (O : Partition n) (ε : ℝ) : ℝ := ε * largestRadius d O / 4

noncomputable def largeClusters {n : ℕ} (d : Point n → Point n → ℝ)
    (O : Partition n) (ε : ℝ) : Partition n := O.filter (fun C => smallThreshold d O ε ≤ radius d C)

noncomputable def smallClusters {n : ℕ} (d : Point n → Point n → ℝ)
    (O : Partition n) (ε : ℝ) : Partition n := O.filter (fun C => radius d C < smallThreshold d O ε)

noncomputable def largeMass {n : ℕ} (d : Point n → Point n → ℝ)
    (O : Partition n) (ε : ℝ) : ℝ := cost d (largeClusters d O ε)

noncomputable def densityScale {n : ℕ} (d : Point n → Point n → ℝ)
    (O : Partition n) (ε : ℝ) : ℝ := ε * largeMass d O ε / 4

noncomputable def meeting {n : ℕ} (Q : Partition n) (A : Cluster n) : Partition n :=
  Q.filter (fun C => (C ∩ A).Nonempty)

end StableMSR.Recovery


