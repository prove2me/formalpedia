-- Prove2me | Definitions.Def_StrategyproofMinimax_Circle_rc
-- name    : StrategyproofMinimax_Circle_rc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T20:48:27.810955+00:00
-- url     : https://prove2.me/theorems/d8acd3e4-7734-4a69-afd5-60f1aee3a8ca
-- title:
--   The random center (RC) mechanism on the circle
-- statement:
--   Let $x\in G^n$ be a location profile on the circle $G$ of circumference one, and let $\hat x_i = x_i + 1/2$ be the **antipodal point** of $x_i$. The distinct antipodal points cut the circle into arcs between adjacent antipodal points. The **random center (RC) mechanism** picks a uniformly random point $y\in G$ and returns the centre $\operatorname{cen}(\hat x_i,\hat x_j)$ of the arc between the two antipodal points adjacent to $y$. Equivalently, it returns the centre of each arc between adjacent antipodal points with probability equal to the arc's length:
--   $$\operatorname{rc}(x)=\sum_{\text{arcs } A}\ \operatorname{length}(A)\,\delta_{\operatorname{centre}(A)} .$$
--
--   In the formal definition, the arc starting at $\hat x_j$ (walking in the positive direction) has length $\ell_j$, the distance to the next antipodal point of an agent located elsewhere, or $1$ if all agents are at $x_j$. It carries weight $\ell_j$ if $j$ is the least index among the agents at $x_j$, and weight $0$ otherwise, so each arc is counted once. Its centre is $\hat x_j + \ell_j/2$.
--
--   RC is used by Mechanism 3.1 exactly when the agents are not on one semicircle. Then every arc has length less than $1/2$, so the centre along the arc is the centre of the shortest path between its endpoints.
--
--   **Formalization Note.** `rc x = ∑ j, ENNReal.ofReal (arcWeight x j) • dirac (arcCenter x j)`. This is the paper's equivalent form (p. 517), not the push-forward of the uniform measure; the two agree because the random point $y$ lands in an arc with probability equal to its length, and the paper notes that the choice at the antipodal points themselves has probability zero. The definition is total, for every $n$, and depends only on the set of locations, so coinciding agents change nothing; the profile $x\cup\{y\}$ of Lemma A.7 is `Fin.snoc x y`.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 517, Mechanism 3.1 (ii) and the equivalent form stated after it

import Mathlib

namespace StrategyproofMinimax.Circle

open MeasureTheory

/-- The antipodal point `â = a + 1/2` of `a` on the circle of circumference one (p. 515). -/
noncomputable def antipode (a : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ) :=
  a + ((1 / 2 : ℝ) : AddCircle (1 : ℝ))

/-- Length of the arc walked from `a` to `b` in the positive direction: the representative of
`b - a` in `[0, 1)`. -/
noncomputable def fwd (a b : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 (b - a) : ℝ)

/-- Length of the arc from the antipodal point `x̂ⱼ` of agent `j`, walking in the positive
direction, to the next antipodal point `x̂ₖ` of an agent located elsewhere; `1` (the whole
circle) when every agent is at `xⱼ`. -/
noncomputable def arcLength {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) (j : Fin n) : ℝ := by
  classical
  exact
    let K := Finset.univ.filter (fun k => 0 < fwd (antipode (x j)) (antipode (x k)))
    if h : K.Nonempty then K.inf' h (fun k => fwd (antipode (x j)) (antipode (x k))) else 1

/-- Probability that RC returns the centre of the arc starting at `x̂ⱼ`: the arc's length, counted
once per distinct location (only for the least index `j` among the agents at `xⱼ`). -/
noncomputable def arcWeight {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) (j : Fin n) : ℝ := by
  classical
  exact if ∀ k : Fin n, k < j → x k ≠ x j then arcLength x j else 0

/-- Centre `cen(x̂ⱼ, next antipodal point)` of the arc starting at `x̂ⱼ`. -/
noncomputable def arcCenter {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) (j : Fin n) :
    AddCircle (1 : ℝ) :=
  antipode (x j) + ((arcLength x j / 2 : ℝ) : AddCircle (1 : ℝ))

/-- `rc(x)`, the random center (RC) mechanism (p. 517, Mechanism 3.1 (ii)), in the equivalent
form the paper gives on p. 517: the antipodal points `x̂₁, …, x̂ₙ` cut the circle into arcs
between adjacent antipodal points; RC returns the centre of each such arc with probability equal
to its length. (This is the law of `cen(x̂ᵢ, x̂ⱼ)` for a uniformly random `y ∈ G` and the two
antipodal points `x̂ᵢ, x̂ⱼ` adjacent to `y`.) Defined for every profile and every `n`. -/
noncomputable def rc {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) : Measure (AddCircle (1 : ℝ)) :=
  ∑ j, ENNReal.ofReal (arcWeight x j) • Measure.dirac (arcCenter x j)

end StrategyproofMinimax.Circle


