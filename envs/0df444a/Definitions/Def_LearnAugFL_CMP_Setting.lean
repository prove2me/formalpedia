-- Prove2me | Definitions.Def_LearnAugFL_CMP_Setting
-- name    : LearnAugFL_CMP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:03.361912+00:00
-- url     : https://prove2.me/theorems/beef870d-3bab-48f2-ae20-2b0c1ff6c04e
-- title:
--   §2, §4.1, §4.4, pp. 5–6, 12–13, 19 — Euclidean plane, utilitarian cost, optimal location, lower median, CMP, ratio, half-axes, COA/OA/CA families
-- statement:
--   This file sets up the single-facility location model in the Euclidean plane and the Coordinatewise Median with Predictions (CMP) mechanism, together with the instance families used in the paper's worst-case analysis.
--
--   1. **Plane and cost.** Points live in $\mathbb R^2$ with the Euclidean distance $d$. A profile $P=(p_1,\dots,p_n)$ lists the agents' preferred locations. The utilitarian social cost of a facility location $f$ is
--   $$C^u(f,P)=\frac1n\sum_{i=1}^n d(f,p_i).$$
--   A location $o$ is *optimal* for $P$ if $C^u(o,P)\le C^u(z,P)$ for every $z\in\mathbb R^2$.
--
--   2. **Lower median.** For a finite multiset of $m$ reals, the lower median is its $\lceil m/2\rceil$-th smallest element (the smaller of the two medians when $m$ is even).
--
--   3. **CMP.** Given a prediction $\hat o$ and $k=cn$ (confidence $c\in[0,1)$, $cn$ an integer), the mechanism adds $k$ copies of $\hat o$ to the agents' points and returns the point whose $x$- and $y$-coordinates are the lower medians of the $n+k$ $x$-values and the $n+k$ $y$-values. This is $f(P,\hat o,c)$. The approximation ratio is
--   $$r(P,\hat o,c)=\frac{C^u(f(P,\hat o,c),P)}{C^u(o(P),P)}.$$
--
--   4. **Half-axes.** $A_{+x}=\{(x,0):x\ge0\}$, $A^>_{+x}=\{(x,0):x>0\}$, and similarly $A_{-x},A^<_{-x},A_{+y},A^>_{+y},A_{-y},A^<_{-y}$; $A_x$ and $A_y$ are the whole axes.
--
--   5. **COA (Definition 6).** $\mathcal P^C_{coa}(c)$: instances with $o(P)=(0,1)$, $f(P,o(P),c)=(0,0)$, and every point in $\{(0,1),(x,0),(-x,0)\}$ for one $x\ge0$. $\mathcal P^R_{coa}(c)$: the same with prediction $\hat o=(0,0)$.
--
--   6. **OA (Definition 14).** $\mathcal P^C_{oa}(c)$ / $\mathcal P^R_{oa}(c)$: CMP (with prediction $o(P)$, resp. $(0,0)$) outputs the origin, $o(P)$ lies on the open $+y$ half-axis, and every point lies on $A_x\cup A_y$.
--
--   7. **CA (Definition 13).** $\mathcal P^C_{ca}(c)$ / $\mathcal P^R_{ca}(c)$: CMP outputs the origin; $y_o\ge x_o>0$; moving any point $p_i\ne o(P)$ by $\epsilon\in(0,1]$ of the way towards $o(P)$ changes the output; and for some $x_1,x_2,y_1,y_2\ge0$ every point lies in $\{(-x_1,0),(x_2,0),(0,-y_1),(0,y_2),o(P)\}$, there are fewer points in $A^<_{-x}$ than in $A^>_{+x}\cup\{o(P)\}$ and fewer in $A^<_{-y}$ than in $A^>_{+y}\cup\{o(P)\}$, and occupied opposite clusters are equidistant from $o(P)$: $x_o+x_1=x_2-x_o$, $y_o+y_1=y_2-y_o$.
--
--   These objects are shared by every statement of the mission: Theorem 9 is about CMP and $C^u$, and the reduction lemmas move instances between the COA, OA and CA families.
--
--   **Formalization Note** The plane is `EuclideanSpace ℝ (Fin 2)` (not `ℝ × ℝ`, whose metric is the sup metric). Profiles are `Fin n`-indexed; CMP depends only on the multiset of points. The mechanism is indexed by the number `k` of prediction copies; `Admissible c n k` says $n\ge1$ and $k=cn$. The optimal location is a hypothesis `IsOpt P o`, not a chosen function. Families take the optimal location `o` as an argument. Two readings differ from the printed Definition 13: property (3) ranges over points $p_i\ne o(P)$ (for $p_i=o(P)$ the move is trivial, so the printed condition would forbid points at $o(P)$, which (a)–(c) explicitly allow, and the proof of Lemma 17 only moves points that can move); and in (e) the $y$-clusters are $(0,-y_1),(0,y_2)$ (printed as $(-y_1,0),(y_2,0)$). Counts of points are counts of agents (multiset multiplicity).
-- source:
--   Agrawal, Balkanski, Gkatzelis, Ou & Tan, Learning-Augmented Mechanism Design: Leveraging Predictions for Facility Location, arXiv:2204.01120v1, §2, pp. 5–6 (model, CM, consistency/robustness); §4.1, p. 12 (CMP), Definition 6, pp. 12–13; §4.4.1, Definitions 13–14, p. 19

import Mathlib

namespace LearnAugFL.CMP

/-- The Euclidean plane `ℝ²` with the Euclidean distance (not the sup metric of `ℝ × ℝ`).
`p 0` is the x-coordinate and `p 1` the y-coordinate of `p`. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The utilitarian social cost `C^u(f, P) = (∑_{p ∈ P} d(f, p)) / n` of the facility location `f`
for the profile `P = (p_1, …, p_n)` of preferred locations (agents indexed by `Fin n`). -/
noncomputable def ucost {n : ℕ} (P : Fin n → Pt) (f : Pt) : ℝ :=
  (∑ i, dist f (P i)) / n

/-- `o` is an optimal facility location for the utilitarian social cost of `P`
(a minimizer of `C^u(·, P)`, i.e. a geometric median of `P`). -/
def IsOpt {n : ℕ} (P : Fin n → Pt) (o : Pt) : Prop :=
  ∀ z : Pt, ucost P o ≤ ucost P z

/-- The lower median of a finite multiset of `m` reals: its `⌈m/2⌉`-th smallest element
(the smaller of the two medians when `m` is even). -/
noncomputable def lowerMedian (s : Multiset ℝ) : ℝ :=
  (s.sort (· ≤ ·)).getD ((Multiset.card s + 1) / 2 - 1) 0

/-- The multiset of `j`-th coordinates of the `n` agents' points together with `k` copies of the
`j`-th coordinate of the prediction `ô` (the points of `P ∪ P'`, `P'` = `k` copies of `ô`). -/
def coordValues {n : ℕ} (P : Fin n → Pt) (ô : Pt) (k : ℕ) (j : Fin 2) : Multiset ℝ :=
  (Finset.univ.val.map fun i => P i j) + Multiset.replicate k (ô j)

/-- The Coordinatewise Median with Predictions (CMP) mechanism with `k` copies of the prediction
`ô`: each coordinate of the facility is the lower median of the `n + k` values of that coordinate
over the agents' points and the `k` copies of `ô`. With `k = cn` this is `f(P, ô, c)`. -/
noncomputable def cmp {n : ℕ} (P : Fin n → Pt) (ô : Pt) (k : ℕ) : Pt :=
  !₂[lowerMedian (coordValues P ô k 0), lowerMedian (coordValues P ô k 1)]

/-- `n ≥ 1` agents and `k = cn` copies of the prediction (`cn` an integer). -/
def Admissible (c : ℝ) (n k : ℕ) : Prop :=
  1 ≤ n ∧ (k : ℝ) = c * n

/-- The approximation ratio `r(P, ô, c) = C^u(f(P, ô, c), P) / C^u(o(P), P)` of CMP with `k = cn`
copies of the prediction `ô`, measured against the optimal location `o`. -/
noncomputable def ratio {n : ℕ} (P : Fin n → Pt) (ô o : Pt) (k : ℕ) : ℝ :=
  ucost P (cmp P ô k) / ucost P o

/-- Number of agents `i` whose point `P i` satisfies `q` (agents counted with multiplicity). -/
noncomputable def count {n : ℕ} (P : Fin n → Pt) (q : Pt → Prop) : ℕ :=
  Set.ncard {i : Fin n | q (P i)}

/-! ### Axes and half-axes -/

/-- `A_x`: the x-axis. -/
def onX (p : Pt) : Prop := p 1 = 0
/-- `A_y`: the y-axis. -/
def onY (p : Pt) : Prop := p 0 = 0
/-- `A_{+x} = {(x, 0) : x ≥ 0}`. -/
def posX (p : Pt) : Prop := p 1 = 0 ∧ 0 ≤ p 0
/-- `A^>_{+x} = {(x, 0) : x > 0}`. -/
def posX' (p : Pt) : Prop := p 1 = 0 ∧ 0 < p 0
/-- `A_{−x} = {(x, 0) : x ≤ 0}`. -/
def negX (p : Pt) : Prop := p 1 = 0 ∧ p 0 ≤ 0
/-- `A^<_{−x} = {(x, 0) : x < 0}`. -/
def negX' (p : Pt) : Prop := p 1 = 0 ∧ p 0 < 0
/-- `A_{+y} = {(0, y) : y ≥ 0}`. -/
def posY (p : Pt) : Prop := p 0 = 0 ∧ 0 ≤ p 1
/-- `A^>_{+y} = {(0, y) : y > 0}`. -/
def posY' (p : Pt) : Prop := p 0 = 0 ∧ 0 < p 1
/-- `A_{−y} = {(0, y) : y ≤ 0}`. -/
def negY (p : Pt) : Prop := p 0 = 0 ∧ p 1 ≤ 0
/-- `A^<_{−y} = {(0, y) : y < 0}`. -/
def negY' (p : Pt) : Prop := p 0 = 0 ∧ p 1 < 0

/-! ### Definition 6: Clusters-and-Opt-on-Axes (COA) -/

/-- `P ∈ 𝒫^C_coa(c)` (prediction `ô = o(P) = (0, 1)`): `(0, 1)` is optimal, CMP outputs the
origin, and every point is `(0, 1)`, `(x, 0)` or `(−x, 0)` for one `x ≥ 0`. -/
def COA_C (c : ℝ) (n k : ℕ) (P : Fin n → Pt) : Prop :=
  Admissible c n k ∧ IsOpt P !₂[0, 1] ∧ cmp P !₂[0, 1] k = 0 ∧
    ∃ x : ℝ, 0 ≤ x ∧ ∀ i, P i = !₂[0, 1] ∨ P i = !₂[x, 0] ∨ P i = !₂[-x, 0]

/-- `P ∈ 𝒫^R_coa(c)` (prediction `ô = (0, 0)`): as `COA_C`, with CMP run on the prediction `(0, 0)`. -/
def COA_R (c : ℝ) (n k : ℕ) (P : Fin n → Pt) : Prop :=
  Admissible c n k ∧ IsOpt P !₂[0, 1] ∧ cmp P 0 k = 0 ∧
    ∃ x : ℝ, 0 ≤ x ∧ ∀ i, P i = !₂[0, 1] ∨ P i = !₂[x, 0] ∨ P i = !₂[-x, 0]

/-! ### Definition 14: Optimal-on-Axes (OA) -/

/-- `P ∈ 𝒫^C_oa(c)` with optimal location `o` (prediction `ô = o`): CMP outputs the origin,
`o` lies on the open `+y` half-axis, and every point lies on `A_x ∪ A_y`. -/
def OA_C (c : ℝ) (n k : ℕ) (P : Fin n → Pt) (o : Pt) : Prop :=
  Admissible c n k ∧ IsOpt P o ∧ cmp P o k = 0 ∧ o 0 = 0 ∧ 0 < o 1 ∧
    ∀ i, onX (P i) ∨ onY (P i)

/-- `P ∈ 𝒫^R_oa(c)` with optimal location `o` (prediction `ô = (0, 0)`). -/
def OA_R (c : ℝ) (n k : ℕ) (P : Fin n → Pt) (o : Pt) : Prop :=
  Admissible c n k ∧ IsOpt P o ∧ cmp P 0 k = 0 ∧ o 0 = 0 ∧ 0 < o 1 ∧
    ∀ i, onX (P i) ∨ onY (P i)

/-! ### Definition 13: Clusters-on-Axes (CA) -/

/-- Definition 13 for prediction `ô` and optimal location `o`. Property (3) ranges over the agents
whose point differs from `o(P)` (a point at `o(P)` cannot move towards it); in (e) the
y-clusters are `(0, −y₁)` and `(0, y₂)`. -/
def CA (c : ℝ) (n k : ℕ) (P : Fin n → Pt) (ô o : Pt) : Prop :=
  Admissible c n k ∧ IsOpt P o ∧
  -- (1) output at origin
  cmp P ô k = 0 ∧
  -- (2) opt in top-right quadrant
  (0 < o 0 ∧ o 0 ≤ o 1) ∧
  -- (3) no move towards opt
  (∀ i, P i ≠ o → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      cmp (Function.update P i (P i + ε • (o - P i))) ô k ≠ cmp P ô k) ∧
  -- (4)
  ∃ x₁ x₂ y₁ y₂ : ℝ, 0 ≤ x₁ ∧ 0 ≤ x₂ ∧ 0 ≤ y₁ ∧ 0 ≤ y₂ ∧
    -- (a) clusters on axes
    (∀ i, P i = !₂[-x₁, 0] ∨ P i = !₂[x₂, 0] ∨ P i = !₂[0, -y₁] ∨ P i = !₂[0, y₂] ∨ P i = o) ∧
    -- (b) less points in left
    count P negX' < count P (fun p => posX' p ∨ p = o) ∧
    -- (c) less points in bottom
    count P negY' < count P (fun p => posY' p ∨ p = o) ∧
    -- (d) x-clusters equidistant from opt
    ((∃ i, P i = !₂[-x₁, 0]) → (∃ j, P j = !₂[x₂, 0]) → o 0 + x₁ = x₂ - o 0) ∧
    -- (e) y-clusters equidistant from opt
    ((∃ i, P i = !₂[0, -y₁]) → (∃ j, P j = !₂[0, y₂]) → o 1 + y₁ = y₂ - o 1)

/-- `P ∈ 𝒫^C_ca(c)` with optimal location `o` (prediction `ô = o`). -/
def CA_C (c : ℝ) (n k : ℕ) (P : Fin n → Pt) (o : Pt) : Prop := CA c n k P o o

/-- `P ∈ 𝒫^R_ca(c)` with optimal location `o` (prediction `ô = (0, 0)`). -/
def CA_R (c : ℝ) (n k : ℕ) (P : Fin n → Pt) (o : Pt) : Prop := CA c n k P 0 o

end LearnAugFL.CMP


