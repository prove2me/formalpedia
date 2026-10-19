-- Prove2me | Definitions.Def_DynkinIncInfo_Saddle_Regions
-- name    : DynkinIncInfo_Saddle_Regions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:06.930783+00:00
-- url     : https://prove2.me/theorems/e910f40b-e7e6-4e7d-91c1-ea6771ee8735
-- title:
--   §4–§5, pp. 8–15 — stopping regions S1, S2, sets A1, A2, boundaries b1, b2, parabolic coordinates F, H1, H2, v, S'1, S'2, yK, RK, and c1
-- statement:
--   This file defines the geometric objects of §4–§5.
--
--   On the state space $\mathbb R_+\times[0,1]$, $\mathbb R_+=(0,\infty)$, the stopping regions of the buyer and of the seller are
--   $$\mathcal S_1=\{(x,y)\mid V(x,y)=G_1(x)\},\qquad \mathcal S_2=\{(x,y)\mid V(x,y)=G_2(x)\}.$$
--   The sets $A_1=\{(x,y)\mid xy<rK/\delta_0,\ x>K\}$ and $A_2=\{(x,y)\mid xy>r(K-\varepsilon_0)/\delta_0,\ x>K\}$ (with $y\in[0,1]$) are the explicit forms printed on p. 9. The boundaries are
--   $$b_1(y)=\inf\{x>0\mid V(x,y)=G_1(x)\},\qquad b_2(y)=\sup\{x>0\mid V(x,y)=G_2(x)\},$$
--   with $\inf\emptyset=+\infty$ and $\sup\emptyset=0$, valued in $[0,\infty]$.
--
--   In parabolic coordinates, $F(z,y)=e^z\big(\tfrac{1-y}{y}\big)^{\sigma^2/\delta_0}$ on $\mathbb R\times(0,1)$, $H_i(z,y)=G_i(F(z,y))$, $v(z,y)=V(F(z,y),y)$, and
--   $$\mathcal S'_i=\{(z,y)\in\mathbb R\times(0,1)\mid v(z,y)=H_i(z,y)\},\quad R_K=\{(z,y)\in\mathbb R\times(0,1)\mid F(z,y)\ge K\},$$
--   $$y_K(z)=\frac{e^{\delta_0z/\sigma^2}}{K^{\delta_0/\sigma^2}+e^{\delta_0z/\sigma^2}}.$$
--   Finally $c_1(z)=\sup\big(\{0\}\cup\{y\in(0,1)\mid(z,y)\in\mathcal S'_1\}\big)$ is the boundary of $\mathcal S'_1$ (Corollary 5.5).
--
--   **Formalization Note.** The degenerate price $x=0$ is excluded from the regions and boundaries: there the price stays $0$ and $V(0,y)=0=G_1(0)$, so the page's literal $x\in[0,\infty)$ in (4.2) and (4.11) would put every $(0,y)$ in $\mathcal S_1$ and give $b_1\equiv0$. Corollary 5.5 only asserts that some $c_1$ exists; the explicit supremum is the canonical choice and equals $0$ when the section is empty. $F$ uses the real power with base $(1-y)/y$, meaningful for $y\in(0,1)$; the primed regions and $R_K$ are restricted to $y\in(0,1)$.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 8 (4.2)–(4.3); p. 9 (4.6)–(4.7) and the explicit A1, A2; p. 11 (4.11)–(4.12); p. 12 (5.5); p. 13 (5.6), S'1, S'2, (5.11), yK; p. 15 Corollary 5.5 (c1)

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The state space `ℝ₊ × [0, 1]` (§4, p. 8, arXiv:1705.07352v4), with `ℝ₊ = (0, ∞)`.

**Formalization Note.** The price starts at `x > 0` (p. 2) and stays positive. At `x = 0` the price
is identically `0`, so `V(0, y) = 0 = G1(0)`; admitting `x = 0` would put every `(0, y)` into `𝒮1`
and make `b1 ≡ 0`, contradicting Proposition 4.1 and Corollary 4.5. The state `x = 0` is
therefore excluded from the regions and boundaries. -/
def dom : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ q.2 ∈ Set.Icc (0 : ℝ) 1}

/-- **The buyer's stopping region** `𝒮1 = {(x, y) ∈ ℝ₊ × [0, 1] | V(x, y) = G1(x)}`, `ℝ₊ = (0, ∞)`
((4.2), p. 8, arXiv:1705.07352v4). -/
def S1 (p : Params) (st : Setting Ω) : Set (ℝ × ℝ) :=
  {q | q ∈ dom ∧ V p st q.1 q.2 = G1 p q.1}

/-- **The seller's stopping region** `𝒮2 = {(x, y) ∈ ℝ₊ × [0, 1] | V(x, y) = G2(x)}`, `ℝ₊ = (0, ∞)`
((4.3), p. 8, arXiv:1705.07352v4). -/
def S2 (p : Params) (st : Setting Ω) : Set (ℝ × ℝ) :=
  {q | q ∈ dom ∧ V p st q.1 q.2 = G2 p q.1}

/-- The set `A1 = {(x, y) | xy < rK/δ0 and x > K}` with `y ∈ [0, 1]` (p. 9,
arXiv:1705.07352v4: the explicit form of (4.6), `A1 = {(LG1 − rG1) > 0}` on `(K, ∞) × [0, 1]`). -/
def A1 (p : Params) : Set (ℝ × ℝ) :=
  {q | p.K < q.1 ∧ q.2 ∈ Set.Icc (0 : ℝ) 1 ∧ q.1 * q.2 < p.r * p.K / p.δ0}

/-- The set `A2 = {(x, y) | xy > r(K − ε0)/δ0 and x > K}` with `y ∈ [0, 1]` (p. 9,
arXiv:1705.07352v4: the explicit form of (4.7), `A2 = {(LG2 − rG2) < 0}` on `(K, ∞) × [0, 1]`). -/
def A2 (p : Params) : Set (ℝ × ℝ) :=
  {q | p.K < q.1 ∧ q.2 ∈ Set.Icc (0 : ℝ) 1 ∧ p.r * (p.K - p.ε0) / p.δ0 < q.1 * q.2}

/-- **The boundary** `b1(y) = inf{x ∈ (0, ∞) | V(x, y) = G1(x)}`, `inf ∅ = +∞`
((4.11), p. 11, arXiv:1705.07352v4), valued in `[0, ∞]`.

**Formalization Note.** The page writes `x ∈ [0, +∞)`; the degenerate state `x = 0` (where
`V(0, y) = 0 = G1(0)`) is excluded, see `dom`. -/
noncomputable def b1 (p : Params) (st : Setting Ω) (y : ℝ) : ℝ≥0∞ :=
  ⨅ (x : ℝ≥0) (_ : 0 < x ∧ V p st (x : ℝ) y = G1 p (x : ℝ)), (x : ℝ≥0∞)

/-- **The boundary** `b2(y) = sup{x ∈ (0, ∞) | V(x, y) = G2(x)}`, `sup ∅ = 0`
((4.12), p. 11, arXiv:1705.07352v4), valued in `[0, ∞]`.

**Formalization Note.** As for `b1`, the state `x = 0` is excluded (it never satisfies
`V = G2`, since `V(0, y) = 0 < ε0 = G2(0)`, so this does not change `b2`). -/
noncomputable def b2 (p : Params) (st : Setting Ω) (y : ℝ) : ℝ≥0∞ :=
  ⨆ (x : ℝ≥0) (_ : 0 < x ∧ V p st (x : ℝ) y = G2 p (x : ℝ)), (x : ℝ≥0∞)

/-- The change of coordinates `F(z, y) = e^z ((1 − y)/y)^{σ²/δ0}` on `ℝ × (0, 1)`
((5.5), p. 12, arXiv:1705.07352v4); `Real.rpow`, meaningful for `y ∈ (0, 1)`. -/
noncomputable def F (p : Params) (z y : ℝ) : ℝ :=
  Real.exp z * ((1 - y) / y) ^ (p.σ ^ 2 / p.δ0)

/-- `H1(z, y) = G1(F(z, y))` ((5.6), p. 13, arXiv:1705.07352v4). -/
noncomputable def H1 (p : Params) (z y : ℝ) : ℝ := G1 p (F p z y)

/-- `H2(z, y) = G2(F(z, y))` ((5.6), p. 13, arXiv:1705.07352v4). -/
noncomputable def H2 (p : Params) (z y : ℝ) : ℝ := G2 p (F p z y)

/-- The value in parabolic coordinates `v(z, y) = V(F(z, y), y)` ((5.6), p. 13,
arXiv:1705.07352v4). -/
noncomputable def v (p : Params) (st : Setting Ω) (z y : ℝ) : ℝ := V p st (F p z y) y

/-- `𝒮'1 = {(z, y) ∈ ℝ × (0, 1) | v(z, y) = H1(z, y)}` (p. 13, arXiv:1705.07352v4). -/
def S1' (p : Params) (st : Setting Ω) : Set (ℝ × ℝ) :=
  {q | q.2 ∈ Set.Ioo (0 : ℝ) 1 ∧ v p st q.1 q.2 = H1 p q.1 q.2}

/-- `𝒮'2 = {(z, y) ∈ ℝ × (0, 1) | v(z, y) = H2(z, y)}` (p. 13, arXiv:1705.07352v4). -/
def S2' (p : Params) (st : Setting Ω) : Set (ℝ × ℝ) :=
  {q | q.2 ∈ Set.Ioo (0 : ℝ) 1 ∧ v p st q.1 q.2 = H2 p q.1 q.2}

/-- `y_K(z) = e^{δ0 z/σ²} / (K^{δ0/σ²} + e^{δ0 z/σ²})` (p. 13, below (5.11),
arXiv:1705.07352v4). -/
noncomputable def yK (p : Params) (z : ℝ) : ℝ :=
  Real.exp (p.δ0 / p.σ ^ 2 * z) / (p.K ^ (p.δ0 / p.σ ^ 2) + Real.exp (p.δ0 / p.σ ^ 2 * z))

/-- `R_K = {(z, y) ∈ ℝ × (0, 1) | F(z, y) ≥ K}` ((5.11), p. 13, arXiv:1705.07352v4). -/
def RK (p : Params) : Set (ℝ × ℝ) :=
  {q | q.2 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.K ≤ F p q.1 q.2}

/-- The boundary `c1` of `𝒮'1` (Corollary 5.5, p. 15, arXiv:1705.07352v4), made explicit as
`c1(z) = sup({0} ∪ {y ∈ (0, 1) | (z, y) ∈ 𝒮'1})`.

**Formalization Note.** Corollary 5.5 only asserts that some `c1` exists; this is the canonical
choice (it agrees with any `c1` satisfying (5.20) wherever the section is nonempty, and is `0`
when the section is empty). -/
noncomputable def c1 (p : Params) (st : Setting Ω) (z : ℝ) : ℝ :=
  sSup (insert 0 {y : ℝ | y ∈ Set.Ioo (0 : ℝ) 1 ∧ (z, y) ∈ S1' p st})

end DynkinIncInfo.Saddle


