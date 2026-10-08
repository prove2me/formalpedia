-- Prove2me | Definitions.Def_OceanicGames_Interior_Basic
-- name    : OceanicGames_Interior_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:09:43.089038+00:00
-- url     : https://prove2.me/theorems/b632248a-a51f-482b-a143-012d91b54e5c
-- title:
--   Oceanic games [c; w_1, …, w_m; α]: pivot sets, major-player values φ_i, the ocean's value Φ, the pivot location F, interior games, a_n and π(S)
-- statement:
--   These definitions set up the **oceanic games** of Milnor and Shapley: weighted majority games with finitely many **major players** $M = \{1, \dots, m\}$ and a continuum of infinitesimal players, the **ocean** $I = [0,1]$ with Lebesgue measure $\mu$.
--
--   1. **Weights.** Major player $j$ has weight $w_j$, and $w(S) = \sum_{j \in S} w_j$ for $S \subseteq M$. The ocean has total weight $\alpha$. The **oceanic game** $[c; w_1, \dots, w_m; \alpha]$ with quota $c$ is the game in which a coalition wins when its major players' weight plus $\alpha$ times its share of the ocean is at least $c$.
--   2. **Random order.** Let $x = (x_1, \dots, x_m)$ be a uniformly random point of the cube $I^m$; $x_j$ is the position at which major player $j$ is inserted into the ordered ocean. Write $P(t) = \{ j \in M : x_j < t \}$ for the major players placed before position $t$.
--   3. **Pivot sets and values.** Player $i$ is pivotal at $x$ when
--   $$w(P(x_i)) + \alpha x_i \le c \le w(P(x_i)) + w_i + \alpha x_i. \qquad (2.4)$$
--   The set of such $x \in I^m$ is $A_i$, and the **value** of the game to player $i$ is its volume, $\varphi_i = \mu^m(A_i)$.
--   4. **The ocean's value.** The combined value of the ocean is defined by $\Phi = 1 - \sum_{i \in M} \varphi_i$, i.e. by (2.5) $\Phi + \varphi(M) = 1$.
--   5. **The pivot location.** For a quota $y$, $F(y)$ is the position in the ordered ocean at which the cumulative weight $w(P(t)) + \alpha t$ first reaches $y$:
--   $$F(y) = \inf \{ t \ge 0 : w(P(t)) + \alpha t \ge y \},$$
--   and $E\{F(y)\} = \int_{I^m} F(y)\, dx_1 \cdots dx_m$.
--   6. **The added player.** $(w_1, \dots, w_m, w_{m+1})$ denotes the weights of the game $\Gamma^+$ obtained by appending a new major player $m+1$ of weight $w_{m+1}$.
--   7. **Interior games.** $[c; w_1, \dots, w_m; \alpha]$ is **interior** when $w(M) \le c \le \alpha$: the ocean wins alone and the major players together lose.
--   8. **Coefficients.** $a_0 = 1$ and $a_n = 1 - n a_{n-1}$ for $n \ge 1$, so $a_0, a_1, \dots = 1, 0, 1, -2, 9, -44, \dots$
--   9. **Products.** With $\bar w_j = \alpha - w_j$, $\pi(S) = \prod_{j \in S} \frac{w_j}{\alpha} \prod_{j \in M - S} \frac{\bar w_j}{\alpha}$ for $S \subseteq M$, and $\pi_i(S) = \prod_{j \in S} \frac{w_j}{\alpha} \prod_{j \in (M - \{i\}) - S} \frac{\bar w_j}{\alpha}$ for $S \subseteq M - \{i\}$.
--
--   These are the objects of §2, §4 and §5 of the memorandum; every theorem of the mission is stated in terms of them.
--
--   **Formalization Note** Major players are `Fin m`. The probability of an event is the Lebesgue volume of its intersection with the cube $[0,1]^m$ (which has volume 1). $P(t)$ uses the strict inequality $x_j < t$, as printed. The values $\varphi_i$ are defined for every real $c$ and $\alpha$ and every weight vector; nonnegativity of the weights, $\alpha > 0$ and the quota range are hypotheses of the theorems. $\Phi$ is defined by (2.5), as the paper allows, not as a pivot probability. The page defines $F(y) = \min\{x \mid w(P(x)) + \alpha x \ge y\}$; because $P$ is strict the minimum need not be attained (at a jump of the cumulative weight), so $F$ is read as the infimum, over $t \ge 0$, which is the value shown in the paper's Fig. 3. The added player is appended with `Fin.snoc`, as index `Fin.last m`. $a_n$ is integer-valued.
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), §2, (2.1)–(2.5), pp. 2–5; (4.1)–(4.2), p. 9; E{·}, p. 11; (4.8), p. 13; (5.3), p. 17; π(S), π_i(S), (5.6), p. 19

import Mathlib
open MeasureTheory

namespace OceanicGames.Interior

/-- `w(S) = Σ_{j ∈ S} w_j`, the total weight of a set `S` of major players (§2, p. 2). -/
def wsum {m : ℕ} (w : Fin m → ℝ) (S : Finset (Fin m)) : ℝ := ∑ j ∈ S, w j

/-- `P(t)`: the major players `j` with `x_j < t`, i.e. those placed before the ocean position `t`
(§2, p. 4; strict inequality as printed). -/
noncomputable def pred {m : ℕ} (x : Fin m → ℝ) (t : ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => x j < t)

/-- The unit cube `I^m = [0,1]^m` (Pi order). -/
def cube (m : ℕ) : Set (Fin m → ℝ) := Set.Icc 0 1

/-- `A_i` (§2, p. 5): the points of the cube `I^m` at which major player `i` is pivotal in the
oceanic game `[c; w_1, …, w_m; α]`, i.e. at which the inequalities (2.4)
`w(P(x_i)) + α x_i ≤ c ≤ w(P(x_i)) + w_i + α x_i` hold. -/
def pivotSet {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (i : Fin m) : Set (Fin m → ℝ) :=
  {x | x ∈ cube m ∧ wsum w (pred x (x i)) + α * x i ≤ c ∧
                    c ≤ wsum w (pred x (x i)) + w i + α * x i}

/-- `φ_i = μ^m(A_i)`, the value of the oceanic game `[c; w_1, …, w_m; α]` to major player `i`
(§2, pp. 4–5): the probability, for `x` uniform on `I^m`, that (2.4) holds. -/
noncomputable def value {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (i : Fin m) : ℝ :=
  (volume (pivotSet c α w i)).toReal

/-- `Φ`, the combined value of the ocean, defined by (2.5): `Φ + φ(M) = 1`. -/
noncomputable def oceanValue {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) : ℝ :=
  1 - ∑ i, value c α w i

/-- `F(y)` of (4.2), the location in the ordered ocean of the pivot of the game with quota `y`,
for the random point `x ∈ I^m`. The page prints `min {x | w(P(x)) + αx ≥ y}`; the minimum need
not be attained (P is strict), so it is read as the infimum over `t ≥ 0`. -/
noncomputable def pivotLoc {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (x : Fin m → ℝ) (y : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ y ≤ wsum w (pred x t) + α * t}

/-- `E{F(y)} = ∫_{I^m} F(y) dx_1 … dx_m` (p. 11). -/
noncomputable def expPivotLoc {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (y : ℝ) : ℝ :=
  ∫ x in cube m, pivotLoc α w x y

/-- The weights `(w_1, …, w_m, w_{m+1})` of the game `Γ⁺` of (4.8): a new major player
`m+1` (index `Fin.last m`) with weight `w'` is appended. -/
def addWeight {m : ℕ} (w : Fin m → ℝ) (w' : ℝ) : Fin (m + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) w w'

/-- The interior condition (5.3): `w(M) ≤ c ≤ α`. -/
def IsInterior {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) : Prop :=
  wsum w Finset.univ ≤ c ∧ c ≤ α

/-- The coefficients `a_n` of (5.6): `a_0 = 1`, `a_n = 1 − n a_{n−1}`. -/
def coeff : ℕ → ℤ
  | 0 => 1
  | n + 1 => 1 - ((n : ℤ) + 1) * coeff n

/-- `π(S)` for `S ⊆ M` (p. 19): the product of `w_j/α` over `j ∈ S` and of `w̄_j/α = (α − w_j)/α`
over `j ∈ M − S`. -/
noncomputable def piProd {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  (∏ j ∈ S, w j / α) * ∏ j ∈ Finset.univ \ S, (α - w j) / α

/-- `π_i(S)` for `S ⊆ M − {i}` (p. 19): the product of `w_j/α` over `j ∈ S` and of
`(α − w_j)/α` over `j ∈ (M − {i}) − S`. -/
noncomputable def piProdErase {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (i : Fin m)
    (S : Finset (Fin m)) : ℝ :=
  (∏ j ∈ S, w j / α) * ∏ j ∈ (Finset.univ.erase i) \ S, (α - w j) / α

end OceanicGames.Interior


