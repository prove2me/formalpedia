-- Prove2me | Definitions.Def_RevShareCoord_Competing_Model
-- name    : RevShareCoord_Competing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:52:54.224766+00:00
-- url     : https://prove2.me/theorems/7aa8e339-ab26-4283-8f07-6b1a438cb83b
-- title:
--   Sec. 3.2 — the competing-retailers model: standing assumptions on R_i, the first-order system (6) and the prices w_i^I
-- statement:
--   The standing assumptions of Section 3.2 on the competing-retailers model. There are $n$ locations with revenue functions $R_i(\bar q)$ and a unit cost $c$. Write
--   $$R_j^i(\bar q) = \frac{\partial R_j(\bar q)}{\partial q_i}$$
--   for the effect of the quantity at location $i$ on the revenue at location $j$: the superscript is the variable differentiated, the subscript the revenue function. A model consists of the functions $R_i$, their partial derivatives $R_j^i$, and $c$, subject to:
--
--   1. $c > 0$;
--   2. each $R_i$ is continuous on the nonnegative orthant;
--   3. at every profile with all quantities positive, each $R_j$ has the partial derivative $R_j^i$ in the direction $q_i$;
--   4. $\partial^2 R_i/\partial q_i \partial q_j \le 0$ for $j \neq i$, in the form: raising the quantity at another location $j$ does not raise the marginal revenue $R_i^i$ at $i$ (locations are substitutes);
--   5. $R_i(\bar q)$ is concave in its own quantity $q_i \ge 0$ for every profile of nonnegative quantities at the other locations.
--
--   On such a model two derived objects are defined. The **first-order system (6)** of the integrated channel at a profile $\bar q$ is
--   $$R_i^i(\bar q) + \sum_{j\neq i} R_j^i(\bar q) = c, \qquad i = 1,\dots,n .$$
--   The **coordinating wholesale prices** at a profile $\bar q^I$ are
--   $$w_i^I = c - \sum_{j\neq i} R_j^i(\bar q^I), \qquad i = 1,\dots,n,$$
--   which charge retailer $i$ for the marginal cost of production and for the externality its quantity imposes on the other locations.
--
--   **Formalization Note** The paper assumes that $R_i(\bar q)$ is *unimodal* in $q_i$. Unimodality of $R_i$ does not survive subtracting the linear purchase cost $w_i q_i$, so it does not make the retailer's first-order condition sufficient, which the paper's equilibrium argument (via Fudenberg–Tirole, Thm 1.2) needs. Concavity in the own quantity is the standard sufficient condition, holds in the paper's Cournot example (7), and is used here as the reading of "unimodal". The cross-partial assumption is encoded through the monotonicity of $R_i^i$ in $q_j$, which is what the paper's gloss states and does not require second derivatives to exist. The paper's assumption that marginal revenue at $i$ eventually falls below any $\delta > 0$ even when all other locations stock nothing is used only for the existence of an equilibrium, which is not formalized; it is omitted. In Lean `M.dR i j q` is $R_j^i(\bar q) = \partial R_j/\partial q_i$.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), pp. 12–13 (PDF pp. 13–14), Section 3.2: model paragraph, Eq. (6), and the display defining w_i^I

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game

/-!
# The competing-retailers model of Sec. 3.2 and its coordinating wholesale prices

Cachon–Lariviere, *Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and
Limitations*, working paper (June 2000), Sec. 3.2, pp. 12–13.

**Index convention.** `dR i j q` is the partial derivative `∂R_j/∂q_i` at `q`, which the paper
writes `R_j^i(q̄)`: the first index (the paper's superscript) is the variable differentiated,
the second (the paper's subscript) the revenue function.
-/

namespace RevShareCoord.Competing

open Finset

/-- The standing assumptions of Sec. 3.2 (pp. 12–13) on the revenue functions `Rᵢ` of the `n`
locations and the unit cost `c`.

* `R i q` is the revenue `Rᵢ(q̄)` at location `i`; `dR i j q` is `R_j^i(q̄) = ∂R_j/∂q_i`, given at
  every profile with all quantities positive.
* `Rᵢ` is continuous (on profiles with nonnegative entries).
* `∂²Rᵢ/∂qᵢ∂qⱼ ≤ 0` for `j ≠ i`, encoded as: the marginal revenue `R_i^i` at `i` does not increase
  when the quantity at another location `j` increases (the paper's own reading: "increasing the
  quantity at location j reduces the marginal revenue … at i").
* "`Rᵢ(q̄)` is unimodal in `qᵢ`" is read as: for every profile of nonnegative quantities, `Rᵢ` is
  concave in its own quantity `qᵢ ∈ [0, ∞)`.
* `c > 0`.

The assumption on `q_i^δ` (marginal revenue eventually below any `δ > 0`) is used by the paper
only for the existence of an equilibrium and is not part of this structure. -/
structure Model (n : ℕ) where
  /-- Revenue `Rᵢ(q̄)` at location `i`. -/
  R : Fin n → (Fin n → ℝ) → ℝ
  /-- `dR i j q = R_j^i(q̄) = ∂R_j/∂q_i (q̄)`. -/
  dR : Fin n → Fin n → (Fin n → ℝ) → ℝ
  /-- Unit cost `c` of a unit, at any location. -/
  c : ℝ
  /-- `c > 0`. -/
  c_pos : 0 < c
  /-- `Rᵢ` is continuous on the nonnegative orthant. -/
  cont : ∀ i, ContinuousOn (R i) {q | ∀ k, 0 ≤ q k}
  /-- At every profile with all quantities positive, `dR i j q` is the partial derivative of
  `R_j` with respect to `q_i`. -/
  hasPartial : ∀ q : Fin n → ℝ, (∀ k, 0 < q k) → ∀ i j,
    HasDerivAt (fun t => R j (Function.update q i t)) (dR i j q) (q i)
  /-- `∂²Rᵢ/∂qᵢ∂qⱼ ≤ 0` for `j ≠ i`: raising `q_j` does not raise `R_i^i`. -/
  cross : ∀ q : Fin n → ℝ, (∀ k, 0 < q k) → ∀ i j, j ≠ i → ∀ t, q j ≤ t →
    dR i i (Function.update q j t) ≤ dR i i q
  /-- `Rᵢ` is concave in its own quantity `qᵢ ≥ 0` (reading of "unimodal in `qᵢ`"). -/
  concave_own : ∀ (i : Fin n) (q : Fin n → ℝ), (∀ k, 0 ≤ q k) →
    ConcaveOn ℝ (Set.Ici 0) (fun t => R i (Function.update q i t))

namespace Model

variable {n : ℕ} (M : Model n)

/-- The first-order system (6) of the integrated channel (Sec. 3.2, p. 12):
`R_i^i(q̄) + Σ_{j≠i} R_j^i(q̄) = c` for `i = 1, …, n`. -/
def FOC (q : Fin n → ℝ) : Prop :=
  ∀ i, M.dR i i q + ∑ j ∈ univ.erase i, M.dR i j q = M.c

/-- The coordinating wholesale prices `w_i^I = c − Σ_{j≠i} R_j^i(q̄^I)` (Sec. 3.2, p. 13),
computed at the profile `qI`. -/
def wI (qI : Fin n → ℝ) (i : Fin n) : ℝ :=
  M.c - ∑ j ∈ univ.erase i, M.dR i j qI

end Model

end RevShareCoord.Competing


