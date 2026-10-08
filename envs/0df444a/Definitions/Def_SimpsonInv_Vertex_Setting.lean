-- Prove2me | Definitions.Def_SimpsonInv_Vertex_Setting
-- name    : SimpsonInv_Vertex_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:07.033975+00:00
-- url     : https://prove2.me/theorems/484c9137-fab3-4b1e-9a58-d1a3c6e6cc29
-- title:
--   Eq. (9) and THEOREM I, pp. 867–869 — the cost c + Σ rᵢ√(Sᵢ₋₁ − Sᵢ + Tᵢ), its domain D, and the coupled model of THEOREM II
-- statement:
--   This file fixes the objects of Simpson's *In-Process Inventories* (1958). A production line has $n$ operations in sequence; behind operation $i$ sits an inventory point whose **service time** $S_i \ge 0$ is the delay it quotes to the next operation. The first and last service times $S_0$ and $S_n$ are given constants, the intermediate ones $S_1, \dots, S_{n-1}$ are the decision variables, and $T_i$ is the processing time of operation $i$.
--
--   1. **The extended vector.** For a choice of the $n-1$ variables, $(S_0, S_1, \dots, S_{n-1}, S_n)$ is the full vector of service times, the two ends being the constants.
--   2. **The radicands.** For $1 \le i \le n$ the $i$-th radicand is $S_{i-1} - S_i + T_i$, the net replenishment time the $i$-th inventory must cover.
--   3. **The cost function** of equation (9) and THEOREM I, with constants $c$ and $r_1, \dots, r_n$:
--   $$
--   f(S_1, \dots, S_{n-1}) \;=\; c + \sum_{i=1}^{n} r_i \sqrt{S_{i-1} - S_i + T_i}.
--   $$
--   4. **The domain** $D \subseteq \mathbb R^{n-1}$ of THEOREM I: the points at which every variable is nonnegative, $S_i \ge 0$ for $1 \le i \le n-1$, and every radicand is nonnegative, $S_{i-1} - S_i + T_i \ge 0$ for $1 \le i \le n$. It is cut out by $2n - 1$ affine inequalities.
--   5. **Tight constraints.** At a point $S$, `tightCount` counts the defining inequalities that hold with equality. `tightNormals` gives their normal vectors, and `tightRank` is the dimension of their linear span.
--   6. **The coupled model of THEOREM II.** Coupling operations $j$ and $j+1$ ($1 \le j \le n-1$) into one operation gives a model with $n - 1$ operations, processing times $T'_i = T_i$ for $i < j$, $T'_j = T_j + T_{j+1}$, $T'_i = T_{i+1}$ for $i > j$, and cost coefficients $r'_i = r_i$ for $i < j$, $r'_i = r_{i+1}$ for $i \ge j$: the inventory $I_j$ disappears with its coefficient $r_j$.
--   7. **The correlated-demand cost** of the *Extension of the main theorem* (p. 871): the square root replaced by a power $t \mapsto t^k$,
--   $$
--   f_k(S_1, \dots, S_{n-1}) \;=\; c + \sum_{i=1}^{n} r_i \,(S_{i-1} - S_i + T_i)^k .
--   $$
--
--   Every theorem of the mission is stated in terms of these objects; $D$ is the feasible set of service-time choices and $f$ the total inventory cost.
--
--   **Formalization Note** With $m = n - 1$ variables, a point of $D$ is `S : Fin m → ℝ`, and the Lean index `j : Fin m` stores the paper's $S_{j+1}$. `extVec S0 Sn S i` is the paper's $S_i$ for every natural $i$ (equal to $S_n$ for $i \ge m+1$). The constants $T$, $r$ are sequences `ℕ → ℝ` read only at the paper's indices $1, \dots, n$. Because `Real.sqrt` returns $0$ on negative inputs, $f$ is only ever compared on $D$. `Real.rpow` is used for $t^k$; on $D$ its base is nonnegative. `tightRank` uses the span of active inequality normals, so duplicate inequalities contribute only one independent direction.
-- source:
--   Simpson, In-Process Inventories, Operations Research 6 (1958), pp. 867–869, equation (9), The domain of the cost function (p. 867–868), THEOREM I (p. 869), THEOREM II (p. 869); Extension of the main theorem, p. 871

import Mathlib

namespace SimpsonInv.Vertex

/-- The extended service-time vector `(S₀, S₁, …, S_{n-1}, S_n)` of Simpson (1958), with `n = m + 1`
operations and `m` free variables. The Lean variable `S : Fin m → ℝ` stores the paper's `S_{j+1}` at
index `j`; `extVec S0 Sn S i` is the paper's `S_i` for every `i : ℕ`, with `S_i = S_n` for `i ≥ m + 1`. -/
def extVec {m : ℕ} (S0 Sn : ℝ) (S : Fin m → ℝ) (i : ℕ) : ℝ :=
  if h0 : i = 0 then S0 else if h : i ≤ m then S ⟨i - 1, by omega⟩ else Sn

/-- The `i`-th radicand `S_{i-1} - S_i + T_i` of equation (9) (used for `1 ≤ i ≤ m + 1`). -/
def radicand {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin m → ℝ) (i : ℕ) : ℝ :=
  extVec S0 Sn S (i - 1) - extVec S0 Sn S i + T i

/-- The cost function of equation (9) and THEOREM I:
`f(S₁, …, S_{n-1}) = c + ∑_{i=1}^{n} r_i √(S_{i-1} - S_i + T_i)` with `n = m + 1`. -/
noncomputable def cost {m : ℕ} (c : ℝ) (r T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin m → ℝ) : ℝ :=
  c + ∑ i ∈ Finset.Icc 1 (m + 1), r i * Real.sqrt (radicand T S0 Sn S i)

/-- The domain `D` of THEOREM I: every variable `S_i` is nonnegative and every radicand
`S_{i-1} - S_i + T_i`, `1 ≤ i ≤ n`, is nonnegative. -/
def dom {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) : Set (Fin m → ℝ) :=
  {S | (∀ j, 0 ≤ S j) ∧ ∀ i ∈ Finset.Icc 1 (m + 1), 0 ≤ radicand T S0 Sn S i}

/-- The number of the `2m + 1` defining inequalities of `D` that are tight (hold with equality) at `S`:
the number of variables `S_j = 0` plus the number of radicands equal to `0`. -/
noncomputable def tightCount {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin m → ℝ) : ℕ :=
  by classical exact
    (Finset.univ.filter (fun j : Fin m => S j = 0)).card +
      ((Finset.Icc 1 (m + 1)).filter (fun i => radicand T S0 Sn S i = 0)).card

/-- The normal vectors of the defining inequalities of `D` that are tight at `S`.
For `S_j ≥ 0` the normal is `e_j`; for the `i`-th radicand it is
`e_{i-2} - e_{i-1}`, omitting coordinates outside `Fin m`. -/
def tightNormals {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin m → ℝ) :
    Set (Fin m → ℝ) :=
  {v | ∃ j : Fin m, S j = 0 ∧ v = (fun k => if k = j then (1 : ℝ) else 0)} ∪
    {v | ∃ i ∈ Finset.Icc 1 (m + 1), radicand T S0 Sn S i = 0 ∧
      v = (fun k => (if k.val + 2 = i then (1 : ℝ) else 0) -
        (if k.val + 1 = i then (1 : ℝ) else 0))}

/-- The number of independent active boundary directions at `S`. In a full-dimensional
polyhedron, rank at least two means that `S` lies beyond the relative interior of a facet. -/
noncomputable def tightRank {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin m → ℝ) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (tightNormals T S0 Sn S))

/-- THEOREM II's processing times after tightly coupling operations `j` and `j + 1` (paper indices):
`T'_i = T_i` for `i < j`, `T'_j = T_j + T_{j+1}`, `T'_i = T_{i+1}` for `i > j`. -/
def coupledT (T : ℕ → ℝ) (j : ℕ) : ℕ → ℝ := fun i =>
  if i < j then T i else if i = j then T j + T (j + 1) else T (i + 1)

/-- THEOREM II's cost coefficients after eliminating inventory `I_j`:
`r'_i = r_i` for `i < j` and `r'_i = r_{i+1}` for `i ≥ j`. -/
def coupledR (r : ℕ → ℝ) (j : ℕ) : ℕ → ℝ := fun i =>
  if i < j then r i else r (i + 1)

/-- The correlated-demand cost of the *Extension of the main theorem* (p. 871): the square root of
equation (9) replaced by the power `t ↦ t ^ k`, i.e. `c + ∑_{i=1}^{n} r_i (S_{i-1} - S_i + T_i)^k`. -/
noncomputable def costPow {m : ℕ} (k c : ℝ) (r T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin m → ℝ) : ℝ :=
  c + ∑ i ∈ Finset.Icc 1 (m + 1), r i * (radicand T S0 Sn S i) ^ k

end SimpsonInv.Vertex


