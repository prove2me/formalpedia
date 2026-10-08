-- Prove2me | Definitions.Def_BNCovPack_Routing_FracScheme
-- name    : BNCovPack_Routing_FracScheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:54:18.032668+00:00
-- url     : https://prove2.me/theorems/b134c2c6-c626-4249-9d57-548aedbde924
-- title:
--   The {0,1} online fractional packing scheme with an oracle, run on routing (Section 3)
-- statement:
--   This is the online primal–dual scheme of Section 3 of the paper, in its $\{0,1\}$ form with parameter $\ell$ and with an oracle for Line (ii), applied to the routing problem.
--
--   The primal (covering) side has a variable $x(e) \ge 0$ of cost $u(e)$ for each edge and a variable $Z(r_i) \ge 0$ of cost $1$ for each request, with one constraint $\sum_{e \in P} x(e) + Z(r_i) \ge 1$ for every request $r_i$ and path $P \in \mathcal P(r_i)$. The dual (packing) variables are the flows $f(r_i, P)$. Initially all variables are zero.
--
--   When request $r_i$ arrives, $Z(r_i) = 0$, and its paths are visited in the order of $\mathcal P(r_i)$. For a path $P$ whose constraint already holds, $f(r_i, P) = 0$. Otherwise $f(r_i, P)$ is raised from $0$ to the least value $y \ge 0$ for which the constraint holds, where during the increase
--
--   $$
--   x(e) \leftarrow \max\Big(x(e),\ \tfrac{1}{\ell}\big(e^{\frac{B}{2u(e)} F_e} - 1\big)\Big)\ (e \in P), \qquad Z(r_i) \leftarrow \max\Big(Z(r_i),\ \tfrac{1}{\ell}\big(e^{\frac{B}{2} f(r_i)} - 1\big)\Big),
--   $$
--
--   with $F_e$ the total flow through $e$ and $f(r_i) = \sum_P f(r_i, P)$, both including the current value $y$. The loads, $f(r_i)$ and the recorded flows are then updated.
--
--   The paper uses this scheme with $\ell = P(\max) + 1$ (a primal constraint involves at most $P(\max)$ edge variables and $Z(r_i)$) to generate a feasible near-optimal fractional routing online.
--
--   **Formalization Note** The continuous increase is replaced by its discrete equivalent: the least $y$ is an `sInf`, which is attained for $\ell \ge 1$ and $B > 0$ (the $Z$-term grows without bound). Line (ii)b also re-applies the maximum to $x(e)$ for $e \notin P$; their exponent does not change, so this is omitted. The oracle reports unsatisfied constraints in list order.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 4–5, Section 3, Lines (i)–(ii), the {0,1} case and the oracle remark; p. 14, Section 5.2

import Mathlib

namespace BNCovPack.Routing

/-! The Section 3 online fractional packing scheme with `{0,1}` coefficients and the oracle for
Line (ii), run on the routing problem of §5.2 (Buchbinder–Naor 2009, p. 5 and pp. 14–15).

Round `i` introduces the dual variables `f(r_i, P)`, `P ∈ P(r_i)`, and the primal constraints
`∑_{e ∈ P} x(e) + Z(r_i) ≥ 1`. The oracle reports the unsatisfied constraints in the order of the
list `P(r_i)`; for each one, the single-variable round of §3 is run with `a(i, j) ∈ {0,1}`,
`a_i(max) = 1`, `n` replaced by `ℓ`, cost `c = u(e)` for `x(e)` and cost `c = 1` for `Z(r_i)`. -/

/-- State of the fractional scheme between requests:
* `x e` is the primal variable `x(e)`;
* `load e` is `∑_{r_i} ∑_{P ∋ e} f(r_i, P)`, the flow through `e` so far (the exponent's sum
  `∑_k a(i,k) y(k)` of Line (ii)b for the primal variable `x(e)`);
* `flows` lists, request by request in arrival order, the flows `f(r_i, P)` on the paths of
  `P(r_i)` (in the order of `P(r_i)`). -/
structure FracState (E : Type*) where
  x : E → ℝ
  load : E → ℝ
  flows : List (List ℝ)

/-- Initially all variables are zero (p. 4) and no request has arrived. -/
def FracState.init (E : Type*) : FracState E where
  x := fun _ => 0
  load := fun _ => 0
  flows := []

/-- State inside a round, while the paths of the current request `r_i` are processed:
* `x`, `load` as in `FracState`;
* `Z` is the primal variable `Z(r_i)` of the current request (zero when it arrives);
* `fr` is `f(r_i) = ∑_P f(r_i, P)` so far;
* `fs` is the list of flows given to the paths of `r_i` processed so far. -/
structure RoundState (E : Type*) where
  x : E → ℝ
  load : E → ℝ
  Z : ℝ
  fr : ℝ
  fs : List ℝ

/-- Line (ii)b for `x(e)` (p. 5): `(1/ℓ)(exp((B/(2 u(e)))·t) − 1)` at flow `t` through `e`. -/
noncomputable def xCurve {E : Type*} (u : E → ℝ) (ℓ : ℕ) (B : ℝ) (e : E) (t : ℝ) : ℝ :=
  (1 / (ℓ : ℝ)) * (Real.exp (B / (2 * u e) * t) - 1)

/-- Line (ii)b for `Z(r_i)` (cost `1`): `(1/ℓ)(exp((B/2)·t) − 1)` at flow `t = f(r_i)`. -/
noncomputable def zCurve (ℓ : ℕ) (B : ℝ) (t : ℝ) : ℝ :=
  (1 / (ℓ : ℝ)) * (Real.exp (B / 2 * t) - 1)

/-- The left-hand side `∑_{e ∈ P} x(e) + Z(r_i)` of the primal constraint of path `P`, when the
dual variable `f(r_i, P)` has been raised to `y` from the round state `rs`: every `x(e)`, `e ∈ P`,
is `max(x(e), xCurve(load e + y))` and `Z(r_i)` is `max(Z, zCurve(fr + y))`. -/
noncomputable def pathLHS {E : Type*} (u : E → ℝ) (ℓ : ℕ) (B : ℝ) (rs : RoundState E)
    (P : Finset E) (y : ℝ) : ℝ :=
  ∑ e ∈ P, max (rs.x e) (xCurve u ℓ B e (rs.load e + y)) + max rs.Z (zCurve ℓ B (rs.fr + y))

/-- The value given to `f(r_i, P)` (p. 4–5: "find the minimal `y(j)` such that the new primal
constraint is satisfied"): the least `y ≥ 0` with `pathLHS … y ≥ 1`. For `ℓ ≥ 1` and `B > 0`
the set is non-empty (the `Z` term grows without bound), closed and bounded below, so the
infimum is attained. -/
noncomputable def pathIncrement {E : Type*} (u : E → ℝ) (ℓ : ℕ) (B : ℝ) (rs : RoundState E)
    (P : Finset E) : ℝ :=
  sInf {y : ℝ | 0 ≤ y ∧ 1 ≤ pathLHS u ℓ B rs P y}

open Classical in
/-- The oracle step for path `P` of the current request (Line (ii), p. 5, with the oracle remark):
if the constraint `∑_{e ∈ P} x(e) + Z(r_i) ≥ 1` already holds, `f(r_i, P) = 0` and nothing
changes; otherwise `f(r_i, P) := pathIncrement`, and `x(e)` (`e ∈ P`), the loads, `Z(r_i)` and
`f(r_i)` are updated accordingly. (Line (ii)b also re-applies the max to `x(e)` for `e ∉ P`; their
exponent does not change, so this is a no-op and is omitted.) -/
noncomputable def pathStep {E : Type*} [DecidableEq E] (u : E → ℝ) (ℓ : ℕ) (B : ℝ)
    (rs : RoundState E) (P : Finset E) : RoundState E :=
  if 1 ≤ ∑ e ∈ P, rs.x e + rs.Z then { rs with fs := rs.fs ++ [0] }
  else
    let y := pathIncrement u ℓ B rs P
    { x := fun e => if e ∈ P then max (rs.x e) (xCurve u ℓ B e (rs.load e + y)) else rs.x e
      load := fun e => if e ∈ P then rs.load e + y else rs.load e
      Z := max rs.Z (zCurve ℓ B (rs.fr + y))
      fr := rs.fr + y
      fs := rs.fs ++ [y] }

/-- One round of the fractional scheme: request `r_i` with path list `ps = P(r_i)` arrives,
`Z(r_i)` starts at `0`, the paths are handed over by the oracle in the order of `ps`, and the
flows `f(r_i, ·)` are appended to `flows`. -/
noncomputable def fracStep {E : Type*} [DecidableEq E] (u : E → ℝ) (ℓ : ℕ) (B : ℝ)
    (st : FracState E) (ps : List (Finset E)) : FracState E :=
  let rs := ps.foldl (pathStep u ℓ B) ⟨st.x, st.load, 0, 0, []⟩
  { x := rs.x, load := rs.load, flows := st.flows ++ [rs.fs] }

/-- The state of the fractional scheme with parameters `ℓ` and `B` after the requests of `σ` have
arrived, in order, from the all-zero state. -/
noncomputable def fracRun {E : Type*} [DecidableEq E] (u : E → ℝ) (ℓ : ℕ) (B : ℝ)
    (σ : List (List (Finset E))) : FracState E :=
  σ.foldl (fracStep u ℓ B) (FracState.init E)

end BNCovPack.Routing


