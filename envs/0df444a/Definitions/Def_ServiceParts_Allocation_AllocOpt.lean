-- Prove2me | Definitions.Def_ServiceParts_Allocation_AllocOpt
-- name    : ServiceParts_Allocation_AllocOpt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T22:53:09.095+00:00
-- url     : https://prove2.me/theorems/9fbc68b6-3453-404b-8947-3d6e1ee8c1bf
-- title:
--   Definition 4 — algorithm AllocOpt (marginal allocation), with Remark 2's variant
-- statement:
--   This definition formalizes Algorithm **AllocOpt** (Muckstadt, Definition 4, pp. 178–179), a marginal analysis algorithm for the allocation problem (7.22), on the data of `AllocData`.
--
--   The algorithm keeps, for each location $m \in M$, a current gridpoint index $n^*(m)$ and allocation $r^*(m)$, a current location $m^*$, a running cost $z$ and a number $u$ of units still to be allocated:
--
--   1. For each $m \in M$ and $n \in N_m$, compute $\hat c^m_n$ using (7.19).
--   2. For each $m \in M$, set $n^*(m) \leftarrow 0$ and $r^*(m) \leftarrow 0$.
--   3. Set $m^* = \arg\min_{m \in M} \{\hat c^m_0\}$.
--   4. Set $z \leftarrow \sum_{m \in M} c^m_0$.
--   5. Set $c^0_0 \leftarrow z$.
--   6. Set $n \leftarrow 1$.
--   7. While $n \le n(0)$, do:
--      a) set $u \leftarrow r^0_n - r^0_{n-1}$;
--      b) while $u > 0$, do:
--         (i) if $n^*(m^*) = n(m^*)$ then set $x \leftarrow u$, else set $x \leftarrow u \wedge (r^{m^*}_{n^*(m^*)+1} - r^*(m^*))$;
--         (ii) set $z \leftarrow z + x \cdot \hat c^{m^*}_{n^*(m^*)}$;
--         (iii) set $r^*(m^*) \leftarrow r^*(m^*) + x$;
--         (iv) if $n^*(m^*) < n(m^*)$ and $r^*(m^*) = r^{m^*}_{n^*(m^*)+1}$, then set $n^*(m^*) \leftarrow n^*(m^*) + 1$;
--         (v) set $m^* = \arg\min_{m \in M} \{\hat c^m_{n^*(m)}\}$;
--         (vi) set $u \leftarrow u - x$;
--      c) set $c^0_n \leftarrow z$;
--      d) set $n \leftarrow n + 1$.
--   8. For $n = 0, 1, \dots, n(0)$, set $c^0_n \leftarrow c^0_n + f(r^0_n)$.
--
--   The output is the vector $c^0 = (c^0_n)_{n \in N_0}$. Remark 2 (p. 179) modifies step 7b to read "While $u > 0$ and $\hat c^{m^*}_{n^*(m^*)} \le 0$, do …"; this variant is defined alongside (`allocOptLE`).
--
--   **Formalization Note** The $\arg\min$ in steps 3 and 7(b)v is realised by a selection rule `sel`, a function from slope vectors to locations; the book fixes no tie-breaking, so the theorems quantify over every rule returning a minimizing location (`IsArgminRule`). The outer loop is a recursion on $n$ (`stateAfter`). The inner loop is given a pass budget of $u + \sum_m n(m) + 1$, more than it can use (each pass either sets $u$ to $0$ or advances some $n^*(m)$), so it always exits through its own condition; the definitions are therefore total. `allocOpt k` is $c^0_k$ after step 8, meaningful for $k \le n(0)$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 178-179, Definition 4 (Algorithm AllocOpt) and Remark 2

import Mathlib
import Definitions.Def_ServiceParts_Allocation_AllocData

namespace ServiceParts.Allocation

/-- The variables of algorithm AllocOpt (Definition 4, pp. 178–179): the current gridpoint
index `n*(m)` and allocation `r*(m)` of every location, the current arg min location `m*`,
the running cost `z` and the units `u` still to be allocated in the current outer step. -/
structure AllocState (Mbar : ℕ) where
  nStar : Fin Mbar → ℕ
  rStar : Fin Mbar → ℤ
  mStar : Fin Mbar
  z : ℝ
  u : ℤ

/-- A rule realising the `arg min_{m ∈ M}` of steps 3 and 7(b)v: it returns a location at
which the given vector is minimal. The book does not fix a tie-breaking rule; the results
are stated for every such rule. -/
def IsArgminRule {Mbar : ℕ} (sel : (Fin Mbar → ℝ) → Fin Mbar) : Prop :=
  ∀ g : Fin Mbar → ℝ, ∀ j, g (sel g) ≤ g j

namespace AllocData

variable {Mbar : ℕ} (d : AllocData Mbar) (sel : (Fin Mbar → ℝ) → Fin Mbar)

/-- The vector `(ĉ^m_{n*(m)})_{m ∈ M}` of current slopes. -/
noncomputable def currentSlopes (nStar : Fin Mbar → ℕ) : Fin Mbar → ℝ :=
  fun m => d.slope m (nStar m)

/-- One pass of the inner loop, steps 7(b) i–vi of Definition 4. -/
noncomputable def innerStep (s : AllocState Mbar) : AllocState Mbar :=
  let m := s.mStar
  -- (i) if n*(m*) = n(m*) then x ← u, else x ← u ∧ (r^{m*}_{n*(m*)+1} - r*(m*))
  let x : ℤ := if s.nStar m = d.n m then s.u
    else min s.u (d.grid m (s.nStar m + 1) - s.rStar m)
  -- (ii) z ← z + x · ĉ^{m*}_{n*(m*)}
  let z' : ℝ := s.z + (x : ℝ) * d.slope m (s.nStar m)
  -- (iii) r*(m*) ← r*(m*) + x
  let r' : Fin Mbar → ℤ := Function.update s.rStar m (s.rStar m + x)
  -- (iv) if n*(m*) < n(m*) and r*(m*) = r^{m*}_{n*(m*)+1} then n*(m*) ← n*(m*) + 1
  let n' : Fin Mbar → ℕ :=
    if s.nStar m < d.n m ∧ r' m = d.grid m (s.nStar m + 1) then
      Function.update s.nStar m (s.nStar m + 1)
    else s.nStar
  -- (v) m* ← arg min_{m ∈ M} ĉ^m_{n*(m)}
  let m' := sel (d.currentSlopes n')
  -- (vi) u ← u - x
  { nStar := n', rStar := r', mStar := m', z := z', u := s.u - x }

/-- The inner loop, step 7(b): "While `u > 0`, do (i)–(vi)". With `le = true` the loop
condition is Remark 2's "While `u > 0` and `ĉ^{m*}_{n*(m*)} ≤ 0`". The first argument is
a pass budget; `stateAfter` supplies `u + Σ_m n(m) + 1` passes, more than the loop can use
(every pass either sets `u` to zero or advances some `n*(m)`), so the loop always exits
through its condition. -/
noncomputable def innerLoop (le : Bool) : ℕ → AllocState Mbar → AllocState Mbar
  | 0, s => s
  | k + 1, s =>
    if 0 < s.u ∧ (le = false ∨ d.slope s.mStar (s.nStar s.mStar) ≤ 0) then
      innerLoop le k (d.innerStep sel s)
    else s

/-- Steps 2–5 of Definition 4: `n*(m) ← 0`, `r*(m) ← 0`, `m* ← arg min_m ĉ^m_0`,
`z ← Σ_{m ∈ M} c^m_0` (so that `c^0_0 = z`). -/
noncomputable def initState : AllocState Mbar :=
  { nStar := fun _ => 0
    rStar := fun _ => 0
    mStar := sel (d.currentSlopes fun _ => 0)
    z := ∑ m, d.cost m 0
    u := 0 }

/-- The state of AllocOpt after the outer loop (step 7) has processed `n = 1, …, k`:
for each `n`, (a) `u ← r^0_n - r^0_{n-1}`, then (b) the inner loop. -/
noncomputable def stateAfter (le : Bool) : ℕ → AllocState Mbar
  | 0 => d.initState sel
  | k + 1 =>
    let s : AllocState Mbar := { stateAfter le k with u := d.grid0 (k + 1) - d.grid0 k }
    d.innerLoop sel le (s.u.toNat + ∑ m, d.n m + 1) s

/-- The output `c^0_k` of AllocOpt (with Remark 2's modification if `le = true`):
step 7(c) records `c^0_k ← z` after the `k`-th outer step, and step 8 adds `f(r^0_k)`.
Meaningful for `k = 0, …, n(0)`. -/
noncomputable def allocOptCore (le : Bool) (k : ℕ) : ℝ :=
  (d.stateAfter sel le k).z + d.f (d.grid0 k)

/-- Algorithm AllocOpt, Definition 4 (pp. 178–179): the values `c^0_k`, `k ∈ N₀`. -/
noncomputable def allocOpt (k : ℕ) : ℝ := d.allocOptCore sel false k

/-- Algorithm AllocOpt with Remark 2's inner loop (p. 179):
"While `u > 0` and `ĉ^{m*}_{n*(m*)} ≤ 0`, do …". -/
noncomputable def allocOptLE (k : ℕ) : ℝ := d.allocOptCore sel true k

end AllocData

end ServiceParts.Allocation


