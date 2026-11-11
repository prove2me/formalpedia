-- Prove2me | Definitions.Def_RoundedPotentials_Main_EnergyResidual
-- name    : RoundedPotentials_Main_EnergyResidual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T08:34:00.752174+00:00
-- url     : https://prove2.me/theorems/47f956a9-9f9b-4f0b-a5df-17aaa23502a9
-- title:
--   Quadratic energy, residual edge identities, walks and root distances
-- statement:
--   For a capacity-feasible assignment $f$ with prescribed excess $b$, define
--   $$\Phi(f)=\sum_{(u,v):c_{uv}>0}\frac{f_{uv}^2}{2c_{uv}}.$$
--   MinimumEnergy means that $f$ has this excess and has energy no greater than every capacity-feasible assignment with that excess. It asserts a comparison property, without choosing or presupposing a minimizer.
--
--   A residual arc retains an original edge's list position and a direction. For a positive-capacity edge $u\to v$, the forward residual arc exists when $f_{uv}<c_{uv}$ and has length $f_{uv}/c_{uv}$; the backward arc exists when $f_{uv}>0$ and has length $-f_{uv}/c_{uv}$. Residual walks concatenate enabled arcs with matching endpoints, and their length is the sum of arc lengths. Antiparallel input edges therefore remain distinct residual edges.
--
--   A new root has a zero-length arc to every vertex. Equivalently, its distance to $v$ is
--   $$d(v)=\inf\{\ell(w):w\text{ is a finite residual walk from any vertex to }v\}.$$
--   The infimum is taken in the extended reals, permitting $-\infty$ before optimality is established. The empty walk ensures a zero candidate for every vertex. Define $y_v=-d(v)$ after conversion to a real value; outside the finite-distance regime this conversion returns zero. Lemma 3.4 explicitly establishes finiteness, so it never relies on that default.
--
--   This layer supplies the common objects for residual optimality and clipped-potential representation; it does not build either claimed property into the graph or distance.
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), pp. 13–15, §3.2, eqs. (8), (9), residual optimality and shortest-path construction

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Certificate

namespace RoundedPotentials.Main
open scoped BigOperators

noncomputable def energy {n W : ℕ} (I : Instance n W) (f : Assignment n) : ℝ :=
  ∑ u, ∑ v, if 0 < capNat I u v then f u v ^ 2 / (2 * (capNat I u v : ℝ)) else 0

def MinimumEnergy {n W : ℕ} (I : Instance n W) (b : Fin n → ℝ) (f : Assignment n) : Prop :=
  CapacityFeasible I f ∧ HasExcess f b ∧
    ∀ g : Assignment n, CapacityFeasible I g → HasExcess g b → energy I f ≤ energy I g

/-- An original edge position and its direction; parallel residual edges remain distinct. -/
structure ResidualArc {n W : ℕ} (I : Instance n W) where
  edge : Fin I.edges.length
  backward : Bool

def residualTail {n W : ℕ} {I : Instance n W} (a : ResidualArc I) : Fin n :=
  let e := I.edges.get a.edge
  if a.backward then e.2.1 else e.1

def residualHead {n W : ℕ} {I : Instance n W} (a : ResidualArc I) : Fin n :=
  let e := I.edges.get a.edge
  if a.backward then e.1 else e.2.1

def ResidualEnabled {n W : ℕ} {I : Instance n W} (f : Assignment n) (a : ResidualArc I) : Prop :=
  let e := I.edges.get a.edge
  0 < e.2.2 ∧ if a.backward then 0 < f e.1 e.2.1 else f e.1 e.2.1 < (e.2.2 : ℝ)

noncomputable def residualLength {n W : ℕ} {I : Instance n W}
    (f : Assignment n) (a : ResidualArc I) : ℝ :=
  let e := I.edges.get a.edge
  let x := f e.1 e.2.1 / (e.2.2 : ℝ)
  if a.backward then -x else x

inductive ResidualWalk {n W : ℕ} (I : Instance n W) (f : Assignment n) : Fin n → Fin n → Type
  | nil (v : Fin n) : ResidualWalk I f v v
  | cons (a : ResidualArc I) (enabled : ResidualEnabled f a) {v : Fin n}
      (rest : ResidualWalk I f (residualHead a) v) : ResidualWalk I f (residualTail a) v

noncomputable def walkLength {n W : ℕ} {I : Instance n W} {f : Assignment n}
    {u v : Fin n} : ResidualWalk I f u v → ℝ
  | .nil _ => 0
  | .cons a _ rest => residualLength f a + walkLength rest

/-- The zero root edge may end at ANY start vertex. All finite walks, with no length cutoff. -/
noncomputable def rootDistance {n W : ℕ} (I : Instance n W) (f : Assignment n) (v : Fin n) : EReal :=
  sInf {d : EReal | ∃ u : Fin n, ∃ w : ResidualWalk I f u v, d = (walkLength w : EReal)}

/-- Defined even for a negative cycle; Lemma 3.4 separately proves distance finiteness. -/
noncomputable def shortestPotential {n W : ℕ} (I : Instance n W) (f : Assignment n) : Fin n → ℝ :=
  fun v => -(rootDistance I f v).toReal

end RoundedPotentials.Main


