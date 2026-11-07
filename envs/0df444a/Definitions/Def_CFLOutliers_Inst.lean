-- Prove2me | Definitions.Def_CFLOutliers_Inst
-- name    : CFLOutliers_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:35:26.738069+00:00
-- url     : https://prove2.me/theorems/ddb280de-f97d-4a62-b87f-bbeeedc0fde6
-- title:
--   Instances of capacitated facility location with outliers and the standing assumptions
-- statement:
--   An **instance** of capacitated facility location with outliers (CFLO) consists of
--
--   1. $m$ facilities $F=\{0,\dots,m-1\}$ and $n$ unit-demand clients $C=\{0,\dots,n-1\}$;
--   2. distances $c$ between all points of $F\sqcup C$, with $c_{ij}$ the service cost of client $j$ at facility $i$ and $c_{st}$ the distance between facilities $s,t$;
--   3. an opening cost $f_i$ and an integer capacity $u_i\ge 0$ for each facility $i$;
--   4. a quota $q$: at least $q$ clients must be served (at most $L=n-q$ outliers).
--
--   The **standing assumptions** of the paper are: $c$ is a pseudometric on $F\sqcup C$ ($c(x,x)=0$, symmetric, triangle inequality; distinct points may be at distance $0$), every $f_i\ge 0$, and $q\le n$. Capacities may be $0$ or exceed $n$.
--
--   These are the data of every statement of the mission.
--
--   **Formalization Note** Facilities are `Fin m`, clients `Fin n`, and the distances are one function on `Fin m ⊕ Fin n`. The standing assumptions are the separate predicate `Inst.Std`, which uses the published `MetricMinTest.IsPseudometric`.
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), §1 "Problem and result", p.2

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric

namespace CFLOutliers

/-- **An instance of capacitated facility location with outliers (CFLO).**
Dabas, arXiv:2611.04094, §1 "Problem and result", p.2.

* `m` facilities `Fin m` and `n` unit-demand clients `Fin n`;
* `c`, the distances on the disjoint union `Fin m ⊕ Fin n` (facilities `Sum.inl i`, clients
  `Sum.inr j`);
* `f i`, the opening cost of facility `i`; `u i`, its integer capacity;
* `q`, the quota: at least `q` clients must be served.

**Formalization Note.** The standing assumptions of the paper (`c` a finite metric, `f ≥ 0`,
`q ∈ {0, …, n}`) are the separate predicate `Inst.Std`; capacities are natural numbers, so
`u i ≥ 0` is built in and `u i = 0` is allowed. -/
structure Inst where
  /-- number of facilities -/
  m : ℕ
  /-- number of clients -/
  n : ℕ
  /-- distances between all points (facilities first) -/
  c : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ
  /-- opening costs -/
  f : Fin m → ℝ
  /-- hard capacities -/
  u : Fin m → ℕ
  /-- the quota -/
  q : ℕ

namespace Inst

/-- Service cost `c_{ij}` of serving client `j` from facility `i`. -/
def cFC (I : Inst) (i : Fin I.m) (j : Fin I.n) : ℝ := I.c (Sum.inl i) (Sum.inr j)

/-- Facility–facility distance `c_{st}` (used in the certificates (9), (10), p.8). -/
def cFF (I : Inst) (s t : Fin I.m) : ℝ := I.c (Sum.inl s) (Sum.inl t)

/-- **The standing assumptions** of p.2: the distances form a pseudometric on `F ⊔ C`, every
opening cost is nonnegative, and `q ≤ n`.

**Formalization Note.** A pseudometric rather than a metric (the published
`MetricMinTest.IsPseudometric`: `c x x = 0`, symmetry, triangle inequality): a facility may be
co-located with a client (`generalization`, it covers every metric instance). -/
def Std (I : Inst) : Prop := MetricMinTest.IsPseudometric I.c ∧ (∀ i, 0 ≤ I.f i) ∧ I.q ≤ I.n

end Inst

end CFLOutliers


