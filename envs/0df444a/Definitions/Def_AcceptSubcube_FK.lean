-- Prove2me | Definitions.Def_AcceptSubcube_FK
-- name    : AcceptSubcube_FK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:39.759325+00:00
-- url     : https://prove2.me/theorems/b032e60e-78cb-4adb-8d8d-d1840db42213
-- title:
--   Cheap families $F_K$, $v_\ell(K)$ and $\Sigma(m,v)$
-- statement:
--   For an instance $\mathcal I$ and an integer $K\ge 0$, $F_K$ is the family of assignments of cost at most $K$. Put
--   $$v_\ell(K)=\max\Big\{\lambda\ge0:\binom{\lambda}{\ell}\le 2^\ell K\Big\},\qquad \Sigma(m,v)=\sum_{j=0}^{\min(m,v)}\binom mj .$$
--   A family of vectors is also viewed as a set family (each vector by its set of ones), so that shattering and VC dimension are Mathlib's `Finset.Shatters` and `Finset.vcDim`: a set $\Lambda$ of coordinates is shattered exactly when the family realizes all $2^{|\Lambda|}$ patterns on $\Lambda$.
--
--   These are the objects of Lemma 3.1 (cheap assignments of a complete instance have VC dimension at most $v_\ell(K)$).
--
--   **Formalization Note** $\lambda$ ranges over integers; the maximum is computed below the bound $\ell+2^\ell K$, which every admissible $\lambda$ satisfies for $\ell\ge1$, and equals $\ell-1$ at $K=0$. The mission uses $\ell\ge2$ (p.11).
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), §3.1, p.11 (F_K, v_ℓ(K), Σ(m, v))

import Mathlib
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost

namespace AcceptSubcube

/-- **Cheap family** `F_K`: the assignments of cost at most `K`.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), §3.1, p.11: "Let F_K be the family of
assignments of cost at most K". -/
def FK (I : GInst) (K : ℕ) : Finset (Fin I.n → Bool) :=
  Finset.univ.filter (fun x => cost I x ≤ K)

/-- A family of Boolean vectors as a set family (each vector by its set of ones), so that Mathlib's
`Finset.Shatters` / `Finset.vcDim` apply: a set `Λ` is shattered iff the vectors realize all `2^{|Λ|}`
patterns on `Λ`. -/
def toSets {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Finset (ι → Bool)) : Finset (Finset ι) :=
  F.image (fun x => Finset.univ.filter (fun i => x i = true))

/-- `v_ℓ(K) = max{λ ≥ 0 : (λ choose ℓ) ≤ 2^ℓ K}` (§3.1, p.11), `λ` ranging over integers.

**Formalization Note.** `Nat.findGreatest` up to `ℓ + 2^ℓ K`; for `ℓ ≥ 1` every admissible `λ`
is below this bound (`(λ choose ℓ) ≥ λ − ℓ + 1` for `λ ≥ ℓ`), so this is the paper's maximum; for
`K = 0` it is `ℓ − 1`. The value at `ℓ = 0` (where the set is unbounded) is never used: the mission
uses `ℓ ≥ 2` ("Throughout, ℓ ≥ 2 is the arity", p.11). -/
def vl (ℓ K : ℕ) : ℕ :=
  Nat.findGreatest (fun lam => lam.choose ℓ ≤ 2 ^ ℓ * K) (ℓ + 2 ^ ℓ * K)

/-- `Σ(m, v) = Σ_{j=0}^{min(m,v)} (m choose j)` (§3.1, p.11). -/
def sigmaSum (m v : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min m v + 1), m.choose j

end AcceptSubcube


