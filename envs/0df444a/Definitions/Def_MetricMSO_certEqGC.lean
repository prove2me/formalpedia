-- Prove2me | Definitions.Def_MetricMSO_certEqGC
-- name    : MetricMSO_certEqGC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:29.1929+00:00
-- url     : https://prove2.me/theorems/6e508504-4375-4015-9664-05feeb03badf
-- title:
--   The guarded-equidistance certificate $\mathsf{CertEqGC}_M(C,x,y,u,v)$
-- statement:
--   The $\mathrm{MSO}_1$ formula, with $N:=2M+1$,
--   $$\mathsf{CertEqGC}_M(C,x,y,u,v):=\mathsf{Isometric}_M(C)\wedge x,y,u,v\in C\wedge\exists P\exists Q\bigl(\mathsf{Arc}(C,P,x,y)\wedge\mathsf{CertSP}_M(P,x,y)\wedge\mathsf{Arc}(C,Q,u,v)\wedge\mathsf{CertSP}_M(Q,u,v)\wedge\mathsf{EqLen}^C_N(P,x,y,Q,u,v)\bigr).$$
--   $\mathsf{Isometric}_M$ requires that $C$ induces a cycle and that any two distinct vertices of $C$ are joined by an arc satisfying $\mathsf{CertSP}_M$. $\mathsf{EqLen}^C_N$ is the disjunction $\mathsf{Wind}^+_N\vee\mathsf{Wind}^-_N$, where $\mathsf{Wind}^\eta_N$ quantifies a partition $X_0,\dots,X_{N-1}$ of $V(G)$ whose label differences lie in $\{-2,\dots,2\}$ on every edge and equal $\beta^\eta_{P,Q}$ on the edges inside $C$.
--
--   **Formalization Note** The formula is written for a context of `dV` vertex and `dS` vertex-set variables, with fresh levels for its bound variables. The building blocks `Cycle`, `Arc`, `Isometric_M`, `Forw`, `Beta^η_j`, `Diff_j`, `Wind^η_N` and `EqLen^C_N` are written out as on pp.27–28.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §4.3, pp.27–28 (PDF 29–30)

import Mathlib
import Definitions.Def_MetricMSO_certSP

namespace MetricMSO

namespace Builder

/-- **Cycle(C)** (§4.3, p.27 (PDF 29)): "C is nonempty, G[C] is connected, and every vertex of C has
exactly two neighbors in C." -/
def cycle (C : ℕ) : Builder :=
  and (exV fun a => memV a C) (and (conn C) (allV fun a => imp (memV a C) (deg2 a C)))

/-- **Arc(C, P, a, b) := Path(P, a, b) ∧ P ⊆ C** (§4.3, p.27 (PDF 29)). -/
def arc (C P a b : ℕ) : Builder := and (path P a b) (subset P C)

/-- **Isometric_M(C)** (§4.3, p.27 (PDF 29)): "Cycle(C) and, for every two distinct vertices a, b ∈ C,
a set P satisfying Arc(C, P, a, b) ∧ CertSPM(P, a, b)." -/
def isometric (M C : ℕ) : Builder :=
  and (cycle C) (allV fun a => allV fun b =>
    imp (and (memV a C) (and (memV b C) (neg (eqV a b))))
      (exVS fun P => and (arc C P a b) (certSP M P a b)))

/-- **Forw(P, a, b, r, z)** (§4.3, p.27 (PDF 29)): "r, z ∈ P, E(r, z), and a set Z ⊆ P containing
a, r but neither b nor z, such that rz is the only edge of G[P] between Z and P \ Z." -/
def forw (P a b r z : ℕ) : Builder :=
  and (memV r P) (and (memV z P) (and (adj r z) (exVS fun Z =>
    and (subset Z P) (and (memV a Z) (and (memV r Z) (and (neg (memV b Z)) (and (neg (memV z Z))
      (allV fun x => allV fun y =>
        imp (and (memV x Z) (and (memV y P) (and (neg (memV y Z)) (adj x y))))
          (and (eqV x r) (eqV y z))))))))))

/-- `ε_P(r, z) = h` for `h ∈ {−1, 0, 1}` (§4.3, p.27 (PDF 29)): `1` is `Forw(P, s, t, r, z)`, `−1` is
`Forw(P, s, t, z, r)`, and `0` is the negation of both. -/
def eps (P s t r z : ℕ) (h : ℤ) : Builder :=
  if h = 1 then forw P s t r z
  else if h = -1 then forw P s t z r
  else and (neg (forw P s t r z)) (neg (forw P s t z r))

/-- **Beta^η_j(P, s, t, Q, u, v, r, z)** (§4.3, p.27 (PDF 29)), expressing `β^η_{P,Q}(r, z) = j`:
"For η = +, we take the disjunction over the pairs h, k ∈ {−1, 0, 1} with h − k = j, requiring
εP(r, z) = h and εQ(r, z) = k. For η = −, we use the pairs with h + k = j instead." (`η = true` is
`+`.) -/
def beta (η : Bool) (j : ℤ) (P s t Q u v r z : ℕ) : Builder :=
  bigOr (([-1, 0, 1] : List ℤ).flatMap fun h => ([-1, 0, 1] : List ℤ).filterMap fun k =>
    if (if η then h - k else h + k) = j then some (and (eps P s t r z h) (eps Q u v r z k))
    else none)

/-- **Diff^X̄_j(r, z) := ⋁_{i=0}^{N−1} (r ∈ X_i ∧ z ∈ X_{[i+j]_N})** (§4.3, p.27 (PDF 29)), where
`[i + j]_N` is the representative of `i + j` modulo `N` in `{0, …, N − 1}`. -/
def diff (N : ℕ) (X : ℕ → ℕ) (r z : ℕ) (j : ℤ) : Builder :=
  bigOr (List.ofFn fun i : Fin N => and (memV r (X i)) (memV z (X ((((i : ℕ) : ℤ) + j) % N).toNat)))

/-- **Wind^η_N(C, P, s, t, Q, u, v)** (§4.3, pp.27–28 (PDF 29–30)): `∃X_0 ⋯ ∃X_{N−1}` with
`Part_N(X̄)`, and for every ordered pair of adjacent vertices `r, z` at least one of the five
formulas `Diff_j(r, z)` (`j ∈ {−2, …, 2}`), and, if `r, z ∈ C`, at least one of the five
conjunctions `Beta^η_j(P, s, t, Q, u, v, r, z) ∧ Diff_j(r, z)`. -/
def wind (η : Bool) (N : ℕ) (C P s t Q u v : ℕ) : Builder :=
  exVSn N fun X => and (part N X) (allV fun r => allV fun z => imp (adj r z)
    (and (bigOr (([-2, -1, 0, 1, 2] : List ℤ).map fun j => diff N X r z j))
      (imp (and (memV r C) (memV z C))
        (bigOr (([-2, -1, 0, 1, 2] : List ℤ).map fun j =>
          and (beta η j P s t Q u v r z) (diff N X r z j))))))

/-- **EqLen^C_N(P, s, t, Q, u, v) := Wind^+_N ∨ Wind^−_N** (§4.3, p.28 (PDF 30)). -/
def eqLen (N : ℕ) (C P s t Q u v : ℕ) : Builder :=
  or (wind true N C P s t Q u v) (wind false N C P s t Q u v)

/-- **CertEqGC_M(C, x, y, u, v)** (§4.3, p.28 (PDF 30)), with `N := 2M + 1`. -/
def certEqGC (M : ℕ) (C x y u v : ℕ) : Builder :=
  and (isometric M C) (and (memV x C) (and (memV y C) (and (memV u C) (and (memV v C)
    (exVS fun P => exVS fun Q =>
      and (arc C P x y) (and (certSP M P x y) (and (arc C Q u v) (and (certSP M Q u v)
        (eqLen (2 * M + 1) C P x y Q u v)))))))))

end Builder

/-- **The guarded-equidistance certificate `CertEqGC_M(C, x, y, u, v)`.**

Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), §4.3, pp.27–28
(PDF 29–30): "We fix M ≥ 3 and put N := 2M + 1 … We define CertEqGCM(C, x, y, u, v) :=
IsometricM(C) ∧ x ∈ C ∧ y ∈ C ∧ u ∈ C ∧ v ∈ C ∧ ∃P∃Q (Arc(C, P, x, y) ∧ CertSPM(P, x, y) ∧
Arc(C, Q, u, v) ∧ CertSPM(Q, u, v) ∧ EqLen^C_N(P, x, y, Q, u, v))."

`certEqGC M C x y u v dV dS` is this MSO1 formula, written for a context with `dV` vertex and `dS`
vertex-set variables (`C` the level of the set variable, `x, y, u, v` those of the vertex
variables). Its building blocks `Cycle`, `Arc`, `Isometric_M`, `Forw`, `Beta^η_j`, `Diff_j`,
`Wind^η_N`, `EqLen^C_N` are written out as on pp.27–28 (see `Builder.cycle` … `Builder.eqLen`).

**Formalization Note** Fresh bound variables are fresh de Bruijn levels. The canonical formula
`CertEqGC_M(C, x, y, u, v)` of Theorem 1.6 is `certEqGC M 0 0 1 2 3 4 1`. -/
def certEqGC (M : ℕ) (C x y u v : ℕ) (dV dS : ℕ) : Formula :=
  Builder.certEqGC M C x y u v (dV, dS)

end MetricMSO


