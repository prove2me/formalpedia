-- Prove2me | Definitions.Def_BorderD4_LowWeightForm
-- name    : BorderD4_LowWeightForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:58.167501+00:00
-- url     : https://prove2.me/theorems/dac07d59-21b6-4e19-b696-53db5269c258
-- title:
--   The border low-weight form of Theorem 6.7
-- statement:
--   A low-weight form of $f\in F[x]$ with parameters $k,\delta,\rho$ consists of: a set $T$ of free coordinates, $u=x_T$, with $N-|T|\le k$; a point $b\in F^N$; for each $a\notin T$ a series $\varphi_a\in F[[\varepsilon,u]]$ and a polynomial $Q_a\in F[[\varepsilon]][u,x_a]$ of degree at most $\Delta=\delta^k$ with
--   $$\varphi_a(\varepsilon,0)=0,\qquad Q_a(u,\varphi_a)=0,\qquad (\partial_{x_a}Q_a)(u,\varphi_a)\text{ an }\varepsilon\text{-unit};$$
--   an integer $k'$ with $0\le k'\le k$; integers $e_i$; and factors $p_{i,j}\in F[[\varepsilon]][x]$ of degree at most $\delta$, at most $\rho$ of them distinct, with each $p_{i,j}(u,\varphi)$ an $\varepsilon$-unit, such that
--   $$\sum_{i=1}^{k'}\varepsilon^{e_i}\prod_j p_{i,j}(u,\varphi)\equiv f(b+(u,\varphi))\pmod\varepsilon.$$
--   This is the conclusion of Theorem 6.7 and the standing situation of §6.3. Also defined: the set `factors` of distinct $p_{i,j}$, and $f_0=f(b+(u,\varphi(0,u)))\in F[[u]]$ of (26).
--
--   **Formalization Note** The sum is computed in the fraction field of $F[[\varepsilon,u]]$, since $e_i$ may be negative, and the congruence carries its witness $S_0\in F[[\varepsilon,u]]$. It is not stated in a quotient of $F[[\varepsilon,x]]$, which need not be a domain (Remark 6.8).
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 6.7, p.52; (26), (27), p.62

import Mathlib
import Definitions.Def_BorderD4_evalAt
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

open Classical in
/-- The data of the border low-weight translation of `f`, Theorem 6.7, which §6.3 fixes as its situation.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 6.7, p.52; (26), (27), p.62.

* `T` is the set of free coordinates, `u = x_T`, with `N − |T| ≤ k`, and `b` is the point;
* Item 1: for `a ∉ T`, `φ_a ∈ F[[ε, u]]` and `Q_a ∈ F[[ε]][u, x_a]` of degree at most `Δ = δ^k`, with
  `φ_a(ε, 0) = 0`, `Q_a(u, φ_a) = 0` and `(∂_{x_a} Q_a)(u, φ_a)` an ε-unit;
* Item 2: `0 ≤ k′ ≤ k`, integers `e_i`, and factors `p_{i,j} ∈ F[[ε]][x]` of degree at most `δ`, at most `ρ` of them
  distinct, with every `p_{i,j}(u, φ)` an ε-unit, and (20):
  `∑_i ε^{e_i} ∏_j p_{i,j}(u, φ) ≡ f(b + (u, φ)) (mod ε)`.

**Formalization Note** `Q_a` is an element of `F[[ε]][x]` whose variables lie in `T ∪ {a}`, so `Q_a(u, φ_a)` is
`Q_a(u, φ)`. Since `e_i` may be negative, the sum in (20) is computed in the fraction field of `F[[ε, u]]`, which
contains `F[[ε, u]]_ε`. The congruence is written with its witness `S₀ ∈ F[[ε, u]]`, so it says exactly what the
page's paragraph after (20) says: the negative powers of `ε` cancel. It is not stated in a quotient of `F[[ε, x]]`
(Remark 6.8, p.53). -/
structure LowWeightForm {F σ : Type*} [Field F] [Fintype σ] [DecidableEq σ]
    (f : MvPolynomial σ F) (k δ ρ : ℕ) where
  /-- The free coordinates. -/
  T : Finset σ
  hT : Fintype.card σ - T.card ≤ k
  /-- The point `b`. -/
  b : σ → F
  /-- The power series `φ_a`. -/
  φ : {a // a ∉ T} → EpsSeries F T
  /-- The polynomials `Q_a`. -/
  Q : {a // a ∉ T} → MvPolynomial σ F⟦X⟧
  hφ0 : ∀ a, PowerSeries.map MvPowerSeries.constantCoeff (φ a) = 0
  hQvars : ∀ a, (Q a).vars ⊆ insert a.1 T
  hQdeg : ∀ a, (Q a).totalDegree ≤ δ ^ k
  hQzero : ∀ a, evalAt T (freeDep T φ) (Q a) = 0
  hQunit : ∀ a, IsEpsUnit (evalAt T (freeDep T φ) (pderiv a.1 (Q a)))
  /-- The number `k′` of surviving summands. -/
  k' : ℕ
  hk' : k' ≤ k
  /-- The integers `e_i`. -/
  e : Fin k' → ℤ
  /-- The factors `p_{i,j}` of each summand. -/
  p : Fin k' → List (MvPolynomial σ F⟦X⟧)
  hpdeg : ∀ i, ∀ q ∈ p i, q.totalDegree ≤ δ
  hpcard : (Finset.univ.biUnion fun i => (p i).toFinset).card ≤ ρ
  hpunit : ∀ i, ∀ q ∈ p i, IsEpsUnit (evalAt T (freeDep T φ) q)
  /-- The witness of the congruence (20), which is `S₀` of (27). -/
  S₀ : EpsSeries F T
  hsum : ∑ i, (algebraMap (EpsSeries F T) (FractionRing (EpsSeries F T)) PowerSeries.X) ^ e i *
        algebraMap (EpsSeries F T) (FractionRing (EpsSeries F T))
          ((p i).map (evalAt T (freeDep T φ))).prod =
      algebraMap (EpsSeries F T) (FractionRing (EpsSeries F T))
        (evalAt T (shifted T b φ) (map PowerSeries.C f) + PowerSeries.X * S₀)

namespace LowWeightForm

variable {F σ : Type*} [Field F] [Fintype σ] [DecidableEq σ] {f : MvPolynomial σ F} {k δ ρ : ℕ}

open Classical in
/-- The set `P` of distinct polynomials among the `p_{i,j}` (p.64). -/
noncomputable def factors (D : LowWeightForm f k δ ρ) : Finset (MvPolynomial σ F⟦X⟧) :=
  Finset.univ.biUnion fun i => (D.p i).toFinset

/-- The power series `f₀ = f(b + (u, φ(0, u))) ∈ F[[u]]` of (26), p.62. -/
noncomputable def f0 (D : LowWeightForm f k δ ρ) : MvPowerSeries D.T F :=
  aeval (uShift D.T D.b fun a => PowerSeries.constantCoeff (D.φ a)) f

end LowWeightForm

end BorderD4


