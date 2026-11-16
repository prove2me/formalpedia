-- Prove2me | Definitions.Def_SubmodSparsify_Supplement_gibbsShare
-- name    : SubmodSparsify_Supplement_gibbsShare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:09:10.387596+00:00
-- url     : https://prove2.me/theorems/6ec1ed25-3739-482b-9634-98b1ce060423
-- title:
--   Shares of a Gibbs distribution (67)–(68)
-- statement:
--   Let $h_1,\dots,h_m : 2^E \to \mathbb R_{\ge 0}$ be monotone submodular with $h_i(\emptyset)=0$, $h = \sum_i h_i$, and let $\beta \ge 1$ be an integer. A coordinate $v$ is **effective** if $h(\{v\}) > 0$; let $D$ be the set of effective coordinates and $d = |D|$. If $d = 0$ every share is $0$. Otherwise the Gibbs distribution $\mu_h$ on $(0,\infty)^D$ has density
--
--   $$\mu_h(dx) = \frac{1}{Z_h}\, e^{-\beta \hat h(x)} \prod_{v \in D} x(v)^{\beta-1}\, dx, \qquad Z_h = \int_{(0,\infty)^D} e^{-\beta \hat h(y)} \prod_{v\in D} y(v)^{\beta-1}\, dy,$$
--
--   where $\hat h$ is the Lovász extension, and the share of $h_i$ is
--
--   $$s_i(h) = \mathbb E_{\mu_h}\, \hat h_i(X).$$
--
--   These shares are the importance scores of Algorithm 6 (Appendix A).
--
--   **Formalization Note** $h$ and the $h_i$ are restricted to the effective coordinates, as in the paper: a point of $(0,\infty)^D$ is extended by $0$ outside $D$ before the base Lovász extension on ground set $D$ is applied. The share is the ratio of two Bochner integrals over the open orthant with Lebesgue measure; for the paper's families both are finite and $Z_h > 0$ (p.47). $\beta$ is a natural number.
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6793d37e5008919a4795e2e18da7fa5049f06ad4d1b929ac6d7fbc634), Appendix A preamble, p.42; §A.1, (67)–(68), p.47

import Mathlib
import Definitions.Def_SubmodSparsify_lovasz
import Definitions.Def_SubmodSparsify_chain

namespace SubmodSparsify.Supplement

/-!
# Shares of a Gibbs distribution ((67)–(68), §A.1, p.47)

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Appendix A preamble p.42, §A.1 p.47.

"Let h1, . . . , hm : 2^E → R≥0 be monotone submodular functions with hi(∅) = 0, and put
h = Σᵢ hᵢ. […] A coordinate v is effective if h({v}) > 0. […] We henceforth restrict h and every
hi to the set of effective coordinates of h, which we still denote by E, and put d = |E|. If
d = 0, all shares and influences below are defined to be zero. For d > 0, let
µh(dx) = (1/Zh) e^{−βĥ(x)} Π_{v∈E} x(v)^{β−1} dx, Zh = ∫_{(0,∞)^E} e^{−βĥ(y)} Π_{v∈E} y(v)^{β−1} dy,
(67) for x ∈ (0, ∞)^E. […] Define si(h) := E_{µh} ĥi(X)" (68), p.47.

**Formalization Note.**
* The ground set is a `Finset E` of an arbitrary type `α`; set functions are `Finset α → ℝ`.
  The effective coordinates form the finset `D = {v ∈ E : h({v}) > 0}`; a point of `(0,∞)^D` is a
  function `x : D → ℝ` with positive values, extended by `0` outside `D` before the Lovász
  extension (base module `SubmodSparsify.lovasz`, ground set `D`) is applied. Restricting to `D`
  is the paper's restriction of `h` and every `hᵢ` to the effective coordinates.
* The inverse temperature `β` is a natural number (Theorem A.1 takes `β ≥ 1` an integer);
  `x(v)^{β−1}` is a natural power. For `β = 0` the value is junk; every statement assumes
  `1 ≤ β`.
* `dx` is Lebesgue measure on `D → ℝ` restricted to the open orthant. The share is the ratio of
  the two Bochner integrals `∫ ĥᵢ(x) e^{−βĥ(x)} Π x(v)^{β−1} dx` and `Z_h`. For normalized
  monotone submodular `hᵢ` both integrands are integrable and `0 < Z_h < ∞` (p.47), so the ratio
  is the paper's expectation; no integrability is assumed in the definition.
* If `d = 0` the share is `0`, as in the paper.
-/

variable {α : Type} [DecidableEq α]

/-- The effective coordinates `{v ∈ E : h({v}) > 0}` of `h`. -/
noncomputable def effective (h : Finset α → ℝ) (E : Finset α) : Finset α := by
  classical exact E.filter (fun v => 0 < h {v})

/-- Extension by zero of a vector on the coordinates `D` to all of `α`. -/
noncomputable def extendZero (D : Finset α) (x : D → ℝ) : α → ℝ :=
  fun v => if hv : v ∈ D then x ⟨v, hv⟩ else 0

/-- The open orthant `(0, ∞)^D`. -/
def orthant (D : Finset α) : Set (D → ℝ) :=
  Set.univ.pi (fun _ => Set.Ioi (0 : ℝ))

/-- The unnormalized Gibbs density `e^{−βĥ(x)} Π_{v∈D} x(v)^{β−1}` of (67). -/
noncomputable def gibbsDensity (β : ℕ) (h : Finset α → ℝ) (D : Finset α) (x : D → ℝ) : ℝ :=
  Real.exp (-(β : ℝ) * lovasz D h (extendZero D x)) * ∏ v, x v ^ (β - 1)

/-- The Gibbs share (68) `s_i(h) = E_{µ_h} ĥ_i(X)` of the family `hs` with sum
`h = Σᵢ hs i` on the ground set `E`, at inverse temperature `β` (`0` when `h` has no effective
coordinate). -/
noncomputable def gibbsShare {ι : Type} [Fintype ι] (β : ℕ) (hs : ι → Finset α → ℝ)
    (E : Finset α) (i : ι) : ℝ :=
  let D := effective (sumFn hs) E
  if D = ∅ then 0 else
    (∫ x in orthant D, lovasz D (hs i) (extendZero D x) * gibbsDensity β (sumFn hs) D x) /
      (∫ x in orthant D, gibbsDensity β (sumFn hs) D x)

end SubmodSparsify.Supplement


