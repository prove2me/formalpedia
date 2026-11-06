-- Prove2me | Definitions.Def_UnobservedWelfare_IsRC
-- name    : UnobservedWelfare_IsRC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:43.611779+00:00
-- url     : https://prove2.me/theorems/09c88721-a9a5-49f5-acc7-6f557a9c0d3a
-- title:
--   Market primitives, buyer utilities and radial curvature (RC) at scale $W$
-- statement:
--   One seller supplies $m$ divisible goods. Prices and bundles are vectors in $\mathbb R^m$; $\mathbb R^m_{++}=\{z: z_i>0\ \forall i\}$ is the strictly positive orthant, $p\gg0$ means $p\in\mathbb R^m_{++}$, and $[0,1]^m$ is the production cube.
--
--   1. **Admissible cost.** $c:[0,1]^m\to\mathbb R_+$ is continuous, convex, coordinatewise nondecreasing, with $c(0)=0$. Its **capacity-constrained conjugate** is
--   $$c^*(z)=\max_{q\in[0,1]^m}\{z\cdot q-c(q)\}.$$
--   2. **Surplus and demand.** For a utility $u:\mathbb R^m_+\to\mathbb R\cup\{-\infty\}$,
--   $$S(z)=\sup_{x\ge0}\{u(x)-z\cdot x\},\qquad D(p)=\arg\max_{x\ge0}\{u(x)-p\cdot x\},$$
--   the surplus being allowed to equal $+\infty$ at boundary prices.
--   3. **Buyer utility.** $u$ is concave, upper semicontinuous on $\mathbb R^m_+$, coordinatewise nondecreasing, never $+\infty$ on $\mathbb R^m_+$ and finite on $\mathbb R^m_{++}$. A **buyer model** $(u_\theta)_{\theta\in\Theta}$ has every $u_\theta$ a buyer utility, with $(\theta,x)\mapsto u_\theta(x)$ on $\Theta\times\mathbb R^m_+$ and $(\theta,p)\mapsto S_\theta(p)$ on $\Theta\times\mathbb R^m_{++}$ jointly Borel.
--   4. **Radial curvature (RC) at scale $W>0$.** (1) For every $p\gg0$, $S(p)$ is finite and $D(p)$ is nonempty; (2) for every $x\gg0$, $\lambda\mapsto u(\lambda x)-W\log\lambda$ is convex on $(0,\infty)$.
--   5. **Affine purchase record.** For a transaction at price $p$ with purchase $x$,
--   $$a(z;p,x)=1+\frac{(z-p)\cdot x}{W}.$$
--
--   These are the primitives of the whole mission: RC is the condition under which the paper obtains logarithmic welfare regret, and the affine record is the only information about a buyer that the seller observes.
--
--   **Formalization Note** Goods are `Fin m`, vectors `Fin m → ℝ`. Utilities and surpluses are `EReal`-valued. Concavity of an $\mathbb R\cup\{-\infty\}$-valued utility is convexity of its hypograph over $\mathbb R^m_+$. Values of a utility outside $\mathbb R^m_+$ are unconstrained and never used. In RC (2) the utility is finite along the ray, so its real value is used.
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), §2, pp.15–17 (PDF pp.17–19): Notation, Seller, Production Costs and Their Conjugate, Buyers, Definition 2.1, (27), (28)

import Mathlib

open Matrix

namespace UnobservedWelfare

/-- The strictly positive orthant `ℝ^m_{++} = {z | z ≫ 0}` (Cheng–Tao–Xing, *Maximizing Unobserved
Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), §2 "Notation",
p.15 (PDF p.17)).

**Formalization Note** Goods are indexed by `Fin m` and price/bundle vectors are `Fin m → ℝ`; the
nonnegative orthant `ℝ^m_+` is written `0 ≤ x` with the coordinatewise order. -/
def posOrthant (m : ℕ) : Set (Fin m → ℝ) := {z | ∀ i, 0 < z i}

/-- The production cube `[0,1]^m` (Cheng–Tao–Xing manuscript, §2 "Seller", p.15 (PDF p.17)). -/
def cube (m : ℕ) : Set (Fin m → ℝ) := {q | 0 ≤ q ∧ q ≤ 1}

/-- An admissible production cost (Cheng–Tao–Xing manuscript, §2 "Production Costs and Their
Conjugate", p.16 (PDF p.18)): `c : [0,1]^m → ℝ_+` is continuous, convex, coordinatewise
nondecreasing, with `c(0) = 0`.

**Formalization Note** `c` is a function on all of `Fin m → ℝ`; only its values on the cube are
constrained or ever used. -/
structure IsAdmissibleCost {m : ℕ} (c : (Fin m → ℝ) → ℝ) : Prop where
  continuousOn : ContinuousOn c (cube m)
  convexOn : ConvexOn ℝ (cube m) c
  monotoneOn : MonotoneOn c (cube m)
  map_zero : c 0 = 0
  nonneg : ∀ q ∈ cube m, 0 ≤ c q

/-- The capacity-constrained conjugate `c*(z) = max_{q ∈ [0,1]^m} {z · q − c(q)}`
(Cheng–Tao–Xing manuscript, §2, p.16 (PDF p.18)), the maximum profit from one round of
production at price `z`.

**Formalization Note** Written as `sSup` of the image of the cube; for an admissible (continuous)
cost the image of the compact cube is compact and nonempty, so this is the attained maximum. -/
noncomputable def costConj {m : ℕ} (c : (Fin m → ℝ) → ℝ) (z : Fin m → ℝ) : ℝ :=
  sSup ((fun q => z ⬝ᵥ q - c q) '' cube m)

/-- The surplus `S(z) = sup_{x ≥ 0} {u(x) − z · x}` of a utility `u` at a price `z`
(Cheng–Tao–Xing manuscript, (27), p.16 (PDF p.18); extended to nonnegative `z`, with the value
`+∞` allowed, on p.17 (PDF p.19)).

**Formalization Note** Utilities take values in `EReal` (the paper's `ℝ ∪ {−∞}`), so the surplus
is an `EReal` supremum. -/
noncomputable def surplus {m : ℕ} (u : (Fin m → ℝ) → EReal) (z : Fin m → ℝ) : EReal :=
  ⨆ (x : Fin m → ℝ) (_ : 0 ≤ x), u x - ((z ⬝ᵥ x : ℝ) : EReal)

/-- The demand set `D(p) = argmax_{x ≥ 0} {u(x) − p · x}` (Cheng–Tao–Xing manuscript, (27), p.16
(PDF p.18)): the nonnegative bundles at which utility net of expenditure is maximal. -/
def demand {m : ℕ} (u : (Fin m → ℝ) → EReal) (p : Fin m → ℝ) : Set (Fin m → ℝ) :=
  {x | 0 ≤ x ∧ ∀ y, 0 ≤ y → u y - ((p ⬝ᵥ y : ℝ) : EReal) ≤ u x - ((p ⬝ᵥ x : ℝ) : EReal)}

/-- The standing assumptions on one buyer utility `u : ℝ^m_+ → ℝ ∪ {−∞}` (Cheng–Tao–Xing
manuscript, §2 "Buyers", p.16 (PDF p.18)): concave, upper semicontinuous on `ℝ^m_+`, coordinatewise
nondecreasing, and finite on `ℝ^m_{++}`.

**Formalization Note** Concavity of an `ℝ ∪ {−∞}`-valued function is convexity of its hypograph
`{(x, r) | x ≥ 0, r ≤ u(x)}`. The value `+∞` is excluded on `ℝ^m_+` (the paper's codomain is
`ℝ ∪ {−∞}`). Values of `u` outside `ℝ^m_+` are unconstrained and never used. -/
structure IsBuyerUtility {m : ℕ} (u : (Fin m → ℝ) → EReal) : Prop where
  concave : Convex ℝ {xr : (Fin m → ℝ) × ℝ | 0 ≤ xr.1 ∧ (xr.2 : EReal) ≤ u xr.1}
  usc : UpperSemicontinuousOn u {x | 0 ≤ x}
  monotoneOn : MonotoneOn u {x | 0 ≤ x}
  ne_top : ∀ x, 0 ≤ x → u x ≠ ⊤
  ne_bot : ∀ x ∈ posOrthant m, u x ≠ ⊥

/-- A buyer model on a type space `Θ` (Cheng–Tao–Xing manuscript, §2 "Buyers", p.16 (PDF p.18)):
every `u θ` satisfies the standing utility assumptions, and the maps `(θ, x) ↦ u_θ(x)` on
`Θ × ℝ^m_+` and `(θ, p) ↦ S_θ(p)` on `Θ × ℝ^m_{++}` are jointly Borel measurable. -/
structure IsBuyerModel {m : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (u : Θ → (Fin m → ℝ) → EReal) : Prop where
  utility : ∀ θ, IsBuyerUtility (u θ)
  measurable_utility :
    Measurable (fun q : Θ × {x : Fin m → ℝ // 0 ≤ x} => u q.1 q.2.1)
  measurable_surplus :
    Measurable (fun q : Θ × posOrthant m => surplus (u q.1) q.2.1)

/-- Radial curvature (RC) at scale `W` (Cheng–Tao–Xing manuscript, Definition 2.1, p.16 (PDF
p.18)): (1) for every `p ≫ 0`, `S(p)` is finite and `D(p)` is nonempty; (2) for every `x ≫ 0`,
`λ ↦ u(λx) − W log λ` is convex on `(0, ∞)`. A buyer model satisfies RC at scale `W` when every
`u θ` does.

**Formalization Note** In (2), `u(λx)` is finite because `λx ≫ 0` and a buyer utility is finite
on `ℝ^m_{++}`, so taking `EReal.toReal` loses nothing. The scale `W > 0` is a separate hypothesis
of every statement. -/
structure IsRC {m : ℕ} (W : ℝ) (u : (Fin m → ℝ) → EReal) : Prop where
  surplus_finite : ∀ p ∈ posOrthant m, surplus u p ≠ ⊤ ∧ surplus u p ≠ ⊥
  demand_nonempty : ∀ p ∈ posOrthant m, (demand u p).Nonempty
  radial : ∀ x ∈ posOrthant m,
    ConvexOn ℝ (Set.Ioi 0) (fun l : ℝ => (u (l • x)).toReal - W * Real.log l)

/-- The affine purchase record `a(z; p, x) := 1 + (z − p) · x / W` of a transaction at price `p`
with purchase `x` (Cheng–Tao–Xing manuscript, (28), p.17 (PDF p.19)). -/
noncomputable def affineRecord {m : ℕ} (W : ℝ) (p x z : Fin m → ℝ) : ℝ :=
  1 + ((z - p) ⬝ᵥ x) / W

end UnobservedWelfare


