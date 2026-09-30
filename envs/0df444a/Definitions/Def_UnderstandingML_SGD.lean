-- Prove2me | Definitions.Def_UnderstandingML_SGD
-- name    : UnderstandingML_SGD
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T04:23:27.35507+00:00
-- url     : https://prove2.me/theorems/c9ea7d65-9863-4a2d-aff7-dad3baf5564a
-- title:
--   Chapter 14: subgradients (Def. 14.4), gradient-descent iterates (14.4), projections, SGD driven by a sample with a subgradient oracle, the strongly convex variant with projections
-- statement:
--   Chapter 14 of Shalev-Shwartz and Ben-David. **Definition 14.4:** $v$ is a subgradient of $f$ at $w$ if $f(u) \ge f(w) + \langle u - w, v\rangle$ for all $u$ (`IsSubgradient`); the differential set $\partial f(w)$ (`subdifferential`). The hinge-loss subgradient of Example 14.2 (`hingeSubgradient`). **(14.4):** the iterates $w^{(1)} = 0$, $w^{(t+1)} = w^{(t)} - \eta v_t$ of any sequence of directions (`gdIterates`, indexed from $0$) and the average $\bar w = \frac1T\sum_{t<T} w^{(t)}$ (`gdAverage`). **Projection (§14.4.1):** $v$ is a projection of $w$ onto $H$ if $v \in H$ minimizes $\|x - w\|$ over $H$ (`IsProjection`, `projOnto`). **SGD (§14.3, §14.5):** driven by a sample $S = (z_0, \dots, z_{T-1}) \sim D^T$ and an oracle $g$, $w^{(t+1)} = w^{(t)} - \eta\, g(w^{(t)}, z_t)$ (`sgdIterates`, `sgdAverage`); $g$ is a stochastic subgradient oracle for $f$ if $\mathbb{E}_{z \sim D}\, g(w, z) \in \partial f(w)$ for every $w$ (`IsSubgradientOracle`), and a loss-subgradient selector if $g(w,z) \in \partial\ell(\cdot,z)(w)$ for all $w, z$ (`IsLossSubgradientSelector`). **Strongly convex variant (§14.4.4):** $w^{(t+1)} = \operatorname{proj}_H\big(w^{(t)} - \frac{1}{\lambda(t+1)} g(w^{(t)}, z_t)\big)$, the book's $\eta_t = 1/(\lambda t)$ (`sgdStrongIterates`, `sgdStrongAverage`).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §14.1 (14.4) p. 187, §14.2 Definition 14.4 p. 188 and Example 14.2 p. 190, §14.3 pp. 191-192, §14.4.1 p. 193, §14.4.4 p. 195, §14.5.1 p. 197

import Definitions.Def_UnderstandingML_Convex

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 14:
# stochastic gradient descent

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §14.1–§14.5.

**Gradient descent (§14.1).** `w⁽¹⁾ = 0`, `w⁽ᵗ⁺¹⁾ = w⁽ᵗ⁾ − η vₜ` (14.4) with `vₜ = ∇f(w⁽ᵗ⁾)`,
output `w̄ = (1/T) ∑ₜ w⁽ᵗ⁾`.

**Subgradients (Definition 14.4).** `v` is a subgradient of `f` at `w` if
`f(u) ≥ f(w) + ⟨u − w, v⟩` for all `u`; the differential set is `∂f(w)`.

**SGD (§14.3).** `w⁽¹⁾ = 0`; at step `t` a random `vₜ` with `E[vₜ | w⁽ᵗ⁾] ∈ ∂f(w⁽ᵗ⁾)`;
`w⁽ᵗ⁺¹⁾ = w⁽ᵗ⁾ − η vₜ`; output `w̄`. The randomness is modelled as in §14.5: `vₜ = g(w⁽ᵗ⁾, zₜ)`
for a fresh example `zₜ ∼ D` and an oracle `g` whose expectation `E_z g(w, z)` is a subgradient
of `f` at `w`. For learning, `g(w, z)` is a subgradient of `ℓ(·, z)` at `w`, so that
`E_z g(w, z) ∈ ∂L_D(w)` (14.13).

**Projections and strong convexity (§14.4).** The projection of `w` onto a closed convex `H` is
`argmin_{x ∈ H} ‖x − w‖`; the strongly convex variant uses `ηₜ = 1/(λt)` and a projection after
each step.

**Conventions.** Iterates are indexed from `0`, so `gdIterates η v 0` is the book's `w⁽¹⁾` and
`gdIterates η v t` is `w⁽ᵗ⁺¹⁾`; the average over `T` steps is over `t = 0, …, T − 1`. The SGD
iterates driven by a finite sample `S : Fin T → Z` stop updating after `T` steps. The projection
`projOnto H w` is some nearest point when one exists (it is unique for closed convex `H`).
-/

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

section Subgradients

variable {d : ℕ}

/-- **Definition 14.4**: `v` is a **subgradient** of `f` at `w`, `∀ u, f(u) ≥ f(w) + ⟨u − w, v⟩`. -/
def IsSubgradient (f : Vec d → ℝ) (w v : Vec d) : Prop :=
  ∀ u, f w + ⟪u - w, v⟫_ℝ ≤ f u

/-- The **differential set** `∂f(w)` (Definition 14.4). -/
def subdifferential (f : Vec d → ℝ) (w : Vec d) : Set (Vec d) := {v | IsSubgradient f w v}

/-- A subgradient of the hinge loss at `w` (Example 14.2): `0` if `1 − y⟨w, x⟩ ≤ 0`, else `−y x`. -/
noncomputable def hingeSubgradient (w : Vec d) (z : Vec d × ℝ) : Vec d :=
  if 1 - z.2 * ⟪w, z.1⟫_ℝ ≤ 0 then 0 else -(z.2 • z.1)

/-- **The projection lemma's projection**: `v` is a projection of `w` onto `H`, a point of `H`
closest to `w` (§14.4.1). -/
def IsProjection (H : Set (Vec d)) (w v : Vec d) : Prop :=
  v ∈ H ∧ ∀ x ∈ H, ‖v - w‖ ≤ ‖x - w‖

/-- A projection of `w` onto `H` when one exists (unique for closed convex `H`), else `w`. -/
noncomputable def projOnto (H : Set (Vec d)) (w : Vec d) : Vec d := by
  classical exact if h : ∃ v, IsProjection H w v then Classical.choose h else w

end Subgradients

section Descent

variable {d : ℕ}

/-- The iterates of an update rule `w⁽¹⁾ = 0`, `w⁽ᵗ⁺¹⁾ = w⁽ᵗ⁾ − η vₜ` (14.4), indexed from `0`. -/
noncomputable def gdIterates (η : ℝ) (v : ℕ → Vec d) : ℕ → Vec d
  | 0 => 0
  | t + 1 => gdIterates η v t - η • v t

/-- The averaged output `w̄ = (1/T) ∑_{t < T} w⁽ᵗ⁾` of `T` steps of (14.4). -/
noncomputable def gdAverage (η : ℝ) (v : ℕ → Vec d) (T : ℕ) : Vec d :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, gdIterates η v t

end Descent

section SGD

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

/-- **SGD driven by a sample** (§14.3, §14.5): `w⁽⁰⁾ = 0` and `w⁽ᵗ⁺¹⁾ = w⁽ᵗ⁾ − η g(w⁽ᵗ⁾, zₜ)` for
`t < T`, where `g` is the (sub)gradient oracle and `zₜ` the `t`-th example of `S`. -/
noncomputable def sgdIterates (η : ℝ) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z) :
    ℕ → Vec d
  | 0 => 0
  | t + 1 =>
    let w := sgdIterates η g S t
    w - η • (if h : t < T then g w (S ⟨t, h⟩) else 0)

/-- The averaged output `w̄ = (1/T) ∑_{t < T} w⁽ᵗ⁾` of SGD on the sample `S`. -/
noncomputable def sgdAverage (η : ℝ) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z) : Vec d :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, sgdIterates η g S t

/-- `g` is a **stochastic subgradient oracle** for `f` under `D`: for every `w`, the expected
direction `E_{z ∼ D} g(w, z)` is a subgradient of `f` at `w` (§14.3). -/
def IsSubgradientOracle (f : Vec d → ℝ) (D : Measure Z) (g : Vec d → Z → Vec d) : Prop :=
  ∀ w, IsSubgradient f w (∫ z, g w z ∂D)

/-- `g` selects subgradients of the loss: `g(w, z) ∈ ∂ℓ(·, z)(w)` for all `w, z` (§14.5.1). -/
def IsLossSubgradientSelector (loss : Vec d → Z → ℝ) (g : Vec d → Z → Vec d) : Prop :=
  ∀ w z, IsSubgradient (fun w ↦ loss w z) w (g w z)

/-- **SGD for a strongly convex objective with projections** (§14.4.4): `w⁽⁰⁾ = 0` and
`w⁽ᵗ⁺¹⁾ = proj_H (w⁽ᵗ⁾ − (1/(λ(t+1))) g(w⁽ᵗ⁾, zₜ))`, the book's `ηₜ = 1/(λt)` with `t` from `1`. -/
noncomputable def sgdStrongIterates (lam : ℝ) (H : Set (Vec d)) (g : Vec d → Z → Vec d) {T : ℕ}
    (S : Fin T → Z) : ℕ → Vec d
  | 0 => 0
  | t + 1 =>
    let w := sgdStrongIterates lam H g S t
    projOnto H (w - (1 / (lam * (t + 1))) • (if h : t < T then g w (S ⟨t, h⟩) else 0))

/-- The averaged output of the strongly convex variant. -/
noncomputable def sgdStrongAverage (lam : ℝ) (H : Set (Vec d)) (g : Vec d → Z → Vec d) {T : ℕ}
    (S : Fin T → Z) : Vec d :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, sgdStrongIterates lam H g S t

end SGD

end UnderstandingML


