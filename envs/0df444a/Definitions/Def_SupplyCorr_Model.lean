-- Prove2me | Definitions.Def_SupplyCorr_Model
-- name    : SupplyCorr_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:03.176899+00:00
-- url     : https://prove2.me/theorems/0adad3c2-2cd4-4241-8f70-bce2d058e1c6
-- title:
--   Supply correspondences: (strong) rationalizability, law of supply, maximal monotonicity, homogeneity, profit function (Definitions 1–5)
-- statement:
--   A **supply correspondence** is a map $y:\mathbb R^N\rightrightarrows\mathbb R^N$ assigning to every price vector $p$ a (possibly empty) set $y(p)$ of production plans. Its image is $\operatorname{Im}(y)=\{z\mid \exists p,\ z\in y(p)\}$. For a production set $Y\subseteq\mathbb R^N$ and prices $p$, the set of **optimal plans** is
--
--   $$\operatorname{opt}_Y(p)=\{z\in Y \mid p\cdot z=\sup_{z'\in Y}p\cdot z'\}=\{z\in Y\mid p\cdot z'\le p\cdot z\ \text{for all } z'\in Y\}.$$
--
--   1. (Definition 1) $y$ is **rationalizable** if there is a nonempty convex closed $Y$ with $y(p)\subseteq\operatorname{opt}_Y(p)$ for all $p$.
--   2. (Definition 2) $y$ is **strongly rationalizable** if there is a nonempty convex closed $Y$ with $y(p)=\operatorname{opt}_Y(p)$ for all $p$.
--   3. (Definition 3) $y$ satisfies the **law of supply** if $(p-p')\cdot(z-z')\ge 0$ for all $p,p'$, $z\in y(p)$, $z'\in y(p')$.
--   4. (Definition 4) The **graph** of $y$ is $G(y)=\{(z,p): z\in y(p)\}$; $y$ is **maximal monotone** if $G(y)$ is a maximal monotone subset of $\mathbb R^N\times\mathbb R^N$.
--   5. (Definition 5) $y$ is **homogeneous of degree $0$** if $y(\lambda p)=y(p)$ for all $p$ and all $\lambda>0$.
--
--   For the necessity proof of Theorem 2 the module also defines the **profit function** (support function of $Y$) $\pi_Y(p)=\sup_{z'\in Y}p\cdot z'\in[-\infty,+\infty]$ and the **subdifferential** $\partial f(p)=\{z\mid f(q)\ge f(p)+(q-p)\cdot z\ \text{for all } q\}$ of an extended-real function $f$ on $\mathbb R^N$.
--
--   **Formalization Note** $\mathbb R^N$ is `Fin N → ℝ` with the dot product, for every $N$ (the paper assumes $N\ge 2$). Definitions 1 and 2 are corrected: the paper prints the set $\{z\in\mathbb R^N\mid p\cdot z=\sup_{z'\in Y}p\cdot z'\}$, a hyperplane, while its proofs use $z\in Y$; and $Y$ must be nonempty, since $Y=\emptyset$ would strongly rationalize $y\equiv\emptyset$, which is not maximal monotone. The optimal set is encoded without a real supremum. $\pi_Y$ takes values in the extended reals (`EReal`). The subdifferential pairs subgradients with the dot product, so $\partial\pi_Y$ is a correspondence $\mathbb R^N\rightrightarrows\mathbb R^N$ like $y$.
-- source:
--   Krishnamoorthy–Kushnir, A Simple Characterization of Supply Correspondences, arXiv:2205.10472v1, §2, Definitions 1–5 and the definition of Im(y), pp.3–4; optimal-plan set as in the proofs, pp.5–6; profit function π, p.6

import Mathlib
import Definitions.Def_SupplyCorr_MonotoneSet

open Matrix

namespace SupplyCorr

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, §2, p.3: the image of a supply correspondence
`y : ℝᴺ ⇒ ℝᴺ`, `Im(y) = {z ∈ ℝᴺ | ∃ p ∈ ℝᴺ s.t. z ∈ y(p)}`.

Formalization Note: a correspondence is a map `(Fin N → ℝ) → Set (Fin N → ℝ)`; empty values
are allowed. The printed `z ∈ Rⁿ` is read as `ℝᴺ` (slip). -/
def image {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ)) : Set (Fin N → ℝ) :=
  {z | ∃ p, z ∈ y p}

/-- The set of optimal production plans of a production set `Y` at prices `p`,
`{z ∈ Y | p · z = sup_{z′∈Y} p · z′}`, as written in the proofs of Theorems 1 and 2
(Krishnamoorthy–Kushnir, arXiv:2205.10472v1, pp.5–6).

Formalization Note: encoded as `z ∈ Y ∧ ∀ z' ∈ Y, p ⬝ᵥ z' ≤ p ⬝ᵥ z`, which for `z ∈ Y` is
equivalent to `p · z = sup_{z′∈Y} p · z′` in the extended reals; no real `sSup` (which is `0` on
unbounded sets) is used. -/
def optSet {N : ℕ} (Y : Set (Fin N → ℝ)) (p : Fin N → ℝ) : Set (Fin N → ℝ) :=
  {z | z ∈ Y ∧ ∀ z' ∈ Y, p ⬝ᵥ z' ≤ p ⬝ᵥ z}

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, Definition 1, p.3 (corrected): `y` is
*rationalizable* if there is a nonempty convex and closed production set `Y` with
`y(p) ⊆ {z ∈ Y | p · z = sup_{z′∈Y} p · z′}` for all `p ∈ ℝᴺ`.

Formalization Note: the printed set `{z ∈ ℝᴺ | …}` is read with `z ∈ Y` (as in the proof of
Theorem 1, p.5), and `Y` is required to be nonempty; both changes are those of Definition 2. -/
def IsRationalizable {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ)) : Prop :=
  ∃ Y : Set (Fin N → ℝ), Y.Nonempty ∧ Convex ℝ Y ∧ IsClosed Y ∧ ∀ p, y p ⊆ optSet Y p

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, Definition 2, p.3 (corrected): `y` is
*strongly rationalizable* if there is a nonempty convex and closed production set `Y` with
`y(p) = {z ∈ Y | p · z = sup_{z′∈Y} p · z′}` for all `p ∈ ℝᴺ`.

Formalization Note: two corrections of the printed definition. (1) The printed set
`{z ∈ ℝᴺ | p · z = sup}` is a hyperplane; with it Theorem 2 fails in both directions
(e.g. `N = 2`, `Y = {0}`: `y(p) = {z | p · z = 0}` is not monotone). The proofs on pp.5–6 use
`z ∈ Y`. (2) `Y` is nonempty: `Y = ∅` would strongly rationalize `y ≡ ∅`, whose empty graph is
not maximal monotone. -/
def IsStronglyRationalizable {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ)) : Prop :=
  ∃ Y : Set (Fin N → ℝ), Y.Nonempty ∧ Convex ℝ Y ∧ IsClosed Y ∧ ∀ p, y p = optSet Y p

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, Definition 3, p.3: `y` satisfies the
*law of supply* (is monotone) if `(p − p′) · (z − z′) ≥ 0` for all `p, p′ ∈ ℝᴺ`, `z ∈ y(p)`,
`z′ ∈ y(p′)`. -/
def LawOfSupply {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ)) : Prop :=
  ∀ (p p' z z' : Fin N → ℝ), z ∈ y p → z' ∈ y p' → 0 ≤ (p - p') ⬝ᵥ (z - z')

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, Definition 4, p.4: the graph
`G(y) = {(z, p) : z ∈ y(p)}` of a correspondence, as a subset of `ℝᴺ × ℝᴺ` with the plan first
and the price second. -/
def graph {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ)) : Set ((Fin N → ℝ) × (Fin N → ℝ)) :=
  {q | q.1 ∈ y q.2}

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, Definition 4, p.4: `y` is *maximal monotone*
provided its graph is a maximal monotone set, i.e. maximal among all monotone subsets of
`ℝᴺ × ℝᴺ` ordered by inclusion. -/
def IsMaximalMonotone {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ)) : Prop :=
  IsMaximalMonotoneSet (graph y)

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, Definition 5, p.4: `y` is *homogeneous of
degree 0* if `y(λp) = y(p)` for all `p ∈ ℝᴺ` and `λ > 0`. -/
def IsHomogeneousZero {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ)) : Prop :=
  ∀ (p : Fin N → ℝ) (t : ℝ), 0 < t → y (t • p) = y p

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, proof of Theorem 2, necessity, p.6: the profit
function (support function of `Y`) `π(p) = sup_{z′∈Y} p · z′`.

Formalization Note: valued in `EReal`, so `π(p) = +∞` when `p · z′` is unbounded on `Y` and
`π ≡ −∞` when `Y = ∅`. -/
noncomputable def profitFn {N : ℕ} (Y : Set (Fin N → ℝ)) (p : Fin N → ℝ) : EReal :=
  ⨆ z ∈ Y, ((p ⬝ᵥ z : ℝ) : EReal)

/-- The subdifferential `∂f(p) = {z ∈ ℝᴺ | f(q) ≥ f(p) + (q − p) · z for all q ∈ ℝᴺ}` of an
extended-real function on `ℝᴺ`, with subgradients paired by the dot product (used in the proof
of Theorem 2, necessity, Krishnamoorthy–Kushnir, arXiv:2205.10472v1, p.6).

Formalization Note: the same formula as the platform's `RockafellarMaxMono.Shared.subdiff`,
with `ℝᴺ` identified with its dual through `⬝ᵥ`, so that `∂π` takes values in `Set ℝᴺ` like `y`. -/
def subdiffDot {N : ℕ} (f : (Fin N → ℝ) → EReal) (p : Fin N → ℝ) : Set (Fin N → ℝ) :=
  {z | ∀ q, f p + (((q - p) ⬝ᵥ z : ℝ) : EReal) ≤ f q}

end SupplyCorr


