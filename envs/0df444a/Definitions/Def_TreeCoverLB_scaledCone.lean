-- Prove2me | Definitions.Def_TreeCoverLB_scaledCone
-- name    : TreeCoverLB_scaledCone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:44.624764+00:00
-- url     : https://prove2.me/theorems/072699a1-d15d-4a4d-ab0b-ed2c705d0c16
-- title:
--   Scaled cone $C_r$, its base $r|K|$, radial coordinate $\tau$ and Euclidean distance
-- statement:
--   For a complex $K$ on $V$ and $r\ge 0$, the **scaled cone** is
--   $$
--   C_r=rC(K)=\{tx:\ 0\le t\le r,\ x\in|K|\}\subseteq\mathbb R^V,
--   $$
--   with apex $0$ and **base** $r|K|=\{rx: x\in|K|\}$; for $r=1$ it is the cone $C(K)$. The **radial coordinate** is $\tau(tx)=t$, and $\|x-y\|_2=(\sum_v (x_v-y_v)^2)^{1/2}$ is the Euclidean distance.
--
--   **Formalization Note** As in Definition 3.5, the cone is identified with a subset of $\mathbb R^V$ by dropping the apex coordinate. $\tau$ is defined as the coordinate sum $\sum_v z_v$, which equals $t$ for $z=tx$, $x\in|K|$.
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Definition 3.5, p.9 (PDF p.11); §4.1, p.12 (PDF p.14) (C_r, its base, τ)

import Mathlib
import Definitions.Def_TreeCoverLB_realization

namespace TreeCoverLB

/-- The **scaled cone** `C_r = r·C(K) = {t x : 0 ≤ t ≤ r, x ∈ |K|}` over the realization of `K`
(Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Definition 3.5, p.9 (PDF p.11), and §4.1, p.12 (PDF p.14)). For `r = 1` it is the cone
`C(K)`.

**Formalization Note** As in the paper (Definition 3.5: "We will also identify C(K) with a subset of
ℝ^V by dropping the coordinate corresponding to the apex"), the cone lives in `ℝ^V`: its apex is
the origin and its base is `r|K|` (`coneBase`). Dropping the apex coordinate is a linear
homeomorphism from `|K ∗ ∆{v}|` onto `C(K)`. -/
def scaledCone {V : Type*} [Fintype V] (K : Set (Finset V)) (r : ℝ) : Set (V → ℝ) :=
  {z | ∃ t ∈ Set.Icc (0 : ℝ) r, ∃ x ∈ realization K, z = t • x}

/-- The **base** `r|K| = {r x : x ∈ |K|}` of the scaled cone `C_r` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §4.1, p.12 (PDF p.14):
"Its apex is O = 0 and its base is r|K|"). -/
def coneBase {V : Type*} [Fintype V] (K : Set (Finset V)) (r : ℝ) : Set (V → ℝ) :=
  {z | ∃ x ∈ realization K, z = r • x}

/-- The **radial coordinate** `τ` on the cone (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §4.1, p.12 (PDF p.14): `τ(t x) = t` for
`x ∈ |K|`).

**Formalization Note** `τ` is defined as the coordinate sum `Σ_v z_v`; on `C_r` this equals `t`
for `z = t x` because the coordinates of `x ∈ |K|` sum to one (proof of Lemma 4.5, p.13). -/
def radial {V : Type*} [Fintype V] (z : V → ℝ) : ℝ :=
  ∑ v, z v

/-- The **Euclidean distance** `‖x − y‖₂ = (Σ_v (x_v − y_v)²)^{1/2}` on `ℝ^V` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §4,
pp.12–16, the norm `‖·‖₂` of Lemma 4.5, of the mesh, and of the edge weights of `G̃_r`). -/
noncomputable def euclid {V : Type*} [Fintype V] (x y : V → ℝ) : ℝ :=
  Real.sqrt (∑ v, (x v - y v) ^ 2)

end TreeCoverLB


