-- Prove2me | Definitions.Def_AppliedComb_Flows_AugmentingPath
-- name    : AppliedComb_Flows_AugmentingPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:38:21.997173+00:00
-- url     : https://prove2.me/theorems/a96d3e2d-6353-40e9-9e28-2bf56225d906
-- title:
--   Augmenting paths, the amount δ, and the augmented flow (Section 13.3)
-- statement:
--   Let $\phi$ be a flow in a network with source $S$ and sink $T$. An edge $(x, y)$ is **used** if $\phi(x, y) > 0$ and **has spare capacity** if $\phi(x, y) < c(x, y)$.
--
--   An **augmenting path** is a sequence $P = (x_0, x_1, \dots, x_m)$ of distinct vertices with $x_0 = S$, $x_m = T$, such that for each $i = 1, \dots, m$ either (a) $(x_{i-1}, x_i)$ is an edge with spare capacity, or (b) $(x_i, x_{i-1})$ is an edge that is used. In case (a) the edge $(x_{i-1}, x_i)$ is a **forward edge** of $P$; in case (b) it is a **backward edge** (the path traverses the edge $(x_i, x_{i-1})$ against its direction). Augmenting paths need not be directed paths.
--
--   The amount of augmentation is
--   $$\delta_1 = \min\{c(x_{i-1}, x_i) - \phi(x_{i-1}, x_i) : (x_{i-1}, x_i) \text{ forward}\},\qquad \delta_2 = \min\{\phi(x_i, x_{i-1}) : (x_{i-1}, x_i) \text{ backward}\},$$
--   with $\delta = \delta_1$ when $P$ has no backward edge and $\delta = \min\{\delta_1, \delta_2\}$ otherwise. The **augmented function** $\hat\phi$ increases $\phi$ by $\delta$ on every forward edge of $P$, decreases it by $\delta$ on every backward edge of $P$, and leaves all other values unchanged.
--
--   These notions are used in Proposition 13.7 and in the Ford–Fulkerson labeling algorithm.
--
--   **Formalization Note.** The path is a function `x : Fin (m + 1) → V`; the step from $x_{i-1}$ to $x_i$ is indexed by `i : Fin m`, with $x_{i-1}$ = `x i.castSucc` and $x_i$ = `x i.succ`. Distinctness is injectivity of `x`. Whether a step is forward or backward is read off the direction of the network edge between its endpoints (the graph is oriented, so at most one direction is an edge). $\delta_1$, $\delta_2$ and $\delta$ take values in `WithTop ℝ`: a minimum over an empty set is $\top$, so $\delta_2 = \top$ exactly when $P$ has no backward edge, and then $\delta = \min(\delta_1, \top) = \delta_1$ as the book prescribes; $\delta_1$ is finite for every augmenting path because its first edge leaves $S$ and is therefore forward. The augmented function `augment ϕ x δ` takes the real number $\delta$ as an argument.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), pp. 264–265, Section 13.3 (used, spare capacity, augmenting path, forward/backward edges, δ₁, δ₂, δ)

import Mathlib
import Definitions.Def_AppliedComb_Flows_Network

namespace AppliedComb.Flows

namespace Network

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge `(x, y)` **has spare capacity** for the flow `ϕ` (Keller & Trotter, *Applied
Combinatorics*, 2017 Edition, p. 264): it is an edge of the network and `ϕ(x, y) < c(x, y)`. -/
def HasSpareCapacity (N : Network V) (ϕ : V → V → ℝ) (x y : V) : Prop :=
  N.adj x y ∧ ϕ x y < N.cap x y

/-- The edge `(x, y)` is **used** by the flow `ϕ` (p. 264): it is an edge of the network and
`ϕ(x, y) > 0`. -/
def IsUsed (N : Network V) (ϕ : V → V → ℝ) (x y : V) : Prop :=
  N.adj x y ∧ 0 < ϕ x y

/-- An **augmenting path** for the flow `ϕ` (p. 264): a sequence `P = (x₀, x₁, …, xₘ)` of
distinct vertices, written `x : Fin (m + 1) → V`, with `x₀ = S`, `xₘ = T`, such that for each
`i = 1, …, m` either
(a) `(x_{i-1}, x_i)` has spare capacity, or
(b) `(x_i, x_{i-1})` is used.
In Lean the step from `x_{i-1}` to `x_i` is indexed by `i : Fin m`, with
`x_{i-1} = x i.castSucc` and `x_i = x i.succ`. -/
def IsAugmentingPath (N : Network V) (ϕ : V → V → ℝ) {m : ℕ} (x : Fin (m + 1) → V) : Prop :=
  Function.Injective x ∧ x 0 = N.S ∧ x (Fin.last m) = N.T ∧
  ∀ i : Fin m, N.HasSpareCapacity ϕ (x i.castSucc) (x i.succ) ∨
    N.IsUsed ϕ (x i.succ) (x i.castSucc)

/-- The step `i` of the path `x` (from `x_{i-1} = x i.castSucc` to `x_i = x i.succ`) is a
**forward edge** (p. 264): `(x_{i-1}, x_i)` is a directed edge of the network. -/
def IsForward (N : Network V) {m : ℕ} (x : Fin (m + 1) → V) (i : Fin m) : Prop :=
  N.adj (x i.castSucc) (x i.succ)

/-- The step `i` of the path `x` is a **backward edge** (p. 264): `(x_i, x_{i-1})` is a directed
edge of the network, so the path traverses it against its direction. -/
def IsBackward (N : Network V) {m : ℕ} (x : Fin (m + 1) → V) (i : Fin m) : Prop :=
  N.adj (x i.succ) (x i.castSucc)

open Classical in
/-- `δ₁ = min {c(x_{i-1}, x_i) − ϕ(x_{i-1}, x_i) : (x_{i-1}, x_i) a forward edge of P}` (p. 264).
The minimum is taken in `WithTop ℝ`; it would be `⊤` only if `P` had no forward edge, which
never happens for an augmenting path (its first edge `(x₀, x₁)` is forward). -/
noncomputable def delta1 (N : Network V) (ϕ : V → V → ℝ) {m : ℕ} (x : Fin (m + 1) → V) :
    WithTop ℝ :=
  (Finset.univ.filter (fun i : Fin m => N.IsForward x i)).inf
    (fun i => ((N.cap (x i.castSucc) (x i.succ) - ϕ (x i.castSucc) (x i.succ) : ℝ) : WithTop ℝ))

open Classical in
/-- `δ₂ = min {ϕ(x_i, x_{i-1}) : (x_{i-1}, x_i) a backward edge of P}` (p. 265). The minimum is
taken in `WithTop ℝ` and equals `⊤` exactly when `P` has no backward edge. -/
noncomputable def delta2 (N : Network V) (ϕ : V → V → ℝ) {m : ℕ} (x : Fin (m + 1) → V) :
    WithTop ℝ :=
  (Finset.univ.filter (fun i : Fin m => N.IsBackward x i)).inf
    (fun i => ((ϕ (x i.succ) (x i.castSucc) : ℝ) : WithTop ℝ))

/-- The augmentation amount `δ` of the path `P` (p. 265): `δ = δ₁` when `P` has no backward
edges, and `δ = min {δ₁, δ₂}` otherwise. Both cases are `min δ₁ δ₂` in `WithTop ℝ`, because
`δ₂ = ⊤` when there is no backward edge. -/
noncomputable def delta (N : Network V) (ϕ : V → V → ℝ) {m : ℕ} (x : Fin (m + 1) → V) :
    WithTop ℝ :=
  min (N.delta1 ϕ x) (N.delta2 ϕ x)

open Classical in
/-- The function `ϕ̂` obtained from `ϕ` by changing the values along the edges of the path
`P = (x₀, …, xₘ)` by `+δ` or `−δ` (p. 265, Proposition 13.7):
1. the flow on each forward edge `(x_{i-1}, x_i)` of `P` is increased by `δ`;
2. the flow on each backward edge `(x_i, x_{i-1})` of `P` is decreased by `δ`;
all other values of `ϕ` are unchanged. -/
noncomputable def augment (N : Network V) (ϕ : V → V → ℝ) {m : ℕ} (x : Fin (m + 1) → V)
    (δ : ℝ) : V → V → ℝ :=
  fun a b =>
    if ∃ i : Fin m, N.adj a b ∧ a = x i.castSucc ∧ b = x i.succ then ϕ a b + δ
    else if ∃ i : Fin m, N.adj a b ∧ a = x i.succ ∧ b = x i.castSucc then ϕ a b - δ
    else ϕ a b

end Network

end AppliedComb.Flows


