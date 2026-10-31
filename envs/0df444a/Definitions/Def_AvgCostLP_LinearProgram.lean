-- Prove2me | Definitions.Def_AvgCostLP_LinearProgram
-- name    : AvgCostLP_LinearProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:42.372091+00:00
-- url     : https://prove2.me/theorems/f01bd486-fc9c-4227-a4a2-543b57db0a96
-- title:
--   §2.2 — linear programs (P), (P*) in dual pairs, the set $H$ and the subvalue
-- statement:
--   Let $(X,Y)$ and $(Z,W)$ be **dual pairs** of real vector spaces: bilinear forms $\langle\cdot,\cdot\rangle$ such that every nonzero vector of either space pairs nonzero with some vector of the other. Let $L:X\to Z$ be linear with adjoint $L^*:W\to Y$, $\langle x,L^*w\rangle=\langle Lx,w\rangle$; let $\Lambda\subset X$ be a nonempty convex cone with dual cone $\Lambda^*=\{y\mid\langle x,y\rangle\ge0\ \forall x\in\Lambda\}$; and let $c\in Y$, $b\in Z$. The programs are
--   $$(\mathrm P)\ \ \min\ \langle x,c\rangle\ \text{ s.t. }Lx=b,\ x\in\Lambda; \qquad (\mathrm P^*)\ \ \max\ \langle b,w\rangle\ \text{ s.t. }-L^*w+c\in\Lambda^*.$$
--   With $H:=\{(Lx,\langle x,c\rangle+r)\mid x\in\Lambda,\ r\ge0\}$ (2.4) and $\overline H$ its closure in the weak topology $\sigma(Z\times\mathbb R,W\times\mathbb R)$, (P) is **subconsistent** when $(b,r)\in\overline H$ for some $r$, and the **subvalue** of (P) is $\inf\{r\mid(b,r)\in\overline H\}$.
--
--   **Formalization Note** The weak topology is the coarsest one making every $(z,r)\mapsto\langle z,w\rangle+rr'$ continuous (p.7 writes $|\langle\cdot,y\rangle|$, but the net characterization on the same page fixes the usual weak topology). The paper asks $L$ to be weakly continuous; here the adjoint with the identity above is part of the data, which by Prop. 2.1 is equivalent. The cone is required to be nonempty.
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §2.2, pp.7-8, (2.2)-(2.4)

import Mathlib

open Topology

namespace AvgCostLP

/-- Yu, arXiv:1905.12095v3, §2.2, p.7: a *dual pair* `(E, F)` of real vector spaces, given by a
bilinear form `⟨·, ·⟩ : E × F → ℝ` such that for each `x ≠ 0` in `E` there is `y ∈ F` with
`⟨x, y⟩ ≠ 0`, and for each `y ≠ 0` in `F` there is `x ∈ E` with `⟨x, y⟩ ≠ 0`. -/
structure DualPair (E F : Type*) [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] where
  /-- the bilinear form `⟨·, ·⟩` -/
  pair : E →ₗ[ℝ] F →ₗ[ℝ] ℝ
  sep_left : ∀ x : E, x ≠ 0 → ∃ y : F, pair x y ≠ 0
  sep_right : ∀ y : F, y ≠ 0 → ∃ x : E, pair x y ≠ 0

/-- Yu, arXiv:1905.12095v3, §2.2, pp.7–8: an equality-constrained linear program (P) and its
dual (P*) in topological vector spaces:

* two dual pairs `(X, Y)` and `(Z, W)`;
* a linear map `L : X → Z` and its adjoint `L* : W → Y`, `⟨x, L*w⟩ = ⟨Lx, w⟩`;
* a nonempty convex cone `Λ ⊂ X` (its dual cone is `Λ* = {y | ⟨x, y⟩ ≥ 0 ∀ x ∈ Λ}`);
* `c ∈ Y` and `b ∈ Z`.

(P) minimizes `⟨x, c⟩` subject to `Lx = b`, `x ∈ Λ` (2.2); (P*) maximizes `⟨b, w⟩` subject to
`−L*w + c ∈ Λ*`, `w ∈ W` (2.3).

**Formalization Note** The paper requires `L` to be weakly continuous and then takes the weakly
continuous adjoint `L*` (Prop. 2.1). Here a linear `L*` with the adjoint identity is part of the
data; by Prop. 2.1 its existence is equivalent to weak continuity of `L`. A convex cone is
required to be nonempty (with `Λ = ∅` the subvalue/value correspondence fails). -/
structure LinearProgram (X Y Z W : Type*) [AddCommGroup X] [Module ℝ X] [AddCommGroup Y]
    [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z] [AddCommGroup W] [Module ℝ W] where
  pXY : DualPair X Y
  pZW : DualPair Z W
  L : X →ₗ[ℝ] Z
  Lstar : W →ₗ[ℝ] Y
  adjoint : ∀ (x : X) (w : W), pXY.pair x (Lstar w) = pZW.pair (L x) w
  Λ : ConvexCone ℝ X
  Λ_nonempty : (Λ : Set X).Nonempty
  c : Y
  b : Z

namespace LinearProgram

variable {X Y Z W : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [AddCommGroup Z] [Module ℝ Z] [AddCommGroup W] [Module ℝ W]

/-- The dual cone `Λ* := {y ∈ Y | ⟨x, y⟩ ≥ 0 ∀ x ∈ Λ}` (p.8). -/
def dualCone (P : LinearProgram X Y Z W) : Set Y :=
  {y | ∀ x ∈ P.Λ, 0 ≤ P.pXY.pair x y}

/-- The set `H := {(Lx, ⟨x, c⟩ + r) | x ∈ Λ, r ≥ 0} ⊂ Z × ℝ` of (2.4), p.8. -/
def setH (P : LinearProgram X Y Z W) : Set (Z × ℝ) :=
  {zr | ∃ x ∈ P.Λ, ∃ r : ℝ, 0 ≤ r ∧ zr = (P.L x, P.pXY.pair x P.c + r)}

/-- The weak topology `σ(Z × ℝ, W × ℝ)` (p.8) of the dual pair `(Z × ℝ, W × ℝ)` with the bilinear
form `⟨(z, r), (w, r')⟩ = ⟨z, w⟩ + r r'`: the coarsest topology on `Z × ℝ` making every map
`(z, r) ↦ ⟨z, w⟩ + r r'` continuous.

**Formalization Note** p.7 says "the coarsest topology under which `|⟨·, y⟩|` is continuous"; the
net characterization on the same page (`⟨x_i, y⟩ → ⟨x̄, y⟩` for all `y`) fixes the intended,
usual weak topology, which is the one used here. -/
@[reducible] def weakTopZR (P : LinearProgram X Y Z W) : TopologicalSpace (Z × ℝ) :=
  TopologicalSpace.induced (fun zr : Z × ℝ => fun wr : W × ℝ => P.pZW.pair zr.1 wr.1 + zr.2 * wr.2)
    Pi.topologicalSpace

/-- `{r ∈ ℝ | (b, r) ∈ H̄}` (p.8), where `H̄` is the closure of `H` in `σ(Z × ℝ, W × ℝ)`. (P) is
*subconsistent* when this set is nonempty, and its infimum is the *subvalue* of (P). -/
def subvalueSet (P : LinearProgram X Y Z W) : Set ℝ :=
  {r | (P.b, r) ∈ @closure (Z × ℝ) P.weakTopZR P.setH}

/-- The set of objective values `⟨b, w⟩` of the feasible solutions `w ∈ W` of (P*), i.e. those
with `−L*w + c ∈ Λ*` (2.3), p.8. Its supremum is `sup(P*)`. -/
def dualValueSet (P : LinearProgram X Y Z W) : Set ℝ :=
  {v | ∃ w : W, -P.Lstar w + P.c ∈ P.dualCone ∧ v = P.pZW.pair P.b w}

end LinearProgram

end AvgCostLP


