-- Prove2me | Definitions.Def_LocalSweepFT_IsSweepRule
-- name    : LocalSweepFT_IsSweepRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:39:45.283236+00:00
-- url     : https://prove2.me/theorems/75f72286-09f1-41e0-9571-ead2f41d52ee
-- title:
--   Sweep-rule conditions and sweep rules (local rules flipping an admissible rooted chain)
-- statement:
--   Let $\sigma$ be a $(d'-1)$-chain (a syndrome) and $v$ a vertex. A $d'$-chain $\tilde z$ satisfies the sweep-rule conditions at $v$ if
--   1. $\tilde z$ is rooted at $v$;
--   2. $\mathrm{Str}^0_+(v,\tilde z)\subseteq\mathrm{Str}^0_+(v,\sigma|_v)$;
--   3. $(\partial^-\tilde z)|_{v+}=\sigma|_{v+}$.
--
--   A **local rule** maps what a vertex sees, the coefficients of $\sigma$ on the $(d'-1)$-cells through $v$, to a pattern of flips on the $d'$-cells rooted at $v$; the same map is used at every vertex and at every time. A **sweep rule** is a local rule that, for every vertex and every syndrome, returns a chain satisfying the conditions whenever one exists ("If such an assignment exists, flip $\tilde z$") and returns $0$ otherwise. One parallel step applies the rule at every vertex: $x\mapsto x+\sum_v\varphi_v$ with $\varphi_v$ the flip at $v$ for the syndrome $\partial^-x$.
--
--   The sweep rule of Kubica and Preskill is the decoder of the mission: the threshold theorem holds for every sweep rule in each sector.
--
--   **Formalization Note** Def. 4.6 does not say which admissible chain is flipped; every choice is allowed. Condition 2 uses $\sigma|_v$, as printed in the formula. The recursive algorithm after Claim 4.7 (p.20) is one sweep rule.
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Definition 4.6, p.18; algorithm after Claim 4.7, p.20

import Mathlib
import Definitions.Def_LocalSweepFT_Chain

namespace LocalSweepFT

/-! Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…), Definition 4.6 (Sweep Rule), p.18. -/

variable {R : Type} [CommRing R] [DecidableEq R] {d d' : ℕ}

/-- The sweep-rule conditions of Def 4.6 (p.18) for a rooted chain `z̃` at the vertex `v`, given
the `(d′−1)`-chain `σ` (the syndrome):
1. `z̃` is rooted at `v`;
2. `Str⁰₊(v, z̃) ⊆ Str⁰₊(v, σ|_v)` (condition 1, with `σ|_v` as printed in the formula);
3. `(∂⁻z̃)|_{v+} = σ|_{v+}` (condition 2). -/
def IsAdmissible (v : Vtx R d) (σ : Chain R d (d' - 1)) (zt : Chain R d d') : Prop :=
  IsRootedAt v zt ∧ str0 v zt ⊆ str0 v (restrictAt v σ) ∧
    restrictPos v (bdry zt) = restrictPos v σ

/-- What a vertex sees: the coefficients of the `(d′−1)`-cells through it. The entry at `(a, T)`
is the coefficient of `θ_{v − Σ_{a_j = 1} 1_j, T}` when `{j : a_j = 1} ⊆ T` (these are exactly the
`(d′−1)`-cells containing `v`) and `0` otherwise. -/
abbrev StarView (d d' : ℕ) := (Fin d → Fin 2) × DirSet d (d' - 1) → ZMod 2

/-- A local rule: a fixed map from what a vertex sees to a pattern of flips on the `d′`-cells
rooted at it. The same map is used at every vertex and at every time (translation invariance and
time independence, p.5, p.18). -/
abbrev LocalRule (d d' : ℕ) := StarView d d' → (DirSet d d' → ZMod 2)

/-- The `0/1` offset vector of a pattern `a : Fin d → Fin 2`. -/
def offset (a : Fin d → Fin 2) : Vtx R d := fun j => ((a j : ℕ) : R)

/-- The star view of `σ` at `v`: `σ|_v`, read off at the cells through `v`. -/
def view (v : Vtx R d) (σ : Chain R d (d' - 1)) : StarView d d' :=
  fun p => if ∀ j, p.1 j = 1 → j ∈ p.2.1 then σ (v - offset p.1, p.2) else 0

/-- The rooted chain at `v` with coefficient `out S′` on `θ_{v,S′}`. -/
noncomputable def place (v : Vtx R d) (out : DirSet d d' → ZMod 2) : Chain R d d' :=
  ∑ S : DirSet d d', Finsupp.single (v, S) (out S)

/-- A sweep rule (Def 4.6, p.18): a local rule that, at every vertex `v` and for every syndrome `σ`,
flips a rooted chain satisfying the sweep-rule conditions whenever one exists ("If such an
assignment exists, flip z̃"), and flips nothing otherwise.

**Formalization Note.** Def 4.6 does not say which admissible `z̃` is flipped when there are
several; every rule that always picks an admissible one is a sweep rule. The explicit recursive
algorithm after Claim 4.7 (p.20) is one of them. The rule depends on `σ` only through the star view,
which determines both conditions. -/
def IsSweepRule (R : Type) [CommRing R] [DecidableEq R] (rule : LocalRule d d') : Prop :=
  ∀ (v : Vtx R d) (σ : Chain R d (d' - 1)),
    ((∃ zt : Chain R d d', IsAdmissible v σ zt) → IsAdmissible v σ (place v (rule (view v σ)))) ∧
    ((¬ ∃ zt : Chain R d d', IsAdmissible v σ zt) → rule (view v σ) = 0)

/-- One parallel application of the sweep rule at every vertex to the syndrome `σ`: the sum of the
rooted flips `φ_v` over the vertices `v` of `σ`. Vertices outside `V(σ)` see nothing and flip
nothing (the only admissible chain is then `0`). The chain after one step from `x` is
`x + sweepStep rule (∂⁻x)`. -/
noncomputable def sweepStep (rule : LocalRule d d') (σ : Chain R d (d' - 1)) : Chain R d d' :=
  ∑ v ∈ chainVerts σ, place v (rule (view v σ))

end LocalSweepFT


