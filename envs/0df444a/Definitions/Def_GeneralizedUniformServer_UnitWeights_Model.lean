-- Prove2me | Definitions.Def_GeneralizedUniformServer_UnitWeights_Model
-- name    : GeneralizedUniformServer_UnitWeights_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:02.625347+00:00
-- url     : https://prove2.me/theorems/e308aaaf-ff46-40b5-b02d-a1ec4caa403b
-- title:
--   Generalized k-server on unit uniform metrics: configurations, Hamming cost, service, repairs, offline solutions, OPT and lazy solutions
-- statement:
--   Fix $k\ge1$ and spaces $M_1,\dots,M_k$ of arbitrary cardinality, each carrying the uniform metric with unit distances. A **configuration** is a tuple $x\in X=M_1\times\cdots\times M_k$; its coordinate $x_i$ is the position of server $i$. Moving from $x$ to $y$ costs the Hamming distance
--   $$d(x,y)=\bigl|\{i\in[k]: x_i\ne y_i\}\bigr|\le k .$$
--   A **request** is a tuple $r\in X$, and $x$ **serves** $r$, written $x\in G(r)$, if $x_i=r_i$ for some $i$. For $i\in[k]$ the **repair** $R_i(x,r)$ moves server $i$ to $r_i$ and keeps every other coordinate.
--
--   For a finite request sequence $\rho=(r_1,\dots,r_T)$, an **offline solution** is a sequence $o_0,o_1,\dots,o_T$ of configurations with $o_t\in G(r_t)$ for $t\ge1$; its cost is $\sum_{t=1}^T d(o_{t-1},o_t)$, and
--   $$\mathrm{OPT}(\rho)=\min\Bigl\{\textstyle\sum_{t=1}^T d(o_{t-1},o_t) : o \text{ an offline solution with } o_0=a\Bigr\}.$$
--   An offline solution is **lazy** if for every $t$ it stays ($o_t=o_{t-1}$) when $o_{t-1}\in G(r_t)$ and otherwise moves to a repair $R_i(o_{t-1},r_t)$. Its **number of moves** is the number of $t\in\{1,\dots,T\}$ with $o_t\ne o_{t-1}$.
--
--   These are the objects of the unit-weight model of §2, shared by every statement of the mission.
--
--   **Formalization Note** The spaces are a family of types `M : Fin k → Type*`, and configurations are dependent functions, which keeps the spaces disjoint. No finiteness, countability or decidability is assumed. Requests are the entries of a list `ρ`, with $r_t$ the entry of 0-based index $t-1$, and an offline solution is a function `Fin (T+1) → X`. OPT is the infimum in $\mathbb N$ over all offline solutions from $a$; for $k\ge1$ the set is nonempty ($o_t=r_t$ is feasible), so the infimum is attained and is the minimum. For $k=0$ (excluded by every theorem) no solution of a nonempty sequence exists and the value is the default $0$.
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 7–8, §2 (Preliminaries; Repairs and lazy solutions)

import Mathlib

noncomputable section

namespace GeneralizedUniformServer.UnitWeights

/-- Configurations `X = M₁ × ⋯ × Mₖ` (source §2, p. 7): coordinate `i` is the position of
server `i` in its own uniform space `M i`. The coordinate types are arbitrary (finite or
infinite); using a dependent product keeps the spaces pairwise disjoint as in the source. -/
abbrev Config {k : ℕ} (M : Fin k → Type*) : Type _ := (i : Fin k) → M i

variable {k : ℕ} {M : Fin k → Type*}

/-- Unit-weight movement cost (source §2, p. 7): the Hamming distance
`d(x, y) = |{i ∈ [k] : xᵢ ≠ yᵢ}|`. -/
def dist (x y : Config M) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin k => x i ≠ y i).card

/-- A configuration `x` serves the request `r ∈ X` iff `xᵢ = rᵢ` for some `i`, i.e. `x ∈ G(r)`
(source §2, p. 7). -/
def Serves (x r : Config M) : Prop := ∃ i : Fin k, x i = r i

/-- The repair `Rᵢ(x, r)` (source §2, p. 8): move server `i` to `rᵢ`, keep the others. -/
def repair (x r : Config M) (i : Fin k) : Config M := Function.update x i (r i)

/-- An offline solution for `ρ = (r₁, …, r_T)` (source §2, p. 8): configurations
`o₀, …, o_T` (here `o : Fin (T+1) → X`, `T = ρ.length`) with `o_t ∈ G(r_t)` for `t ≥ 1`.
The request `r_t` is `ρ[t-1]` (0-based list index). -/
def IsOfflineSolution (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M) : Prop :=
  ∀ s : Fin ρ.length, Serves (o s.succ) ρ[s]

/-- The cost `∑_{t=1}^T d(o_{t-1}, o_t)` of an offline solution (source §2, p. 8). -/
def offlineCost (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M) : ℕ :=
  ∑ s : Fin ρ.length, dist (o s.castSucc) (o s.succ)

/-- `OPT(ρ)` (source §2, p. 8): the minimum cost of an offline solution with `o₀ = a`,
over all offline solutions (not only lazy ones). The minimum is taken in `ℕ`; for `k ≥ 1`
the feasible set is nonempty (e.g. `o_t = r_t`), so the infimum is attained. -/
def optCost (a : Config M) (ρ : List (Config M)) : ℕ :=
  sInf {C : ℕ | ∃ o : Fin (ρ.length + 1) → Config M,
    IsOfflineSolution ρ o ∧ o 0 = a ∧ offlineCost ρ o = C}

/-- Lazy offline solutions (source §2, p. 8): at every time `t ≥ 1` the solution stays
(`õ_t = õ_{t-1}`) when `õ_{t-1} ∈ G(r_t)`, and otherwise moves to a repair of `õ_{t-1}`
for `r_t`. -/
def IsLazy (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M) : Prop :=
  ∀ s : Fin ρ.length,
    (Serves (o s.castSucc) ρ[s] → o s.succ = o s.castSucc) ∧
    (¬ Serves (o s.castSucc) ρ[s] → ∃ i : Fin k, o s.succ = repair (o s.castSucc) ρ[s] i)

/-- The number of moves of a solution: the number of times `t ∈ {1, …, T}` with
`o_t ≠ o_{t-1}` (source §2, p. 8, the count `∑ₜ mₜ`). -/
def numMoves (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M) : ℕ := by
  classical
  exact (Finset.univ.filter fun s : Fin ρ.length => o s.succ ≠ o s.castSucc).card

end GeneralizedUniformServer.UnitWeights


