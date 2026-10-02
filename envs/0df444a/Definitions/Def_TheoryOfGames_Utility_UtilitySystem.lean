-- Prove2me | Definitions.Def_TheoryOfGames_Utility_UtilitySystem
-- name    : TheoryOfGames_Utility_UtilitySystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T00:45:03.188339+00:00
-- url     : https://prove2.me/theorems/c43e4f72-5ca4-413e-ac4d-f87ccf61f43f
-- title:
--   System of utilities: the axioms (3:A)–(3:C) of preference and mixture (3.6.1)
-- statement:
--   A **system of utilities** in the sense of von Neumann and Morgenstern consists of an abstract set $U$ of entities $u, v, w, \dots$, a relation $u > v$ on $U$ (read: $u$ is preferable to $v$), and, for every number $\alpha$ with $0 < \alpha < 1$, an operation assigning to $u, v \in U$ an element written
--   $$\alpha u + (1-\alpha) v \in U .$$
--   Write $u < v$ for $v > u$. The following axioms are required.
--
--   1. **(3:A) Complete ordering.** (3:A:a) For any two $u, v$ exactly one of $u = v$, $u > v$, $u < v$ holds. (3:A:b) $u > v$ and $v > w$ imply $u > w$.
--   2. **(3:B) Ordering and combining.** (3:B:a) $u < v$ implies $u < \alpha u + (1-\alpha)v$. (3:B:b) $u > v$ implies $u > \alpha u + (1-\alpha) v$. (3:B:c) $u < w < v$ implies that $\alpha u + (1-\alpha) v < w$ for some $\alpha$. (3:B:d) $u > w > v$ implies that $\alpha u + (1-\alpha) v > w$ for some $\alpha$.
--   3. **(3:C) Algebra of combining.** (3:C:a) $\alpha u + (1-\alpha)v = (1-\alpha)v + \alpha u$. (3:C:b) $\alpha(\beta u + (1-\beta)v) + (1-\alpha)v = \gamma u + (1-\gamma)v$ where $\gamma = \alpha\beta$.
--
--   All weights $\alpha, \beta, \gamma$ lie strictly between $0$ and $1$ (footnote 4 of 3.6.1), and "$=$" is true identity (A.1.2), so the order is a strict total order on $U$. The expression $\alpha u + (1-\alpha)v$ is formal notation: $U$ carries no linear structure, and the operation satisfies nothing beyond the axioms. The file also fixes the appendix's notations: $u \leqq v$ means $u = v$ or $u < v$, and $(1-\gamma)u + \gamma v$ denotes the operation with weight $1-\gamma$ on $u$.
--
--   These axioms are the entire hypothesis of the Appendix's theorems (A:A)–(A:W), which derive from them a numerical utility unique up to a positive linear transformation.
--
--   **Formalization Note** The set of weights is the subtype `OpenUnit` of $\mathbb R$ given by the open interval $(0,1)$, with `OpenUnit.oneSub` ($\alpha \mapsto 1-\alpha$) and `OpenUnit.mul` ($\alpha\beta$). The structure field `gt u v` is $u > v$ and `mix α u v` is $\alpha u + (1-\alpha)v$; `S.lt u v` is $u < v$, `S.le u v` is $u \leqq v$, and `S.cmb γ u v` is the appendix's $(1-\gamma)u + \gamma v$, i.e. `mix (1 − γ) u v`. Axiom (3:A:a) is stated literally as "exactly one of the three relations holds".
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 26, 3.6.1, axioms (3:A)–(3:C) and footnote 4; p. 617, A.1.2

import Mathlib

namespace TheoryOfGames.Utility

/-- The open unit interval `0 < α < 1`, the only range of the book's mixing weights
(3.6.1, footnote 4: "the α, β, γ occurring here are always > 0, < 1"). -/
abbrev OpenUnit : Type := Set.Ioo (0 : ℝ) 1

/-- `α ↦ 1 − α` on the open unit interval. -/
def OpenUnit.oneSub (α : OpenUnit) : OpenUnit :=
  ⟨1 - (α : ℝ), by
    obtain ⟨h0, h1⟩ := α.2
    exact ⟨by linarith, by linarith⟩⟩

/-- The product `αβ` of two weights in the open unit interval. -/
def OpenUnit.mul (α β : OpenUnit) : OpenUnit :=
  ⟨(α : ℝ) * (β : ℝ), by
    obtain ⟨ha0, ha1⟩ := α.2
    obtain ⟨hb0, hb1⟩ := β.2
    exact ⟨mul_pos ha0 hb0, by nlinarith⟩⟩

/-- A system `U` of (abstract) utilities in the sense of von Neumann–Morgenstern, 3.6.1:
a relation `gt u v` ("u > v", u is preferable to v) and, for every number `0 < α < 1`, an
operation `mix α u v`, written `αu + (1 − α)v` in the book, subject to the axioms
(3:A)–(3:C). Equality is true identity (A.1.2). No linear structure is assumed: `mix` is a
formal operation satisfying only the axioms below, and it is not defined for `α = 0, 1`. -/
structure UtilitySystem (U : Type*) where
  /-- The relation `u > v`. -/
  gt : U → U → Prop
  /-- The operation `αu + (1 − α)v`, for `0 < α < 1`. -/
  mix : OpenUnit → U → U → U
  /-- (3:A:a) For any two `u, v` one and only one of `u = v`, `u > v`, `u < v` holds. -/
  complete : ∀ u v : U,
    (u = v ∧ ¬ gt u v ∧ ¬ gt v u) ∨ (gt u v ∧ u ≠ v ∧ ¬ gt v u) ∨
      (gt v u ∧ u ≠ v ∧ ¬ gt u v)
  /-- (3:A:b) `u > v`, `v > w` imply `u > w`. -/
  trans : ∀ u v w : U, gt u v → gt v w → gt u w
  /-- (3:B:a) `u < v` implies `u < αu + (1 − α)v`. -/
  lt_mix_of_lt : ∀ (α : OpenUnit) (u v : U), gt v u → gt (mix α u v) u
  /-- (3:B:b) `u > v` implies `u > αu + (1 − α)v`. -/
  mix_lt_of_gt : ∀ (α : OpenUnit) (u v : U), gt u v → gt u (mix α u v)
  /-- (3:B:c) `u < w < v` implies the existence of an `α` with `αu + (1 − α)v < w`. -/
  exists_mix_lt : ∀ u v w : U, gt w u → gt v w → ∃ α : OpenUnit, gt w (mix α u v)
  /-- (3:B:d) `u > w > v` implies the existence of an `α` with `αu + (1 − α)v > w`. -/
  exists_mix_gt : ∀ u v w : U, gt u w → gt w v → ∃ α : OpenUnit, gt (mix α u v) w
  /-- (3:C:a) `αu + (1 − α)v = (1 − α)v + αu`. -/
  mix_comm : ∀ (α : OpenUnit) (u v : U), mix α u v = mix (OpenUnit.oneSub α) v u
  /-- (3:C:b) `α(βu + (1 − β)v) + (1 − α)v = γu + (1 − γ)v` where `γ = αβ`. -/
  mix_mix : ∀ (α β : OpenUnit) (u v : U), mix α (mix β u v) v = mix (OpenUnit.mul α β) u v

namespace UtilitySystem

variable {U : Type*} (S : UtilitySystem U)

/-- `u < v`, i.e. `v > u`. -/
def lt (u v : U) : Prop := S.gt v u

/-- `u ≦ v`, i.e. `u = v` or `u < v`. -/
def le (u v : U) : Prop := u = v ∨ S.gt v u

/-- The appendix's notation `(1 − γ)u + γv`, i.e. the book's operation `αu + (1 − α)v`
with `α = 1 − γ`. -/
def cmb (γ : OpenUnit) (u v : U) : U := S.mix (OpenUnit.oneSub γ) u v

end UtilitySystem

end TheoryOfGames.Utility


