-- Prove2me | Definitions.Def_CogCons_similarity_distance
-- name    : CogCons_similarity_distance
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T17:00:55.516856+00:00
-- url     : https://prove2.me/theorems/c950eb57-8dfe-48bb-bb19-e0942be937a5
-- title:
--   Cognitive similarity distance, cognition balls, cognitive limits
-- statement:
--   A **cognitive similarity distance** on a set $C$ is a function $\mathrm{Cog} : C \times C \to [0,1]$ together with a relation $\approx$ on $C$ ("cognitively coincide") such that for all $x, y, z \in C$:
--
--   1. $\mathrm{Cog}(x,y) = 0 \iff x \approx y$;
--   2. $\mathrm{Cog}(x,y) = \mathrm{Cog}(y,x)$;
--   3. $x \approx z$ implies $\mathrm{Cog}(x,y) = \mathrm{Cog}(z,y)$;
--   4. $\mathrm{Cog}(x,z) \le \mathrm{Cog}(x,y) + \mathrm{Cog}(y,z)$.
--
--   The **cognition ball** is $B(x,\varepsilon) = \{y \in C : \mathrm{Cog}(x,y) < \varepsilon\}$. A sequence $(x_n)_{n \ge 0}$ **converges** to $x$ (and $x$ is a **cognitive limit**) if
--   $$\forall \varepsilon \in (0,1)\ \exists m\ \forall n \ge m:\ \mathrm{Cog}(x, x_n) < \varepsilon.$$
--   A set $A \subseteq C$ is a **Gödel's incompleteness black hole** for $(x_n)$ with virtual limit $x$ if there are $\varepsilon \in (0,1)$ and $k$ with $x_n \notin B(x,\varepsilon)$ for all $n \ge k$ and $B(x,\varepsilon) \subseteq A$.
--
--   These are the objects of the paper's Sections 3.1 and 5.
--
--   **Formalization Note** Sequences are indexed from $0$ rather than $1$. The "solution space of a problem" in Definition 5.1 is not modelled.
-- source:
--   S. Acharjee and U. Gogoi, *The limit of human intelligence*, arXiv:2310.10792v2 [math.GM] (2023), https://arxiv.org/abs/2310.10792, Definitions 3.5, 3.6 (pp. 9–10), Definition 3.8 (p. 11), Definition 5.1 (p. 21)

import Mathlib

namespace CogCons

/-- Definition 3.5 (Acharjee–Gogoi): a cognitive similarity distance on a set of
thoughts `C`, together with the relation `x ≈ y` ("x and y cognitively coincide"). -/
structure CognitiveSimilarityDistance (C : Type*) where
  /-- The distance `Cog : C × C → [0, 1]`. -/
  Cog : C → C → ℝ
  /-- The relation `x ≈ y`. -/
  coincide : C → C → Prop
  /-- `Cog` takes values in `[0, 1]` (this also gives property (i), `Cog(x, y) ≥ 0`). -/
  Cog_mem_Icc : ∀ x y : C, Cog x y ∈ Set.Icc (0 : ℝ) 1
  /-- (ii) `Cog(x, y) = 0 ↔ x ≈ y`. -/
  Cog_eq_zero_iff : ∀ x y : C, Cog x y = 0 ↔ coincide x y
  /-- (iii) symmetry. -/
  Cog_symm : ∀ x y : C, Cog x y = Cog y x
  /-- (iv) if `x ≈ z` then `Cog(x, y) = Cog(z, y)`. -/
  Cog_congr : ∀ x y z : C, coincide x z → Cog x y = Cog z y
  /-- (v) triangle inequality. -/
  Cog_triangle : ∀ x y z : C, Cog x z ≤ Cog x y + Cog y z

namespace CognitiveSimilarityDistance

variable {C : Type*} (D : CognitiveSimilarityDistance C)

/-- Definition 3.6: the cognition ball `B(x, ε) = {y ∈ C : Cog(x, y) < ε}`. -/
def cognitionBall (x : C) (ε : ℝ) : Set C := {y : C | D.Cog x y < ε}

/-- Definition 3.8: a sequence of thoughts `s` converges to the thought `x` (`x` is a
cognitive limit of `s`) if for each `ε ∈ (0, 1)` there is `m` with `Cog(x, sₙ) < ε`
for all `n ≥ m`. Sequences are indexed from `0`. -/
def ConvergesTo (s : ℕ → C) (x : C) : Prop :=
  ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∃ m : ℕ, ∀ n ≥ m, D.Cog x (s n) < ε

/-- Definition 5.1: `A` is a Gödel's incompleteness black hole for the solution sequence
`s` with virtual cognitive limit `x`: for some `ε ∈ (0, 1)` there is `k` with
`sₙ ∉ B(x, ε)` for all `n ≥ k`, and `B(x, ε) ⊆ A`. -/
def IsGodelBlackHole (A : Set C) (s : ℕ → C) (x : C) : Prop :=
  ∃ ε ∈ Set.Ioo (0 : ℝ) 1, ∃ k : ℕ,
    (∀ n ≥ k, s n ∉ D.cognitionBall x ε) ∧ D.cognitionBall x ε ⊆ A

end CognitiveSimilarityDistance

end CogCons


