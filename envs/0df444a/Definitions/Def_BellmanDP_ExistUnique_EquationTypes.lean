-- Prove2me | Definitions.Def_BellmanDP_ExistUnique_EquationTypes
-- name    : BellmanDP_ExistUnique_EquationTypes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T15:45:26.834984+00:00
-- url     : https://prove2.me/theorems/c6797f0d-4993-4b5b-bc76-702db24363e1
-- title:
--   Equations of Type One and Type Two (Bellman, Chapter IV, §§ 3–4)
-- statement:
--   Let $D \subseteq \mathbb{R}^N$ with the Euclidean norm $\|p\| = (\sum_{i=1}^N p_i^2)^{1/2}$, let $S$ be a set of decisions, and let $g, h : D \times S \to \mathbb{R}$, $T : D \times S \to \mathbb{R}^N$.
--
--   **Type One** with constant $a$ (Chapter IV, § 3, conditions (1a)–(1e)):
--
--   1. (a) $D$ contains the null vector $\theta$, $T(p,q) \in D$ for all $p \in D$, and for every $c_1$, $g(p,q)$ is uniformly bounded over $q \in S$ and $p \in D$ with $\|p\| \le c_1$;
--   2. (b) $g(\theta, q) = 0$ for all $q \in S$;
--   3. (c) $|h(p,q)| \le 1$ for all $p \in D$, $q \in S$;
--   4. (d) $0 \le a < 1$ and $\|T(p,q)\| \le a\|p\|$ for all $q \in S$, $p \in D$;
--   5. (e) with $v(c) = \sup_{p \in D,\ \|p\| \le c}\sup_q |g(p,q)|$,
--   $$\sum_{n=0}^{\infty} v(a^n c) < \infty \qquad \text{for every } c \ge 0.$$
--
--   **Type Two** (Chapter IV, § 4, conditions (1a)–(1c)):
--
--   1. (a) for every $c_1$, $|g(p,q)|$ is uniformly bounded over $q \in S$ and $p \in D$ with $\|p\| \le c_1$;
--   2. (b) for every $c_1$ there is $a < 1$ with $|h(p,q)| \le a$ for all $q \in S$ and all $p \in D$ with $\|p\| \le c_1$;
--   3. (c) $T(p,q) \in D$ for all $p \in D$, and either $\|T(p,q)\| \le \|p\|$ for all $p \in D$, $q \in S$, or $D$ is bounded.
--
--   Type One expresses that every decision shrinks the state towards $\theta$; Type Two, that the multiplier $h$, a survival probability in applications, is uniformly below one.
--
--   **Formalization Note** The book writes only "for some $a < 1$" in (1d). The requirement $a \ge 0$ loses nothing: if (1d) holds with some $a < 0$ then $D = \{\theta\}$ and it also holds with $a = 0$. Condition (1a) is read for every radius $c_1$, as the statement of Theorem 1 ("bounded for $\|p\| \le c_1$ for any $c_1 > 0$") and condition (1e) require. $v(c)$ is a genuine supremum because of (1a) and because $\theta \in D$ and $S$ is nonempty in every theorem that uses it.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IV, § 3, conditions (1a)-(1e), p. 119; § 4, conditions (1a)-(1c), p. 121

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 3, conditions (1a)–(1e), p. 119: the equation
`f(p) = Sup_q [g(p, q) + h(p, q) f(T(p, q))]` on `D ⊆ ℝ^N` (Euclidean norm) is of **Type One**
with constant `a`. -/
structure TypeOne {N : ℕ} {S : Type*} (D : Set (EuclideanSpace ℝ (Fin N)))
    (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) (a : ℝ) : Prop where
  /-- (1a) `D` contains the null vector `θ`. -/
  zero_mem : (0 : EuclideanSpace ℝ (Fin N)) ∈ D
  /-- (1a) `T(p, q) ∈ D` for all `p ∈ D`. -/
  mapsTo : ∀ p ∈ D, ∀ q : S, T p q ∈ D
  /-- (1a) `g` is uniformly bounded for all `q ∈ S` and all `p ∈ D` with `‖p‖ ≤ c₁`. -/
  g_bdd : ∀ c₁ : ℝ, ∃ M : ℝ, ∀ p ∈ D, ‖p‖ ≤ c₁ → ∀ q : S, |g p q| ≤ M
  /-- (1b) `g(θ, q) = 0` for all `q ∈ S`. -/
  g_zero : ∀ q : S, g 0 q = 0
  /-- (1c) `|h(p, q)| ≤ 1` for all `p ∈ D`, `q ∈ S`. -/
  h_le_one : ∀ p ∈ D, ∀ q : S, |h p q| ≤ 1
  /-- (1d) `0 ≤ a` (implicit in the book: see the Formalization Note). -/
  a_nonneg : 0 ≤ a
  /-- (1d) `a < 1`. -/
  a_lt_one : a < 1
  /-- (1d) `‖T(p, q)‖ ≤ a ‖p‖` for all `q ∈ S`, `p ∈ D`. -/
  T_le : ∀ p ∈ D, ∀ q : S, ‖T p q‖ ≤ a * ‖p‖
  /-- (1e) `Σ_{n=0}^∞ v(aⁿ c) < ∞`, `v(c) = Sup_{‖p‖ ≤ c} Sup_q |g(p, q)|`, for every `c ≥ 0`. -/
  summable_v : ∀ c : ℝ, 0 ≤ c → Summable (fun n : ℕ => radialSup D g (a ^ n * c))

/-- Bellman, *Dynamic Programming*, Ch. IV, § 4, conditions (1a)–(1c), p. 121: the equation
`f(p) = Sup_q [g(p, q) + h(p, q) f(T(p, q))]` on `D ⊆ ℝ^N` is of **Type Two**. -/
structure TypeTwo {N : ℕ} {S : Type*} (D : Set (EuclideanSpace ℝ (Fin N)))
    (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) : Prop where
  /-- (1c) `T(p, q) ∈ D` for all `p ∈ D` (required under both alternatives). -/
  mapsTo : ∀ p ∈ D, ∀ q : S, T p q ∈ D
  /-- (1a) `|g(p, q)|` is uniformly bounded for all `q ∈ S` and `‖p‖ ≤ c₁`, `p ∈ D`. -/
  g_bdd : ∀ c₁ : ℝ, ∃ M : ℝ, ∀ p ∈ D, ‖p‖ ≤ c₁ → ∀ q : S, |g p q| ≤ M
  /-- (1b) `|h(p, q)| ≤ a < 1` for all `q ∈ S`, uniformly in any region `‖p‖ ≤ c₁`, `p ∈ D`. -/
  h_contract : ∀ c₁ : ℝ, ∃ a : ℝ, a < 1 ∧ ∀ p ∈ D, ‖p‖ ≤ c₁ → ∀ q : S, |h p q| ≤ a
  /-- (1c) `‖T(p, q)‖ ≤ ‖p‖` for all `p`, or alternatively `D` is a bounded region. -/
  T_cond : (∀ p ∈ D, ∀ q : S, ‖T p q‖ ≤ ‖p‖) ∨ Bornology.IsBounded D

end BellmanDP.ExistUnique


