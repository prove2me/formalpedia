-- Prove2me | Definitions.Def_HartSchmeidler_FinStrat_Game
-- name    : HartSchmeidler_FinStrat_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:51:43.033947+00:00
-- url     : https://prove2.me/theorems/37768a77-99a7-4be3-8f31-ffc806ba10b4
-- title:
--   §3 — finite-strategy games, correlated equilibrium, and f-sets
-- statement:
--   Let $N$ be a nonempty set of players. Each player $i\in N$ has a nonempty finite pure-strategy set $S^i$, and a payoff $h^i:S=\prod_{j\in N}S^j\to\mathbb R$. A probability measure $p$ on the product σ-algebra $\Sigma_0$ is a **countably additive correlated equilibrium** when, for every player $i$ and recommendations $r^i,t^i\in S^i$, the payoff difference is integrable on the cylinder $\{s:s^i=r^i\}$ and
--
--   $$\int_{\{s:s^i=r^i\}}\!\bigl[h^i(s)-h^i(s^{-i},t^i)\bigr]\,dp(s)\ge0.\tag{3}$$
--
--   An **f-set** $T=\prod_i T^i$ has a nonempty finite $T^i\subseteq S^i$ for each $i$, with $T^i$ a singleton for all but finitely many players. An anchored f-set contains a fixed profile $\hat s$ in every coordinate. A finite weighted equilibrium of the restricted game $\Gamma_T$ has nonnegative weights on finitely many profiles from $T$, weights summing to one, and the finite-sum version of (3) for every $r^i,t^i\in T^i$. Pointwise inclusion orders these f-sets; the finite weights also define a sum of Dirac measures on $\Sigma_0$.
--
--   These definitions supply the equilibrium condition and the finite approximations used in Theorem 2(ii).
--
--   **Formalization Note.** The unilateral deviation $(s^{-i},t^i)$ replaces only coordinate $i$. Integrability is explicit because Lean assigns zero to a nonintegrable Bochner integral. Dirac sums remain measures on $\Sigma_0$ even if individual profile singletons are not measurable. Anchoring repairs the paper's nondirected inclusion order on all f-sets; it does not restrict the final theorem.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), pp. 20–23, §3, condition (3), proof of Theorem 2 (f-set)

import Mathlib

/-! Hart and Schmeidler (1989), §3, pp. 20–23. The player set may be uncountable. -/

namespace HartSchmeidler.FinStrat

open MeasureTheory Finset

variable {ι : Type*} {S : ι → Type*}

/-- Condition (3), p. 21, for a countably additive probability on the product σ-algebra.
The integrability clause excludes Lean's default value zero for an undefined integral. -/
def IsCorrelatedEq [DecidableEq ι] [∀ i, MeasurableSpace (S i)]
    (h : ι → (∀ i, S i) → ℝ) (μ : Measure (∀ i, S i)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (i : ι) (r t : S i),
      IntegrableOn (fun s => h i s - h i (Function.update s i t)) {s | s i = r} μ ∧
      0 ≤ ∫ s in {s | s i = r},
        (h i s - h i (Function.update s i t)) ∂μ

/-- An f-set of the proof of Theorem 2, pp. 22–23: a nonempty finite strategy set
at every coordinate, with only finitely many nonsingleton coordinates. -/
def IsFSet [∀ i, DecidableEq (S i)] (T : ∀ i, Finset (S i)) : Prop :=
  (∀ i, (T i).Nonempty) ∧ {i | ¬ ∃ a : S i, T i = {a}}.Finite

/-- Anchoring fixes the paper's nondirected index order: all f-sets contain the fixed profile. -/
def IsAnchoredFSet [∀ i, DecidableEq (S i)]
    (anchor : ∀ i, S i) (T : ∀ i, Finset (S i)) : Prop :=
  IsFSet T ∧ ∀ i, anchor i ∈ T i

/-- Pointwise inclusion of f-sets, i.e. inclusion of their products. -/
def FSetLE (T U : ∀ i, Finset (S i)) : Prop := ∀ i, T i ⊆ U i

/-- A finite weighted correlated equilibrium of the finite game Γ_T, viewed as a
finite weighted set of profiles in the unrestricted product S. -/
def IsFSetCE [DecidableEq ι] [∀ i, DecidableEq (S i)]
    (h : ι → (∀ i, S i) → ℝ) (T : ∀ i, Finset (S i))
    (F : Finset (∀ i, S i)) (w : (∀ i, S i) → ℝ) : Prop :=
  (∀ s ∈ F, ∀ i, s i ∈ T i) ∧
    (∀ s ∈ F, 0 ≤ w s) ∧
    (∑ s ∈ F, w s) = 1 ∧
    ∀ (i : ι) (r t : S i), r ∈ T i → t ∈ T i →
      0 ≤ ∑ s ∈ F.filter (fun s => s i = r),
        w s * (h i s - h i (Function.update s i t))

/-- The countably additive measure carried by a finite weighted set of profiles.
It is defined on the product σ-algebra even when the singleton of a profile is not measurable. -/
noncomputable def fsetMeasure [∀ i, MeasurableSpace (S i)]
    (F : Finset (∀ i, S i)) (w : (∀ i, S i) → ℝ) : Measure (∀ i, S i) :=
  ∑ s ∈ F, ENNReal.ofReal (w s) • Measure.dirac s

end HartSchmeidler.FinStrat


