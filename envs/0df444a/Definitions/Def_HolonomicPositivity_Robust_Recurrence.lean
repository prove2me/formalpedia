-- Prove2me | Definitions.Def_HolonomicPositivity_Robust_Recurrence
-- name    : HolonomicPositivity_Robust_Recurrence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:47.5219+00:00
-- url     : https://prove2.me/theorems/66b3756c-a220-44af-93cc-cdc6540be389
-- title:
--   The normalized third-order recurrence, robust ultimate positivity, and the certificate (8)
-- statement:
--   For $P,Q\in\mathbb R(x)$, a real sequence $f$ solves the normalized third-order recurrence when
--
--   $$f(n+3)=f(n+2)+P(n)f(n+1)+Q(n)f(n)\qquad\text{for all }n\in\mathbb N.\tag{4}$$
--
--   A sequence is ultimately positive when $f(n)>0$ for all sufficiently large $n$. The recurrence admits a robustly ultimately positive solution when there are a solution $f$ and $\varepsilon>0$ such that every solution $g$ with
--
--   $$|g(0)-f(0)|<\varepsilon,\quad|g(1)-f(1)|<\varepsilon,\quad|g(2)-f(2)|<\varepsilon$$
--
--   is ultimately positive. The coefficients stay fixed under the perturbation, and $f$ itself is covered by taking $g=f$. Each initial triple determines exactly one solution, and this file proves that fact, so the set of initial triples yielding an ultimately positive solution must have nonempty interior.
--
--   For $L\in\mathbb R(x)$ and a real sequence $F$, the $L$-scaled difference is $\Delta_LF(n)=F(n+1)-L(n)F(n)$. For $S,L\in\mathbb R(x)$ the certificate at $n$ is
--
--   $$\operatorname{Certificate}(n)\ :=\ f(n)>0\ \wedge\ \Delta_Sf(n)>0\ \wedge\ \Delta_L\Delta_Sf(n)>0.\tag{8}$$
--
--   These objects state the mission's goal and its invariance lemma.
--
--   **Formalization Note** Solutions are characterized by a predicate, not by assumption: the file constructs the solution from any initial triple. Closeness is measured in the maximum norm on $\mathbb R^3$, which gives the same notion of small perturbation as any other norm.
-- source:
--   Fugen Hagihara, Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission #328 (October 2026), SHA-256 b828a1da95302dcc4eef96a5cd5df68531d46030b0db425e11667ab782afead2: Definition 1.1 and robustness (Theorem 1.2, lines 70-72) PDF p.2; recurrence (4) PDF p.4; Definition 4.1 PDF p.8; certificate (8) PDF p.9.

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Comparison

namespace HolonomicPositivity.Robust

/-- `f` is a solution of the normalized third-order recurrence (4), PDF p.4:
`f(n+3) = f(n+2) + P(n) f(n+1) + Q(n) f(n)` for all natural `n`. -/
def IsSolution (P Q : RatFunc ℝ) (f : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, f (n + 3) = f (n + 2) + ev P n * f (n + 1) + ev Q n * f n

/-- Ultimate positivity (Definition 1.1, PDF p.2): `f(n) > 0` for all sufficiently large `n`. -/
def UltimatelyPositive (f : ℕ → ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, 0 < f n

/-- The recurrence (4) admits a robustly ultimately positive solution (PDF p.2, lines 70–72):
a solution `f` such that every solution `g` whose three initial values are close to those of `f`
is ultimately positive. Taking `g = f` shows `f` itself is ultimately positive. -/
def AdmitsRobustlyUltimatelyPositiveSolution (P Q : RatFunc ℝ) : Prop :=
  ∃ f : ℕ → ℝ, IsSolution P Q f ∧ ∃ ε : ℝ, 0 < ε ∧
    ∀ g : ℕ → ℝ, IsSolution P Q g →
      |g 0 - f 0| < ε → |g 1 - f 1| < ε → |g 2 - f 2| < ε →
      UltimatelyPositive g

/-- The solution of (4) with initial values `a, b, c`. -/
noncomputable def solutionFrom (P Q : RatFunc ℝ) (a b c : ℝ) : ℕ → ℝ
  | 0 => a
  | 1 => b
  | 2 => c
  | n + 3 =>
    solutionFrom P Q a b c (n + 2) + ev P n * solutionFrom P Q a b c (n + 1) +
      ev Q n * solutionFrom P Q a b c n

/-- Every initial triple has exactly one solution of (4), so the quantifier over solutions in
`AdmitsRobustlyUltimatelyPositiveSolution` ranges over the whole neighbourhood of initial triples. -/
theorem existsUnique_isSolution (P Q : RatFunc ℝ) (a b c : ℝ) :
    ∃! f : ℕ → ℝ, IsSolution P Q f ∧ f 0 = a ∧ f 1 = b ∧ f 2 = c := by
  refine ⟨solutionFrom P Q a b c, ⟨fun n => ?_, rfl, rfl, rfl⟩, ?_⟩
  · rw [solutionFrom]
  · rintro g ⟨hg, h0, h1, h2⟩
    have key : ∀ n, g n = solutionFrom P Q a b c n ∧ g (n + 1) = solutionFrom P Q a b c (n + 1) ∧
        g (n + 2) = solutionFrom P Q a b c (n + 2) := by
      intro n
      induction n with
      | zero => exact ⟨h0, h1, h2⟩
      | succ n ih =>
        obtain ⟨i0, i1, i2⟩ := ih
        refine ⟨i1, i2, ?_⟩
        show g (n + 3) = solutionFrom P Q a b c (n + 3)
        rw [hg n, solutionFrom, i0, i1, i2]
    funext n
    exact (key n).1

/-- The `L`-scaled difference (Definition 4.1, PDF p.8):
`Δ_L F (n) = F(n+1) - L(n) F(n)`. -/
noncomputable def scaledDiff (L : RatFunc ℝ) (F : ℕ → ℝ) : ℕ → ℝ :=
  fun n => F (n + 1) - ev L n * F n

/-- The certificate (8), PDF p.9:
`f(n) > 0 ∧ Δ_S f(n) > 0 ∧ Δ_L Δ_S f(n) > 0`. -/
def Certificate (S L : RatFunc ℝ) (f : ℕ → ℝ) (n : ℕ) : Prop :=
  0 < f n ∧ 0 < scaledDiff S f n ∧ 0 < scaledDiff L (scaledDiff S f) n

end HolonomicPositivity.Robust


