-- Prove2me | Definitions.Def_HolonomicPositivity_Robust_Supplement_Conditions
-- name    : HolonomicPositivity_Robust_Supplement_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:53:06.55235+00:00
-- url     : https://prove2.me/theorems/63b3125b-a07a-4e41-bfb7-0b82d718429c
-- title:
--   Strict comparison, procedure coefficient condition, positivity and normalized tails
-- statement:
--   For real functions $U,V$ and an integer $v$, write
--   $$U>V+O(x^v)\quad\Longleftrightarrow\quad U\ge V\text{ eventually and }U-V\ne O(x^v).$$
--   This mirrors the strict comparison defined by the paper and fixes the reading in Theorem 3.6(2). All eventual comparisons use the real variable $x\to+\infty$.
--
--   For rational functions $P,Q$, the coefficient condition requires no poles on the natural numbers, $Q(n)\ne0$ for every natural $n$, and either (1) inequality (6) together with $P\le0<Q$, or (2) failure of (6), $P>-1/3+O(x^{-2})$, and the threshold comparison of case (II-1) or (II-2), using the actual Taylor coefficients of $P$. Inequality (6) is $P\ge-1/4-1/(16x^2)+O(x^{-3})$ in the paper's defined comparison.
--
--   Strict positivity means $f(n)>0$ for every natural $n$. For a tail starting at $N$, define
--   $$\widetilde f_{S,L}(n)=\begin{cases}f(n)\prod_{k=N}^{n-1}S(k)^{-1}&S\ne0,\\f(n)\prod_{k=N}^{n-2}L(k)^{-1}&S=0.\end{cases}$$
--   Empty products are one. Unboundedness means there is no real bound for the absolute values on $n\ge N$. Safety from $N$ requires no poles of $S,L$ there and nonzero $S(k)$ when $S\ne0$, or nonzero $L(k)$ when $S=0$.
--
--   These definitions specify the exact inputs and output guarantees of the two algorithmic results; they assert no algorithm or positivity theorem.
-- source:
--   Fugen Hagihara, Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission #328 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/328.pdf, SHA-256 b828a1da95302dcc4eef96a5cd5df68531d46030b0db425e11667ab782afead2; PDF p.2 (XX:2), Definition 1.1; pp.4-5 (XX:4-5), lines 139,153,166 and inequality (6); p.7 (XX:7), Theorem 3.6 coefficient condition; pp.9-11 (XX:9-11), lines 296-300, equation (9), lines 387-390.

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Conditions
import Definitions.Def_HolonomicPositivity_Robust_Recurrence

namespace HolonomicPositivity.Robust.Supplement

/-- Mirror of the strict comparison at line 166, used in Theorem 3.6(2), PDF p.7. -/
def GtMod (U V : ℝ → ℝ) (v : ℤ) : Prop :=
  EventuallyGE U V ∧ ¬ EqMod U V v

/-- Inequality (6) for the normalized coefficient P, PDF p.5. -/
def Ineq6 (P : RatFunc ℝ) : Prop :=
  GeMod (ev P) (fun x => -(1 / 4) - 1 / (16 * x ^ 2)) (-3)

/-- Both cases of the coefficient condition in Theorem 3.6, PDF p.7, with the global
no-pole convention (PDF p.1). In case (2), the strict comparison excludes case (II-3). -/
def CoeffCond (P Q : RatFunc ℝ) : Prop :=
  NoPolesOnNat P ∧ NoPolesOnNat Q ∧ (∀ n : ℕ, ev Q n ≠ 0) ∧
    ((Ineq6 P ∧ EventuallyGE (fun _ => 0) (ev P) ∧
        EventuallyGT (ev Q) (fun _ => 0)) ∨
     (¬ Ineq6 P ∧ GtMod (ev P) (fun _ => -(1 / 3)) (-2) ∧
       ∃ p₀ p₁ p₂ p₃ : ℝ, HasTaylorExpansion P p₀ p₁ p₂ p₃ ∧
         ((-(1 / 3) < p₀ ∧ GeMod (ev Q) (thresholdOne p₀ p₁ p₂) (-3)) ∨
          (p₀ = -(1 / 3) ∧ 0 < p₁ ∧ GeMod (ev Q) (thresholdTwo p₁) (-2)))))

/-- Strict positivity at every natural index, Definition 1.1, PDF p.2. -/
def Positive (f : ℕ → ℝ) : Prop := ∀ n, 0 < f n

/-- The normalization (9), PDF p.10. `Ico N (n-1)` stops at n-2; it is empty at n=N
and n=N+1. Values before N are irrelevant to the statements. -/
noncomputable def normalized (S L : RatFunc ℝ) (N : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if S ≠ 0 then f n * ∏ k ∈ Finset.Ico N n, (ev S k)⁻¹
  else f n * ∏ k ∈ Finset.Ico N (n - 1), (ev L k)⁻¹

/-- Unbounded absolute values on the tail beginning at N, as in Lemma 5.2. -/
def UnboundedFrom (N : ℕ) (f : ℕ → ℝ) : Prop :=
  ¬ ∃ C : ℝ, ∀ n ≥ N, |f n| ≤ C

/-- Well-defined evaluations and inverses in (8) and (9). This is a conclusion about
computed S,L,N, not an input assumption (PDF p.9 lines 296-300, p.11 lines 387-390). -/
def SafeFrom (S L : RatFunc ℝ) (N : ℕ) : Prop :=
  (∀ n ≥ N, S.denom.eval (n : ℝ) ≠ 0 ∧ L.denom.eval (n : ℝ) ≠ 0) ∧
  (S ≠ 0 → ∀ n ≥ N, ev S n ≠ 0) ∧
  (S = 0 → ∀ n ≥ N, ev L n ≠ 0)

end HolonomicPositivity.Robust.Supplement


