-- Prove2me | Definitions.Def_FirstChoiceDesign_IsRStar
-- name    : FirstChoiceDesign_IsRStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:25:22.100393+00:00
-- url     : https://prove2.me/theorems/504bd177-a048-498c-bbe6-6fdcffd0b219
-- title:
--   The column $r^*_s$ and the columns $\tilde\sigma_{s'}(r)$ of Case 1
-- statement:
--   Let $i_0,i_1$ be the pivots of $r$ at $s$, and call the class the set of students with $\rho^\varphi_{is}=\rho^\varphi_{i_0s}=\rho^\varphi_{i_1s}$. The column $r^*_s$ is the permutation of $r_s$ with
--
--   1. $r^*_{is}=r_{is}$ outside the class;
--   2. $r^*_{i_1s}=\max\{r_{is}\mid i\text{ in the class and }D_{is}(r)=1\}$;
--   3. $r^*_{i_0s}>r^*_{i_1s}$, with no class member strictly between;
--   4. $r^*_{is}>r^*_{js}$ if and only if $r_{is}>r_{js}$, for class members other than the pivots.
--
--   For $s'\ne s$, $\tilde\sigma_{s'}(r)$ is the permutation of $r_{s'}$ equal to $r_{s'}$ under MTB and, under STB, obtained by moving $i_1$ to right above $i_0$: $\tilde\sigma_{i_1s'}(r)<\tilde\sigma_{i_0s'}(r)$ with no student between, and the order of all students other than $i_1$ unchanged.
--
--   **Formalization Note** The conditions determine the columns, so `IsRStar` and `IsSigmaTilde` are predicates on a column and on a profile (whose column $s$ is ignored), and statements hold for every column satisfying them. The source's formula $\tilde\sigma_{i_1s'}(r)=\max\{r_{is'}\mid r_{is'}<r_{i_0s'}\}$ is undefined when $i_0$ has the smallest number at $s'$, and it would collide with the predecessor's number when $i_1$ starts behind $i_0$, so the text's order description is what is formalized. Mechanisms depend on a column only through the induced order. The source's case without a pivot pair, where $r^*=r$ and $\tilde\sigma=r$, needs no statement.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Case 1, p.50

import Definitions.Def_FirstChoiceDesign_First

namespace FirstChoiceDesign

/-- Membership in the priority class `ρ^φ_is = ρ^φ_{i₀ s} = ρ^φ_{i₁ s}` of the pivots, p.50. -/
def InPivotClass {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (s : Fin m) (i₀ i₁ i : Fin n) :
    Prop :=
  φ.modified X.toSetting X.ρ i s = φ.modified X.toSetting X.ρ i₀ s ∧
    φ.modified X.toSetting X.ρ i s = φ.modified X.toSetting X.ρ i₁ s

/-- `c` is the column `r*_s` of Case 1, p.50, for a pivot pair `i₀, i₁` of `r`: a permutation of `r_s`
with (1) `r*_is = r_is` outside the pivots' class; (2) `r*_{i₁ s} = max{r_is | i in the class,
D_is(r) = 1}`; (3) `r*_{i₀ s} > r*_{i₁ s}` with no class member strictly between; (4) on the class
minus the pivots, `r*_is > r*_js` iff `r_is > r_js`.

**Formalization Note** The conditions fix `c` uniquely when `i₀, i₁` lie in one class, so a
predicate plays the role of the page's definition. The page's case `i₀(r) = i₁(r) = ∅`, where
`r* = r`, needs no statement. -/
def IsRStar {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (s : Fin m) (r : Lottery n m)
    (i₀ i₁ : Fin n) (c : Fin n → ℝ) : Prop :=
  (∃ π : Equiv.Perm (Fin n), ∀ i, c i = r (π i) s) ∧
    (∀ i, ¬ InPivotClass φ X s i₀ i₁ i → c i = r i s) ∧
    IsGreatest {x | ∃ i, InPivotClass φ X s i₀ i₁ i ∧ D φ X i s r ∧ r i s = x} (c i₁) ∧
    c i₁ < c i₀ ∧
    (¬ ∃ i, InPivotClass φ X s i₀ i₁ i ∧ c i < c i₀ ∧ c i₁ < c i) ∧
    ∀ i j, InPivotClass φ X s i₀ i₁ i → InPivotClass φ X s i₀ i₁ j →
      i ≠ i₀ → i ≠ i₁ → j ≠ i₀ → j ≠ i₁ → (c j < c i ↔ r j s < r i s)

/-- `τ` agrees on every column `s' ≠ s` with `σ̃_s'(r)` of p.50, for a pivot pair `i₀, i₁` of `r`
(column `s` of `τ` is ignored). Under MTB, `σ̃_s'(r) = r_s'`. Under STB, `σ̃_s'(r)` is a permutation of
`r_s'` "obtained by moving `i₁(r)` to right above `i₀(r)`": `i₁`'s number is below `i₀`'s, no student
lies strictly between, and the order of all students other than `i₁` is unchanged.

**Formalization Note** The page's formula `σ̃_{i₁ s'}(r) = max{r_is' | r_is' < r_{i₀ s'}}` is undefined
when `i₀` has the smallest number at `s'`, and it collides with the number of `i₀`'s predecessor. So
the text's own order description is what is formalized. Mechanisms depend on a column only through
its order. -/
def IsSigmaTilde {n m : ℕ} (regime : Regime) (s : Fin m) (r : Lottery n m) (i₀ i₁ : Fin n)
    (τ : Lottery n m) : Prop :=
  ∀ s', s' ≠ s →
    match regime with
    | .MTB => ∀ i, τ i s' = r i s'
    | .STB =>
      (∃ π : Equiv.Perm (Fin n), ∀ i, τ i s' = r (π i) s') ∧
        τ i₁ s' < τ i₀ s' ∧
        (¬ ∃ i, τ i₁ s' < τ i s' ∧ τ i s' < τ i₀ s') ∧
        ∀ i j, i ≠ i₁ → j ≠ i₁ → (τ j s' < τ i s' ↔ r j s' < r i s')

end FirstChoiceDesign


