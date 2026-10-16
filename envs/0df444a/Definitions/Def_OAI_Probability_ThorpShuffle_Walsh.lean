-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
-- name    : OAI_Probability_ThorpShuffle_Walsh
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:21:06.169839+00:00
-- url     : https://prove2.me/theorems/9bc911e0-a6a2-40a3-a472-7bdd7e4666e1
-- title:
--   Walsh characters on the Boolean cube, orthogonality and Parseval's identity
-- statement:
--   Let $I$ be a finite index set and consider the Boolean cube $\{0,1\}^I$, with Booleans identified with bits. For a statement $P$ write $[P]$ for $1$ if $P$ holds and $0$ otherwise.
--
--   1. *Walsh characters.* For $a,x\in\{0,1\}^I$,
--   $$
--   \chi_a(x)=\prod_{i\in I:\ a_i=1}(-1)^{x_i}=(-1)^{\sum_{i\in I}a_ix_i}.
--   $$
--   The character is symmetric, $\chi_a(x)=\chi_x(a)$, the zero frequency gives $\chi_0\equiv1$, and $\chi_a(x)^2=1$.
--   2. *Orthogonality.* For all $a,b\in\{0,1\}^I$ and, dually, for all $x,y\in\{0,1\}^I$,
--   $$
--   \sum_{x\in\{0,1\}^I}\chi_a(x)\,\chi_b(x)=2^{|I|}\,[a=b],\qquad\sum_{a\in\{0,1\}^I}\chi_a(x)\,\chi_a(y)=2^{|I|}\,[x=y].
--   $$
--   3. *Walsh coefficients.* For $w:\{0,1\}^I\to\mathbb{R}$, the (unnormalized) coefficient at frequency $a$ is $\hat w(a)=\sum_{x}w(x)\,\chi_a(x)$. In particular $\hat w(0)=\sum_xw(x)$ is the total mass.
--   4. *Parseval's identity.* For every $w:\{0,1\}^I\to\mathbb{R}$,
--   $$
--   \frac{1}{2^{|I|}}\sum_{a\in\{0,1\}^I}\hat w(a)^2=\sum_{x\in\{0,1\}^I}w(x)^2 .
--   $$
--
--   The characters $\chi_a$ form an orthogonal basis of real functions on the cube. In the Thorp shuffle analysis, weights on the positions $\{0,1\}^d$ are expanded in this basis. Parseval's identity converts sums of squared coefficients back into the $\ell^2$ energy of the weight, and the zero coefficient records its total mass.
--
--   **Formalization Note** `character a x` is the product over $I$ of `sign (x i)` (when `a i` holds) or `1`, and `coefficient w a` is $\hat w(a)$. The factor $2^{|I|}$ appears as `Fintype.card (ι → Bool)`, and the left side of Parseval's identity (`parseval`) is the uniform `mean` over frequencies. The file also contains a private copy of the lemma `ite_eq_right`, kept for compatibility.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/Walsh.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/Walsh.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uι uκ

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def character {ι : Type uι} [Fintype ι] (a x : ι → Bool) : ℝ :=
  ∏ i, if a i then sign (x i) else 1

theorem character_symm {ι : Type uι} [Fintype ι] (a x : ι → Bool) :
    character a x = character x a := by
  apply Finset.prod_congr rfl
  intro i _
  cases a i <;> cases x i <;> rfl

@[simp] theorem character_false {ι : Type uι} [Fintype ι] (x : ι → Bool) :
    character (fun _ => false) x = 1 := by
  simp [character]

@[simp] theorem character_sq {ι : Type uι} [Fintype ι] (a x : ι → Bool) :
    character a x ^ 2 = 1 := by
  unfold character
  rw [← Finset.prod_pow]
  have h (i : ι) : (if a i then sign (x i) else (1 : ℝ)) ^ 2 = 1 := by
    cases a i <;> simp
  simp only [h, Finset.prod_const_one]

theorem sum_character_pair {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (a b : ι → Bool) :
    (∑ x : ι → Bool, character a x * character b x) =
      if a = b then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  have hlocal (u v : Bool) :
      (∑ x : Bool, (if u then sign x else (1 : ℝ)) * (if v then sign x else 1)) =
        if u = v then 2 else 0 := by
    cases u <;> cases v <;> norm_num [sign]
  have hf : (∑ x : ι → Bool, character a x * character b x) =
      ∏ i, (if a i = b i then (2 : ℝ) else 0) := by
    calc
      _ = ∑ x : ι → Bool, ∏ i,
          (if a i then sign (x i) else (1 : ℝ)) * (if b i then sign (x i) else 1) := by
        apply Finset.sum_congr rfl
        intro x _
        exact (Finset.prod_mul_distrib).symm
      _ = ∏ i, ∑ x : Bool,
          (if a i then sign x else (1 : ℝ)) * (if b i then sign x else 1) :=
        (Fintype.prod_sum (fun (i : ι) (x : Bool) =>
          (if a i then sign x else (1 : ℝ)) * (if b i then sign x else 1))).symm
      _ = _ := by simp only [hlocal]
  rw [hf]
  by_cases h : a = b
  · subst b
    simp
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, a i = b i := fun he => h (funext he)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem sum_character_pair_dual {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (x y : ι → Bool) :
    (∑ a : ι → Bool, character a x * character a y) =
      if x = y then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  calc
    _ = ∑ a : ι → Bool, character x a * character y a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [character_symm a x, character_symm a y]
    _ = _ := sum_character_pair x y

def coefficient {ι : Type uι} [Fintype ι] [DecidableEq ι] (w : (ι → Bool) → ℝ) (a : ι → Bool) : ℝ :=
  ∑ x, w x * character a x

theorem parseval {ι : Type uι} [Fintype ι] [DecidableEq ι] (w : (ι → Bool) → ℝ) :
    mean (fun a : ι → Bool => coefficient w a ^ 2) = ∑ x, w x ^ 2 := by
  have hs :
      (∑ a : ι → Bool, coefficient w a ^ 2) =
        (Fintype.card (ι → Bool) : ℝ) * ∑ x, w x ^ 2 := by
    calc
      _ = ∑ a : ι → Bool, ∑ x, ∑ y,
          (character a x * character a y) * (w x * w y) := by
        apply Finset.sum_congr rfl
        intro a _
        simp only [coefficient, pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = ∑ x, ∑ y, (∑ a : ι → Bool, character a x * character a y) * (w x * w y) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = _ := by
        simp only [sum_character_pair_dual, ite_mul, zero_mul]
        simp [Finset.mul_sum, pow_two]
  unfold mean
  rw [hs]
  have hcard : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ _ hcard

@[simp] theorem coefficient_false {ι : Type uι} [Fintype ι] [DecidableEq ι] (w : (ι → Bool) → ℝ) :
    coefficient w (fun _ => false) = ∑ x, w x := by
  simp [coefficient]

end Conditional

end Thorp

end

end OAI


