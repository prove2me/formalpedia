-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
-- name    : OAI_Combinatorics_BooleanFunctions_Walsh
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:19:32.910807+00:00
-- url     : https://prove2.me/theorems/c7492035-8619-44cc-bc57-dae934c20040
-- title:
--   Walsh calculus on the Boolean cube: coordinate reflections, the sign mask, and juntas
-- statement:
--   Throughout, $I$ is a finite index set and $\mathbb{B}=\{\mathrm{false},\mathrm{true}\}$. A point $x$ of the Boolean cube $\mathbb{B}^I$ is read as a sign vector through $\operatorname{sgn}(\mathrm{false})=1$, $\operatorname{sgn}(\mathrm{true})=-1$. Averages are uniform, $\mathbb{E}_{x\in A}\,g(x)=|A|^{-1}\sum_{x\in A}g(x)$ for a finite set $A$. For $s\subseteq I$ the Walsh character is $\chi_s(x)=\prod_{i\in s}\operatorname{sgn}(x_i)$, the Fourier coefficient of $f:\mathbb{B}^I\to\mathbb{R}$ is $\hat f(s)=\mathbb{E}_x[f(x)\chi_s(x)]$, and $\deg f$ is the largest $|s|$ with $\hat f(s)\neq0$ (and $0$ if all coefficients vanish). On top of this setting the file defines:
--
--   1. **Coordinate reflection.** For $a\in\mathbb{B}^I$, the map $R_a:\mathbb{B}^I\to\mathbb{B}^I$ given by $(R_ax)_i=a_i\oplus x_i$ (exclusive or). It is an involutive bijection of the cube; in sign language it multiplies the $i$-th sign by $\operatorname{sgn}(a_i)$.
--   2. **Positive mask.** For $f:\mathbb{B}^I\to\mathbb{R}$, the point $a^f\in\mathbb{B}^I$ with $a^f_i=\mathrm{true}$ if and only if $\hat f(\{i\})<0$.
--   3. **Dependence on a coordinate set.** For $t\subseteq I$, a function $f$ *depends only on* $t$ if $f(x)=f(y)$ whenever $x_i=y_i$ for all $i\in t$.
--
--   The file also proves the elementary Walsh calculus used later: $\operatorname{sgn}(a\oplus b)=\operatorname{sgn}(a)\operatorname{sgn}(b)$ and $\operatorname{sgn}(b)^2=1$; the average is linear, equals $c$ on the constant $c$ over a nonempty set, and is invariant under bijections; $\chi_\emptyset=1$, $\chi_{\{i\}}(x)=\operatorname{sgn}(x_i)$ and $\chi_s^2=1$; the reflection rules
--   $$\chi_s(R_ax)=\chi_s(a)\,\chi_s(x),\qquad \widehat{f\circ R_a}(s)=\chi_s(a)\,\hat f(s);$$
--   the characterization that $\deg f\le d$ if and only if $\hat f(s)=0$ for every $s$ with $|s|>d$; and the junta bound: if $f$ depends only on $t$, then $\hat f(s)=0$ for every $s\not\subseteq t$, hence $\deg f\le|t|$.
--
--   Reflecting by the positive mask replaces every first-order coefficient $\hat f(\{i\})$ by $|\hat f(\{i\})|$ while preserving the degree and the property of taking only the values $\pm1$; this is how unboundedness of absolute first-order sums is reduced to signed ones. The junta bound is the basic degree estimate for indicator functions of observations that read only a few coordinates.
--
--   **Formalization Note** `Cube ι` is `ι → Bool`; `sign`, `average`, `character`, `fourierCoeff` and `fourierDegree` come from the base definitions of the project, and `fourierDegree f` is the supremum of `Finset.card` over the subsets with nonzero coefficient, so it is $0$ for constant functions. The new definitions are `reflection` (an `Equiv` of the cube), `positiveMask` and `DependsOn`; the lemmas include `sign_xor`, `average_equiv`, `average_const` (which assumes a nonempty type), `character_reflection`, `fourierCoeff_reflection`, `fourierDegree_le_iff`, `fourierCoeff_eq_zero_of_not_subset` and `fourierDegree_le_card_of_dependsOn`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Walsh.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Walsh.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SquareRootDegree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SquareRootDegree

namespace OAI

/-!
Bool encodes a sign: false is +1 and true is -1. The average is uniform,
and degree is ordinary real Fourier degree, not F₂ degree or threshold degree.
-/

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Finite Walsh calculus -/

@[simp] theorem sign_false : sign false = 1 := rfl
@[simp] theorem sign_true : sign true = -1 := rfl

@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

@[simp] theorem sign_xor (a b : Bool) : sign (Bool.xor a b) = sign a * sign b := by
  cases a <;> cases b <;> norm_num [sign]

@[simp] theorem average_zero {α : Type*} [Fintype α] :
    average (fun _ : α => 0) = 0 := by simp [average]

theorem average_mul_const {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    average (fun x => f x * c) = average f * c := by
  simp [average, ← Finset.sum_mul, mul_assoc]

theorem average_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    average (fun x => c * f x) = c * average f := by
  simp only [mul_comm c, average_mul_const]

theorem average_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α => c) = c := by
  simp [average, Fintype.card_ne_zero]

theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : average (fun x => f (e x)) = average f := by
  simp only [average, Fintype.card_congr e, e.sum_comp]

@[simp] theorem character_empty {ι : Type*} (x : Cube ι) : character ∅ x = 1 := by
  simp [character]

@[simp] theorem character_singleton {ι : Type*} (i : ι) (x : Cube ι) :
    character {i} x = sign (x i) := by simp [character]

@[simp] theorem character_sq {ι : Type*} (s : Finset ι) (x : Cube ι) :
    character s x ^ 2 = 1 := by
  simp [character, ← Finset.prod_pow]

def reflection {ι : Type*} (a : Cube ι) : Cube ι ≃ Cube ι where
  toFun x i := Bool.xor (a i) (x i)
  invFun x i := Bool.xor (a i) (x i)
  left_inv x := by
    funext i
    change Bool.xor (a i) (Bool.xor (a i) (x i)) = x i
    cases a i <;> cases x i <;> rfl
  right_inv x := by
    funext i
    change Bool.xor (a i) (Bool.xor (a i) (x i)) = x i
    cases a i <;> cases x i <;> rfl

@[simp] theorem reflection_involutive {ι : Type*} (a x : Cube ι) :
    reflection a (reflection a x) = x := (reflection a).left_inv x

theorem character_reflection {ι : Type*} (a x : Cube ι) (s : Finset ι) :
    character s (reflection a x) = character s a * character s x := by
  simp [character, reflection, sign_xor, Finset.prod_mul_distrib]

theorem fourierCoeff_reflection {ι : Type*} [Fintype ι]
    (f : Cube ι → ℝ) (a : Cube ι) (s : Finset ι) :
    fourierCoeff (fun x => f (reflection a x)) s = character s a * fourierCoeff f s := by
  classical
  unfold fourierCoeff
  rw [← average_equiv (reflection a) (fun x => f (reflection a x) * character s x)]
  simp only [reflection_involutive, character_reflection]
  calc
    _ = average (fun x => character s a * (f x * character s x)) := by
      congr 1
      funext x
      ring
    _ = _ := average_const_mul _ _

def positiveMask {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : Cube ι := by
  classical
  exact fun i => decide (fourierCoeff f {i} < 0)

theorem fourierCoeff_eq_zero_of_degree_lt {ι : Type*} [Fintype ι]
    (f : Cube ι → ℝ) {s : Finset ι} (h : fourierDegree f < s.card) :
    fourierCoeff f s = 0 := by
  classical
  by_contra hc
  have hs := Finset.le_sup (s := Finset.univ.filter (fun s : Finset ι => fourierCoeff f s ≠ 0))
    (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  exact (not_le_of_gt h) hs

theorem fourierDegree_le_iff {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) (d : ℕ) :
    fourierDegree f ≤ d ↔ ∀ s : Finset ι, d < s.card → fourierCoeff f s = 0 := by
  classical
  constructor
  · intro h s hs
    exact fourierCoeff_eq_zero_of_degree_lt f (lt_of_le_of_lt h hs)
  · intro h
    apply Finset.sup_le
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact le_of_not_gt (fun hd => hs (h s hd))

/-! ### Degree calculus for finite observations -/

def DependsOn {ι : Type*} (s : Finset ι) (f : Cube ι → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y

theorem fourierCoeff_eq_zero_of_not_subset {ι : Type*} [Fintype ι]
    {f : Cube ι → ℝ} {s t : Finset ι} (hf : DependsOn t f) (hst : ¬ s ⊆ t) :
    fourierCoeff f s = 0 := by
  classical
  obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp hst
  let a : Cube ι := fun j => decide (j = i)
  have hfa : (fun x => f (reflection a x)) = f := by
    funext x
    apply hf
    intro j hj
    have hji : j ≠ i := by rintro rfl; exact hit hj
    simp [reflection, a, hji]
  have hca : character s a = -1 := by
    simp [character, a, sign, Finset.prod_ite_eq', hi]
  have h := fourierCoeff_reflection f a s
  rw [hfa, hca] at h
  linarith

theorem fourierDegree_le_card_of_dependsOn {ι : Type*} [Fintype ι]
    {f : Cube ι → ℝ} {t : Finset ι} (hf : DependsOn t f) : fourierDegree f ≤ t.card := by
  rw [fourierDegree_le_iff]
  intro s hs
  apply fourierCoeff_eq_zero_of_not_subset hf
  exact fun hst => (not_le_of_gt hs) (Finset.card_le_card hst)

end SquareRootDegree

end

end OAI


