-- Prove2me | Definitions.Def_EnsembleSpaceDraft_axioms
-- name    : EnsembleSpaceDraft_axioms
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-18T11:47:20.238145+00:00
-- url     : https://prove2.me/theorems/dd8b8ad5-b77b-4311-a417-a9edf2340212
-- title:
--   Ensemble space: axioms of ensemble and mixture
-- statement:
--   An **ensemble space** is the structure the 12 October 2026 draft places on the preparations of a physical system, before any entropy is introduced.
--
--   Let $E$ be a topological space. The data are:
--
--   1. $E$ is nonempty, $T_0$, and second countable (Axiom 1.4).
--   2. A mixing operation $pa+\bar p b$, written below as the value of the operation at the coefficient $p\in[0,1]$ and the ensembles $a,b$. The operation is continuous in $(p,a,b)$, and it satisfies identity, idempotence, commutativity, and the associativity identity of Axiom 1.7. Explicitly, if $p_1,p_3\in[0,1)$, $p_1+p_3\le 1$ and $p_2=1-p_1-p_3$, then
--   $$
--   p_1 e_1+\bar p_1\Bigl(\frac{p_2}{\bar p_1}e_2+\frac{p_3}{\bar p_1}e_3\Bigr)
--   =\bar p_3\Bigl(\frac{p_1}{\bar p_3}e_1+\frac{p_2}{\bar p_3}e_2\Bigr)+p_3 e_3.
--   $$
--   Binary mixing determines the second coefficient as the complement of the first, so each side is written as two nested binary mixes.
--
--   The same package defines the vocabulary of §1.3. The complement of a coefficient $p$ is $1-p$. An ensemble $c$ is a **component** of $a$ when $a=pc+\bar p d$ for some $d$ and some $p\in(0,1]$. An **extreme** point has no component other than itself. An **internal** point admits every ensemble as a component. A **boundary** point is a point that is not internal. Two ensembles **have a common component** when some ensemble is a component of both, and they are **separate** otherwise.
--
--   A set $A$ is **bounded around** $e$ when every open neighbourhood $U$ of $e$ admits a coefficient $p\in[0,1)$ such that every point $pe+\bar p a$ with $a\in A$ lies in $U$.
--
--   An ensemble is **decomposable** when it equals $pa+\bar p b$ for some $p\in(0,1)$ and some $a\neq b$; **separately decomposable** when those two ensembles may be taken separate; and **multidecomposable** when it admits two decompositions $pa_1+\bar p a_2=qb_1+\bar q b_2$, with coefficients in $(0,1)$ and distinct summands, such that $a_1$ is separate from both $b_1$ and $b_2$. An ensemble is **monodecomposable** when it is not multidecomposable. The space is monodecomposable when every decomposable ensemble is. **Mixtures preserve separateness** when an ensemble separate from $a$ and from $b$ is separate from $pa+\bar p b$ for every $p\in[0,1]$.
--
--   These predicates are the ones used by Corollary 1.25, Propositions 1.17, 1.21 and 1.27, Corollary 1.32, and Proposition 1.35. Entropy is not part of the data.
--
--   **Formalization Note.** Each real coefficient appearing in associativity is proved to lie in $[0,1]$ and is then used as that unit-interval element. The second coefficient of a binary mix is the complement of the first, which is why the inner mixes name only $(1-p_1-p_3)/(1-p_1)$ and $p_1/(1-p_3)$.
-- source:
--   G. Carcassi, C. A. Aidala, Ensemble spaces, draft of 12 October 2026, Chapter 1. Generated from https://github.com/assumptionsofphysics/book (art_pm_EnsembleSpaces). Axiom 1.4, pp. 12–13; Definition 1.6 and Axiom 1.7, pp. 13–14; Definitions 1.16, 1.19, 1.20, 1.24, pp. 17–22; Definitions 1.28, 1.31, 1.33, pp. 24–26.

import Mathlib

/-!
# Ensemble spaces — axioms of ensemble and mixture

Source: G. Carcassi and C. A. Aidala, draft “Theory of ensemble spaces”, 12 October 2026,
Chapter 1, §§1.2–1.3 (Axiom 1.4, Definition 1.6, Axiom 1.7, Definitions 1.16, 1.19, 1.20,
1.24, 1.28, 1.31, 1.33).

Coefficients that the axiom proves lie in `[0, 1]` are packaged with `unitInterval.mk`
rather than projected. `Set.projIcc` is not used here.
-/

open scoped unitInterval
open unitInterval

namespace EnsembleSpaceDraft

universe u

/-- `p ∈ [0, 1]` from the two inequalities. -/
lemma mem_unitInterval_of_bounds {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : p ∈ unitInterval :=
  ⟨h0, h1⟩

/-- First coefficient of the left-hand inner mixture in Axiom 1.7, `(1 - p₁ - p₃) / (1 - p₁)`. -/
lemma assoc_left_coeff_mem {p₁ p₃ : ℝ} (_hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ < 1) (_hp₃0 : 0 ≤ p₃)
    (_hp₃1 : p₃ < 1) (hsum : p₁ + p₃ ≤ 1) :
    (1 - p₁ - p₃) / (1 - p₁) ∈ unitInterval := by
  have hden : 0 < 1 - p₁ := by linarith
  have hnum : 0 ≤ 1 - p₁ - p₃ := by linarith
  have hle : 1 - p₁ - p₃ ≤ 1 - p₁ := by linarith
  exact div_mem hnum (le_of_lt hden) hle

/-- First coefficient of the right-hand inner mixture in Axiom 1.7, `p₁ / (1 - p₃)`. -/
lemma assoc_right_coeff_mem {p₁ p₃ : ℝ} (hp₁0 : 0 ≤ p₁) (_hp₁1 : p₁ < 1) (_hp₃0 : 0 ≤ p₃)
    (hp₃1 : p₃ < 1) (hsum : p₁ + p₃ ≤ 1) :
    p₁ / (1 - p₃) ∈ unitInterval := by
  have hden : 0 < 1 - p₃ := by linarith
  have hle : p₁ ≤ 1 - p₃ := by linarith
  exact div_mem hp₁0 (le_of_lt hden) hle

/-- `1 - p₃ ∈ [0, 1]` when `p₃ ∈ [0, 1)`. -/
lemma one_sub_mem {p₃ : ℝ} (hp₃0 : 0 ≤ p₃) (hp₃1 : p₃ < 1) : 1 - p₃ ∈ unitInterval :=
  ⟨by linarith, by linarith⟩

/-- Axioms 1.4 and 1.7. An ensemble space is a nonempty `T₀` second-countable space
equipped with a continuous mixing operation `mix p a b = p a + (1 - p) b`. -/
structure EnsembleSpace (E : Type u) [TopologicalSpace E] : Type u where
  /-- Axiom 1.4: at least one preparation exists. -/
  nonempty : Nonempty E
  /-- Axiom 1.4: the topology is `T₀`. -/
  t0 : T0Space E
  /-- Axiom 1.4: the topology is second countable. -/
  secondCountable : SecondCountableTopology E
  /-- Axiom 1.7: mixing. -/
  mix : unitInterval → E → E → E
  /-- Continuity of mixing on `[0, 1] × E × E`. -/
  continuous_mix : Continuous fun x : unitInterval × E × E => mix x.1 x.2.1 x.2.2
  /-- Identity: `1 a + 0 b = a`. -/
  mix_one : ∀ a b : E, mix 1 a b = a
  /-- Idempotence: `p a + (1 - p) a = a`. -/
  mix_self : ∀ (p : unitInterval) (a : E), mix p a a = a
  /-- Commutativity: `p a + (1 - p) b = (1 - p) b + p a`. -/
  mix_comm : ∀ (p : unitInterval) (a b : E), mix p a b = mix (symm p) b a
  /-- Associativity (Axiom 1.7). For `p₁, p₃ ∈ [0, 1)` with `p₁ + p₃ ≤ 1` and
  `p₂ = 1 - p₁ - p₃`,
  `p₁ e₁ + (1 - p₁) ((p₂ / (1 - p₁)) e₂ + (p₃ / (1 - p₁)) e₃)
    = (1 - p₃) ((p₁ / (1 - p₃)) e₁ + (p₂ / (1 - p₃)) e₂) + p₃ e₃`.
  Binary mixing writes only the first coefficient; the second is its complement. -/
  mix_assoc : ∀ (p₁ p₃ : ℝ) (e₁ e₂ e₃ : E) (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ < 1)
    (hp₃0 : 0 ≤ p₃) (hp₃1 : p₃ < 1) (hsum : p₁ + p₃ ≤ 1),
    mix ⟨p₁, mem_unitInterval_of_bounds hp₁0 (le_of_lt hp₁1)⟩ e₁
        (mix ⟨(1 - p₁ - p₃) / (1 - p₁),
            assoc_left_coeff_mem hp₁0 hp₁1 hp₃0 hp₃1 hsum⟩ e₂ e₃) =
      mix ⟨1 - p₃, one_sub_mem hp₃0 hp₃1⟩
        (mix ⟨p₁ / (1 - p₃), assoc_right_coeff_mem hp₁0 hp₁1 hp₃0 hp₃1 hsum⟩ e₁ e₂)
        e₃

namespace EnsembleSpace

variable {E : Type u} [TopologicalSpace E]

/-- Definition 1.6: the complement of a mixing coefficient. -/
def compl (p : unitInterval) : unitInterval :=
  symm p

/-- Definition 1.19: `c` is a component of `a` when `a = p c + (1 - p) d` for some
`d` and some `p ∈ (0, 1]`. -/
def IsComponent (X : EnsembleSpace E) (c a : E) : Prop :=
  ∃ (p : unitInterval) (d : E), 0 < (p : ℝ) ∧ a = X.mix p c d

/-- Definition 1.20: an extreme point has no component distinct from itself. -/
def IsExtreme (X : EnsembleSpace E) (e : E) : Prop :=
  ∀ (p : unitInterval) (a b : E), 0 < (p : ℝ) → e = X.mix p a b → a = e

/-- Definition 1.20: an internal point admits every ensemble as a component. -/
def IsInternal (X : EnsembleSpace E) (e : E) : Prop :=
  ∀ a : E, ∃ (p : unitInterval) (b : E), 0 < (p : ℝ) ∧ e = X.mix p a b

/-- Definition 1.20: a boundary point is an ensemble that is not internal. -/
def IsBoundary (X : EnsembleSpace E) (e : E) : Prop :=
  ¬ X.IsInternal e

/-- Definition 1.24: `a` and `b` have a common component. -/
def HasCommonComponent (X : EnsembleSpace E) (a b : E) : Prop :=
  ∃ c : E, X.IsComponent c a ∧ X.IsComponent c b

/-- Definition 1.24: `a` and `b` are separate (no common component). -/
def Separate (X : EnsembleSpace E) (a b : E) : Prop :=
  ¬ X.HasCommonComponent a b

/-- Definition 1.16: `A` is bounded around `e` when every open neighbourhood of `e`
contains a nontrivial shrink `p e + (1 - p) A` for some `p ∈ [0, 1)`. -/
def BoundedAround (X : EnsembleSpace E) (A : Set E) (e : E) : Prop :=
  ∀ U : Set E, IsOpen U → e ∈ U →
    ∃ p : unitInterval, (p : ℝ) < 1 ∧ (fun a => X.mix p e a) '' A ⊆ U

/-- Definition 1.31: decomposable by a nontrivial mixture of two distinct ensembles.
Mixture coefficients lie in `(0, 1)`. -/
def IsDecomposable (X : EnsembleSpace E) (e : E) : Prop :=
  ∃ (p : unitInterval) (a b : E), 0 < (p : ℝ) ∧ (p : ℝ) < 1 ∧ a ≠ b ∧ e = X.mix p a b

/-- Definition 1.31: separately decomposable, by a nontrivial mixture of two separate ensembles. -/
def IsSeparatelyDecomposable (X : EnsembleSpace E) (e : E) : Prop :=
  ∃ (p : unitInterval) (a b : E),
    0 < (p : ℝ) ∧ (p : ℝ) < 1 ∧ X.Separate a b ∧ e = X.mix p a b

/-- Definition 1.31: multidecomposable. Two nontrivial decompositions into distinct ensembles,
with one component of the first separate from both components of the second. -/
def IsMultidecomposable (X : EnsembleSpace E) (e : E) : Prop :=
  ∃ (p q : unitInterval) (a₁ a₂ b₁ b₂ : E),
    0 < (p : ℝ) ∧ (p : ℝ) < 1 ∧ 0 < (q : ℝ) ∧ (q : ℝ) < 1 ∧
      a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧
      e = X.mix p a₁ a₂ ∧ e = X.mix q b₁ b₂ ∧
      X.Separate a₁ b₁ ∧ X.Separate a₁ b₂

/-- Definition 1.31: monodecomposable as an ensemble (not multidecomposable). -/
def IsMonodecomposable (X : EnsembleSpace E) (e : E) : Prop :=
  ¬ X.IsMultidecomposable e

/-- Definition 1.33: the space is monodecomposable when every decomposable ensemble is. -/
def Monodecomposable (X : EnsembleSpace E) : Prop :=
  ∀ e : E, X.IsDecomposable e → X.IsMonodecomposable e

/-- Definition 1.28: mixtures preserve separateness. -/
def MixturesPreserveSeparateness (X : EnsembleSpace E) : Prop :=
  ∀ (e a b : E) (p : unitInterval),
    X.Separate e a → X.Separate e b → X.Separate e (X.mix p a b)

end EnsembleSpace

end EnsembleSpaceDraft


