-- Prove2me | Definitions.Def_Garrido_BooleanExtension
-- name    : Garrido_BooleanExtension
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-03T22:11:13.227186+00:00
-- url     : https://prove2.me/theorems/fb7629dc-807c-4475-8fd7-4eadd64b7a70
-- title:
--   Garrido, Theorems 2.6 and 2.7 — subrings of a boolean algebra, measures on them, and the Invariant Extension Theorem
-- statement:
--   Definitions for stating Garrido's Theorems 2.6 and 2.7 (p. 7) at the generality printed: for an arbitrary boolean algebra, not only the algebra of all subsets of a set. Garrido writes on p. 7: “**Theorem 2.6** (Invariant Extension Theorem). *Recall Carathéodory’s Extension Theorem: If $\mathcal R$ is a subring of the boolean algebra $\mathcal A$ and $\mu$ is a measure on $\mathcal R$, then $\mu$ can be extended to a measure $\bar\mu$ on $\mathcal A$.* *If $G$ is an amenable group of automorphisms of $\mathcal A$ and $\mathcal R$, $\mu$ are $G$-invariant, then $\bar\mu$ can be chosen to be $G$-invariant.*”
--
--   - `IsBooleanSubring R`: `R` contains `⊥` and is closed under `⊔` and `\`. The notes do not define “subring of the boolean algebra”; this is the sense in which Carathéodory's theorem is stated for rings of sets (closed under unions and differences, hence also under meets). It includes the subrings that contain `⊤`, so the theorems stated with it are at their strongest.
--   - `IsFinitelyAdditiveOn R μ`: `μ : A → [0, ∞]` with `μ ⊥ = 0` and `μ (a ⊔ b) = μ a + μ b` for disjoint `a, b ∈ R`. A “measure” in the notes is finitely additive with values in $[0, \infty]$ (§1); the values of `μ` outside `R` play no role. A measure on the whole algebra is `IsFinitelyAdditiveOn Set.univ`.
--   - `SatisfiesInvariantExtensionTheorem G`: “$G$ satisfies the Invariant Extension Theorem” (Theorem 2.7, item 4), the conclusion of Theorem 2.6 for $G$. For every boolean algebra `A`, every action `ρ : G →* (A ≃o A)` of $G$ by automorphisms (an order automorphism of a boolean algebra preserves `⊔`, `⊓`, `⊥`, `⊤` and complements), every subring `R` with `ρ g r ∈ R` for `r ∈ R`, and every finitely additive `μ` on `R` with `μ (ρ g r) = μ r`, there is a finitely additive `μbar` on all of `A` that agrees with `μ` on `R` and satisfies `μbar (ρ g a) = μbar a` for all `g` and `a`. The notes speak of “a group of automorphisms of $\mathcal A$”; an action contains that case (the inclusion of the group) and asks no more, since the image of an amenable group under a homomorphism is amenable. The algebras range over `Type (max u v)` for `G : Type u`, as in `Garrido.HasInvariantExtensionProperty`, so that the algebra of all subsets of $G$ is among them.
--
--   `Garrido.HasInvariantExtensionProperty` (the [Garrido amenability definitions](https://prove2.me/theorems/66ed88ff-6df9-4c35-af46-fb50c2a87c1f)) is the special case of all subsets of a $G$-set, with an extension of $\mu$ to all subsets supplied as a hypothesis; `SatisfiesInvariantExtensionTheorem` is the property as the notes state it.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 7, Theorems 2.6 and 2.7; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib

open scoped ENNReal

namespace Garrido

universe u v

/-- A subring of a boolean algebra (Garrido, p. 7, Theorem 2.6): contains `⊥` and is closed under
`⊔` and `\`. -/
def IsBooleanSubring {A : Type*} [BooleanAlgebra A] (R : Set A) : Prop :=
  ⊥ ∈ R ∧ ∀ a ∈ R, ∀ b ∈ R, a ⊔ b ∈ R ∧ a \ b ∈ R

/-- A finitely additive measure on `R` (Garrido, p. 7, Theorem 2.6): values in `[0, ∞]`, `⊥` has
measure `0`, and the measures of two disjoint elements of `R` add. -/
def IsFinitelyAdditiveOn {A : Type*} [BooleanAlgebra A] (R : Set A) (μ : A → ℝ≥0∞) : Prop :=
  μ ⊥ = 0 ∧ ∀ a ∈ R, ∀ b ∈ R, Disjoint a b → μ (a ⊔ b) = μ a + μ b

/-- `G` satisfies the Invariant Extension Theorem (Garrido, p. 7, Theorems 2.6 and 2.7): for every
action of `G` on a boolean algebra by automorphisms, every finitely additive measure on a
`G`-invariant subring that is `G`-invariant extends to a `G`-invariant finitely additive measure on
the whole algebra. -/
def SatisfiesInvariantExtensionTheorem (G : Type u) [Group G] : Prop :=
  ∀ (A : Type (max u v)) [BooleanAlgebra A] (ρ : G →* (A ≃o A)) (R : Set A),
    IsBooleanSubring R → (∀ (g : G), ∀ r ∈ R, ρ g r ∈ R) →
    ∀ μ : A → ℝ≥0∞, IsFinitelyAdditiveOn R μ → (∀ (g : G), ∀ r ∈ R, μ (ρ g r) = μ r) →
    ∃ μbar : A → ℝ≥0∞, IsFinitelyAdditiveOn Set.univ μbar ∧ (∀ r ∈ R, μbar r = μ r) ∧
      ∀ (g : G) (a : A), μbar (ρ g a) = μbar a

end Garrido


