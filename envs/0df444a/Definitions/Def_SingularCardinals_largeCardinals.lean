-- Prove2me | Definitions.Def_SingularCardinals_largeCardinals
-- name    : SingularCardinals_largeCardinals
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T14:47:34.03629+00:00
-- url     : https://prove2.me/theorems/49b2e7ae-6b58-494b-a5f7-f3880412abf5
-- title:
--   κ-complete filters, normal measures, strongly compact cardinals
-- statement:
--   Large-cardinal notions used in Scott's and Solovay's theorems. Fix a cardinal $\kappa$.
--
--   1. A filter $F$ on a set $X$ is **$\kappa$-complete** if for every family $(S_i)_{i\in I}$ of members of $F$ with $|I|<\kappa$, also $\bigcap_{i\in I}S_i\in F$.
--   2. A **normal measure on $\kappa$** is an ultrafilter $D$ on the ordinals such that: the set of ordinals below $\kappa$ belongs to $D$; $D$ is $\kappa$-complete; $D$ contains no singleton; and $D$ is normal: whenever $A\in D$ and $f$ is regressive on $A$ (that is, $f(\alpha)<\alpha$ for all $\alpha\in A$), there is $\beta$ with $\{\alpha: f(\alpha)=\beta\}\in D$.
--   3. $\kappa$ is **strongly compact** if $\kappa>\aleph_0$ and, for every set $X$, every proper $\kappa$-complete filter on $X$ extends to a $\kappa$-complete ultrafilter on $X$.
--
--   An uncountable $\kappa$ carrying a normal measure is a measurable cardinal; normality is what makes "a set of measure one below $\kappa$" the right notion in Scott's theorem.
--
--   **Formalization Note** A measure on $\kappa$ is represented as an ultrafilter on the type of all ordinals of the same universe that contains $\{\alpha:\alpha<\kappa\}$. Families in the completeness condition are indexed by types of the same universe as $\kappa$. "Proper" means the filter is not the filter of all subsets (`Filter.NeBot`); without it no cardinal would be strongly compact.
-- source:
--   Wikipedia, "Singular cardinals hypothesis", revision oldid=1349753131, https://en.wikipedia.org/w/index.php?title=Singular_cardinals_hypothesis&oldid=1349753131, paragraphs on Scott's theorem and on Solovay's theorem (standard definitions of normal measure and strongly compact cardinal as in Jech, Set Theory, 3rd ed., Ch. 10 and Ch. 20).

import Mathlib

universe u v

namespace SingularCardinals

open Cardinal

/-- A filter `F` is `κ`-complete if it is closed under intersections of fewer than `κ`
of its members. -/
def IsComplete (κ : Cardinal.{u}) {X : Type v} (F : Filter X) : Prop :=
  ∀ (ι : Type u) (s : ι → Set X), #ι < κ → (∀ i, s i ∈ F) → (⋂ i, s i) ∈ F

/-- `D` is a normal measure on `κ`: an ultrafilter on the ordinals that concentrates on the
ordinals below `κ`, is `κ`-complete and nonprincipal, and is normal (every function that is
regressive on a set in `D` is constant on a set in `D`). -/
structure IsNormalMeasure (κ : Cardinal.{u}) (D : Ultrafilter Ordinal.{u}) : Prop where
  Iio_mem : Set.Iio κ.ord ∈ D
  complete : IsComplete κ (D : Filter Ordinal.{u})
  nonprincipal : ∀ α : Ordinal.{u}, ({α} : Set Ordinal.{u}) ∉ D
  normal : ∀ A ∈ D, ∀ f : Ordinal.{u} → Ordinal.{u}, (∀ α ∈ A, f α < α) →
    ∃ β : Ordinal.{u}, {α | f α = β} ∈ D

/-- `κ` is strongly compact if it is uncountable and every proper `κ`-complete filter on any
set extends to a `κ`-complete ultrafilter. -/
def IsStronglyCompact (κ : Cardinal.{u}) : Prop :=
  ℵ₀ < κ ∧ ∀ (X : Type u) (F : Filter X), F.NeBot → IsComplete κ F →
    ∃ U : Ultrafilter X, IsComplete κ (U : Filter X) ∧ (U : Filter X) ≤ F

end SingularCardinals


