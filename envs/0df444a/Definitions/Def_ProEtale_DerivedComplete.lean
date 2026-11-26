-- Prove2me | Definitions.Def_ProEtale_DerivedComplete
-- name    : ProEtale_DerivedComplete
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T12:26:42.473447+00:00
-- url     : https://prove2.me/theorems/6f4df75e-49c1-5f7e-88bd-5cb8556efd68
-- title:
--   Derived completeness of a module with respect to an ideal
-- statement:
--   Let $R$ be a commutative ring, $x \in R$ and $M$ an $R$-module. Consider the tower $\cdots \xrightarrow{x} M \xrightarrow{x} M \xrightarrow{x} M$ whose transition maps are all multiplication by $x$, and the $R$-linear endomorphism
--
--   $$
--   \delta_x : M^{\mathbb N} \to M^{\mathbb N}, \qquad (m_n)_n \mapsto (m_n - x\, m_{n+1})_n
--   $$
--
--   (`ProEtale.towerDiff x M`). Its kernel is the inverse limit of the tower and its cokernel is the first derived limit, so the derived limit $T(M, x) = R\varprojlim(\cdots \xrightarrow{x} M \xrightarrow{x} M)$ vanishes if and only if $\delta_x$ is bijective.
--
--   For an ideal $I \subseteq R$, the module $M$ is **derived $I$-complete** (`ProEtale.IsDerivedComplete I M`) if $\delta_x$ is bijective for every $x \in I$.
--
--   This is Definition 3.4.1 of the paper in the case where the replete topos is the category of sets. It is the notion of completeness that is stable under kernels, cokernels and extensions, unlike classical $I$-adic completeness.
--
--   **Formalization Note** This file is written for the mission; it is not extracted from the Lean project the other definition files come from. The condition is imposed for all $x \in I$, not only for a set of generators.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Definition 3.4.1 (p. 21 of the arXiv v2 PDF), for X = Set. Written for this mission; the same formulation, for a principal ideal, is used in leanprover-community/riemann-hypothesis, branch main (Apache-2.0, Lean v4.37.0-rc1; readable edition of the Alpöge–Claude formalization), file src/Lib/PadicComparison/Completion.lean (`New.Variety.IsDerivedComplete`).

import Mathlib

/-!
# Derived completeness of a module with respect to an ideal

Bhatt–Scholze, *The pro-étale topology for schemes*, Definition 3.4.1, in the case where the
replete topos is the category of sets: for a commutative ring `R`, an ideal `I` and an
`R`-module `M`, the module `M` is derived `I`-complete if for every `x ∈ I` the derived
limit `T(M, x) = R lim (⋯ → M → M → M)` of the tower with all transition maps
multiplication by `x` vanishes.

The limit and the first derived limit of that tower are the kernel and the cokernel of the
endomorphism `(mₙ)ₙ ↦ (mₙ - x • mₙ₊₁)ₙ` of `ℕ → M`, and its higher derived limits vanish, so
`T(M, x) = 0` if and only if this endomorphism is bijective. This is the form used here.

Written for the Prove2me mission on the pro-étale topology; it is not part of the Lean
project the other definition files of the mission are extracted from.
-/

universe u v

namespace ProEtale

variable {R : Type u} [CommRing R]

/-- For `x : R` and an `R`-module `M`, the `R`-linear endomorphism
`(mₙ)ₙ ↦ (mₙ - x • mₙ₊₁)ₙ` of the module of sequences `ℕ → M`. Its kernel is the limit, and
its cokernel the first derived limit, of the tower `⋯ → M → M → M` whose transition maps are
all multiplication by `x`. -/
def towerDiff (x : R) (M : Type v) [AddCommGroup M] [Module R M] : (ℕ → M) →ₗ[R] (ℕ → M) where
  toFun m n := m n - x • m (n + 1)
  map_add' m m' := by
    funext n
    simp only [Pi.add_apply, smul_add]
    abel
  map_smul' r m := by
    funext n
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, smul_comm r x]

@[simp]
lemma towerDiff_apply (x : R) (M : Type v) [AddCommGroup M] [Module R M] (m : ℕ → M) (n : ℕ) :
    towerDiff x M m n = m n - x • m (n + 1) :=
  rfl

/-- An `R`-module `M` is **derived `I`-complete** if for every `x ∈ I` the derived limit of
the tower `⋯ → M → M → M` with transition maps multiplication by `x` vanishes, i.e. the
endomorphism `towerDiff x M` of `ℕ → M` is bijective
(Bhatt–Scholze, Definition 3.4.1, for the topos of sets). -/
def IsDerivedComplete (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∀ x ∈ I, Function.Bijective (towerDiff x M)

end ProEtale


