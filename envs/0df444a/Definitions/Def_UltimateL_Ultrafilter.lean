-- Prove2me | Definitions.Def_UltimateL_Ultrafilter
-- name    : UltimateL_Ultrafilter
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T21:00:44.280976+00:00
-- url     : https://prove2.me/theorems/3130f0c9-a665-4c1e-90f1-e142aa5a2be1
-- title:
--   Supercompactness: $P_\delta(\gamma)$, normal fine ultrafilters, supercompact cardinals
-- statement:
--   This file develops the ultrafilter characterization of supercompactness, following Woodin's Definitions 3.1 and 3.2. For ordinals $\delta<\gamma$, $P_\delta(\gamma)=\{\sigma\subseteq\gamma:|\sigma|<\delta\}$. An **ultrafilter** $U$ on a set $X$ is a family of subsets of $X$ containing $X$, omitting $\varnothing$, closed under supersets and finite intersections, and deciding every subset. It is **$\delta$-complete** if intersections of nonempty families of fewer than $\delta$ members remain in $U$; **fine** if each $\{\sigma:\alpha\in\sigma\}$ ($\alpha<\gamma$) has measure one; and **normal** if every regressive function $f:P_\delta(\gamma)\to\gamma$ is constant on a measure-one set. A cardinal $\delta$ is **supercompact** if it is an uncountable regular cardinal and for every $\gamma>\delta$ there is a $\delta$-complete normal fine ultrafilter on $P_\delta(\gamma)$. Regularity is expressed by boundedness of every function from a smaller ordinal, avoiding any appeal to cofinality machinery.
-- source:
--   W. Hugh Woodin, In Search of Ultimate-L, BSL 23(1) (2017) 1-109, doi:10.1017/bsl.2016.34, Definition 3.1 (P_kappa(lambda), fine, normal) and Definition 3.2 (supercompact cardinal), p. 6-7.

import Mathlib

namespace UltimateL

universe u

open ZFSet

/-- `P_δ(γ) = {σ ⊆ γ : |σ| < δ}`, as a set. -/
noncomputable def pSmall (δ γ : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun σ => σ.card < δ.card) (ZFSet.powerset γ.toZFSet)

/-- `U` is an ultrafilter on the set `X`. -/
def IsUltrafilterOn (U X : ZFSet.{u}) : Prop :=
  U ⊆ ZFSet.powerset X ∧
  (∅ : ZFSet) ∉ U ∧
  X ∈ U ∧
  (∀ A ∈ U, ∀ B ∈ ZFSet.powerset X, A ⊆ B → B ∈ U) ∧
  (∀ A ∈ U, ∀ B ∈ U, A ∩ B ∈ U) ∧
  (∀ A ∈ ZFSet.powerset X, A ∈ U ∨ (X \ A) ∈ U)

/-- `U` is `δ`-complete: the intersection of any nonempty family of fewer than `δ` members of
`U` again lies in `U`. -/
def IsComplete (U : ZFSet.{u}) (δ : Ordinal.{u}) : Prop :=
  ∀ S ∈ ZFSet.powerset U, (∃ A, A ∈ S) → S.card < δ.card → (⋂₀ S) ∈ U

/-- `U` is fine on `P_δ(γ)`: for each `α < γ`, the set `{σ ∈ P_δ(γ) : α ∈ σ}` lies in `U`. -/
def IsFine (U : ZFSet.{u}) (δ γ : Ordinal.{u}) : Prop :=
  ∀ α < γ, ZFSet.sep (fun σ => α.toZFSet ∈ σ) (pSmall δ γ) ∈ U

/-- `U` is normal on `P_δ(γ)`: every function `f : P_δ(γ) → γ` that is regressive on a
measure-one set is constant on a measure-one set. -/
def IsNormal (U : ZFSet.{u}) (δ γ : Ordinal.{u}) : Prop :=
  ∀ f : ZFSet.{u}, IsFunc (pSmall δ γ) γ.toZFSet f →
    ZFSet.sep (fun σ => ∃ y, pair σ y ∈ f ∧ y ∈ σ) (pSmall δ γ) ∈ U →
    ∃ α < γ, ZFSet.sep (fun σ => ∃ y, pair σ y ∈ f ∧ y = α.toZFSet) (pSmall δ γ) ∈ U

/-- An uncountable regular cardinal: a cardinal `δ > ω` such that every function from a smaller
ordinal into `δ` is bounded below `δ`. -/
def IsRegularCardinal (δ : Ordinal.{u}) : Prop :=
  δ.card.ord = δ ∧ Ordinal.omega0 < δ ∧
  ∀ β < δ, ∀ f : ZFSet.{u}, IsFunc β.toZFSet δ.toZFSet f →
    ∃ γ < δ, ∀ α < β, ∀ y, pair α.toZFSet y ∈ f → y ∈ γ.toZFSet

/-- `δ` is supercompact (Woodin, Definition 3.2): an uncountable regular cardinal such that for
every `γ > δ` there is a `δ`-complete normal fine ultrafilter on `P_δ(γ)`. -/
def IsSupercompact (δ : Ordinal.{u}) : Prop :=
  IsRegularCardinal δ ∧
  ∀ γ > δ, ∃ U : ZFSet.{u},
    IsUltrafilterOn U (pSmall δ γ) ∧ IsComplete U δ ∧ IsFine U δ γ ∧ IsNormal U δ γ

end UltimateL


