-- Prove2me | Definitions.Def_UltimateL_InternalWoodin
-- name    : UltimateL_InternalWoodin
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T21:37:46.838234+00:00
-- url     : https://prove2.me/theorems/ff9c5e8f-e982-412b-b66f-b8a32132707e
-- title:
--   Woodin cardinals computed inside an inner model
-- statement:
--   These are the relativizations, to a class $N$, of the large-cardinal notions needed to say that $N$ satisfies 'there is a proper class of Woodin cardinals'. A cardinal $\delta$ is a **cardinal in $N$** if $\delta\in N$ and no function belonging to $N$ maps a smaller ordinal onto $\delta$. A function $j$ is a **definable class function of $N$** if it maps $N$ into $N$ and its graph is defined over $(N,\in)$ by a first-order formula with parameters from $N$; an **elementary embedding of $N$ into a transitive subclass $M'\subseteq N$** preserves every first-order formula. Then $\delta$ is **Woodin in $N$** exactly when the platform's definition of a Woodin cardinal is read inside $N$: for every $f:\delta\to\delta$ in $N$ there is $\kappa<\delta$ closed under $f$ and a definable class elementary embedding of $N$ with critical point $\kappa$ whose target contains $V_{j(f)(\kappa)}^N$. Requiring the embeddings to be definable classes of $N$ is what makes this the internal notion, since $N\models\mathrm{ZFC}$ has only definable classes.
-- source:
--   W. Hugh Woodin, In Search of Ultimate-L, BSL 23(1) (2017) 1-109, doi:10.1017/bsl.2016.34, Definition 7.14 clause (1) ('there is a proper class of Woodin cardinals', read inside a model); the external Woodin definition is the platform's OmegaLogic.IsWoodin (after Bagaria–Castells–Larson, An Ω-logic primer, Definition 1.5).

import Mathlib
import Definitions.Def_OmegaLogic_Semantics
import Definitions.Def_OmegaLogic_LargeCardinals

namespace UltimateL

universe u

open ZFSet OmegaLogic

/-- `δ` is a cardinal as computed in the class `N`: `δ ∈ N` and no function in `N` maps a
smaller ordinal onto `δ`. -/
def IsCardinalIn (N : Set ZFSet.{u}) (δ : Ordinal.{u}) : Prop :=
  δ.toZFSet ∈ N ∧
  ¬ ∃ β < δ, ∃ f : ZFSet.{u}, f ∈ N ∧ IsFunc β.toZFSet δ.toZFSet f ∧
    ∀ γ < δ, ∃ b < β, pair b.toZFSet γ.toZFSet ∈ f

/-- The function `j` is a definable class function of `N`: it maps `N` into `N` and its graph
is defined over `(N, ∈)` by a first-order formula with parameters from `N`. -/
def IsDefinableClassFunction (N : Set ZFSet.{u}) (j : ZFSet.{u} → ZFSet.{u}) : Prop :=
  (∀ x ∈ N, j x ∈ N) ∧
  ∃ (k : ℕ) (ψ : setLang.Formula (Fin (k + 2))) (p : Fin k → N),
    ∀ (x : N) (y : N), ψ.Realize (Fin.cons x (Fin.cons y p)) ↔ j x.1 = y.1

/-- `j` is an elementary embedding of `(N, ∈)` into the transitive subclass `M' ⊆ N`:
it maps `N` into `M'` and preserves every first-order formula on assignments from `N`. -/
def IsElementaryEmbeddingIn (N : Set ZFSet.{u}) (j : ZFSet.{u} → ZFSet.{u})
    (M' : Set ZFSet.{u}) : Prop :=
  M' ⊆ N ∧
  (∀ x ∈ M', ∀ y ∈ x, y ∈ M') ∧
  (∀ x ∈ N, j x ∈ M') ∧
  ∀ (k : ℕ) (φ : setLang.Formula (Fin k)) (a : Fin k → N) (b : Fin k → M'),
    (∀ i, (b i).1 = j (a i).1) → (φ.Realize a ↔ φ.Realize b)

/-- `δ` is a Woodin cardinal as computed in `N` (the relativization of the platform's
`OmegaLogic.IsWoodin`): `δ` is a cardinal in `N` and for every `f : δ → δ` in `N` there is
`κ < δ` closed under `f` and a definable class elementary embedding `j` of `N` with critical
point `κ` such that `V_{j(f)(κ)}^N` is contained in the target of `j`. -/
def IsWoodinIn (N : Set ZFSet.{u}) (δ : Ordinal.{u}) : Prop :=
  IsCardinalIn N δ ∧
  ∀ f : ZFSet.{u}, f ∈ N → IsFunc δ.toZFSet δ.toZFSet f →
    ∃ κ < δ, (∀ β < κ, ∀ y, pair β.toZFSet y ∈ f → y ∈ κ.toZFSet) ∧
      ∃ (j : ZFSet.{u} → ZFSet.{u}) (M' : Set ZFSet.{u}),
        IsDefinableClassFunction N j ∧ IsElementaryEmbeddingIn N j M' ∧ IsCriticalPoint j κ ∧
        ∃ y ∈ N, pair κ.toZFSet y ∈ j f ∧ ∀ x ∈ N, x.rank < y.rank → x ∈ M'

/-- `N` has a proper class of Woodin cardinals (as computed in `N`). -/
def ProperClassWoodinIn (N : Set ZFSet.{u}) : Prop :=
  ∀ γ : Ordinal.{u}, ∃ δ, γ < δ ∧ IsWoodinIn N δ

end UltimateL


