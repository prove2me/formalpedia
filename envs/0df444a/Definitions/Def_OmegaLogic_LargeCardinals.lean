-- Prove2me | Definitions.Def_OmegaLogic_LargeCardinals
-- name    : OmegaLogic_LargeCardinals
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T16:33:27.910856+00:00
-- url     : https://prove2.me/theorems/0a478381-639f-4baf-8b4e-dc2f3490cdf9
-- title:
--   Ω-logic III: Woodin cardinals and proper classes of large cardinals
-- statement:
--   Large-cardinal hypotheses used in Ω-logic. The universe of sets is `ZFSet.{u}`, and an ordinal $\beta$ is identified with the von Neumann ordinal `β.toZFSet`.
--
--   **Elementary embeddings.** `IsElementaryEmbedding j N` says that $N$ is a transitive class, that $j : V \to N$, and that for every formula $\varphi(x_0, \dots, x_{k-1})$ of set theory and all sets $a_0, \dots, a_{k-1}$,
--   $$V \models \varphi(\vec a) \iff N \models \varphi(j(\vec a)).$$
--   `IsCriticalPoint j κ` says that $j(\beta) = \beta$ for all ordinals $\beta < \kappa$ and $j(\kappa) \neq \kappa$.
--
--   **Woodin cardinals** (primer, Definition 1.5). `IsWoodin δ` says that $\delta$ is a cardinal and that for every function $f : \delta \to \delta$, given as a set of ordered pairs, there is $\kappa < \delta$ with $f[\kappa] \subseteq \kappa$ and an elementary embedding $j : V \to N$ with critical point $\kappa$ such that
--   $$V_{j(f)(\kappa)} \subseteq N .$$
--
--   `ProperClassWoodin` says that the Woodin cardinals are unbounded in the ordinals. `ProperClassInaccessible` says the same of the strongly inaccessible cardinals.
--
--   Classes, such as $j$ and $N$, are arbitrary Lean functions and predicates on `ZFSet`. For Woodin cardinals this is equivalent to the first-order definition by extenders.
-- source:
--   J. Bagaria, N. Castells, P. Larson, "An Ω-logic primer", in Set Theory (Trends in Mathematics), Birkhäuser 2006, pp. 1–28, doi:10.1007/3-7643-7692-9_1; online version https://paulblarson.github.io/omegalogicmaster5.pdf, Definition 1.5 (p. 3).

import Definitions.Def_OmegaLogic_Semantics

/-!
# Ω-logic, part 3: Woodin cardinals

* `OmegaLogic.IsElementaryEmbedding j N` : `j : V → N` is an elementary embedding of the
  universe into a transitive class `N`.
* `OmegaLogic.IsWoodin δ` : `δ` is a Woodin cardinal.
* `OmegaLogic.ProperClassWoodin`, `OmegaLogic.ProperClassInaccessible`.

Here the universe of sets `V` is `ZFSet.{u}` and ordinals are `Ordinal.{u}`, identified with
von Neumann ordinals via `Ordinal.toZFSet`.

Source: Bagaria–Castells–Larson, *An Ω-logic primer*, Definition 1.5.
-/

namespace OmegaLogic

universe u

open ZFSet

/-- `j : V → N` is an elementary embedding of the universe `V` into the transitive class
`N ⊆ V`: `j` maps into `N` and for every formula `φ(x₀,…,x_{k-1})` of set theory and all sets
`a₀,…,a_{k-1}`, `V ⊨ φ(a⃗)` iff `N ⊨ φ(j(a⃗))`. -/
def IsElementaryEmbedding (j : ZFSet.{u} → ZFSet.{u}) (N : Set ZFSet.{u}) : Prop :=
  (∀ x ∈ N, ∀ y ∈ x, y ∈ N) ∧ (∀ x, j x ∈ N) ∧
  ∀ (k : ℕ) (φ : setLang.Formula (Fin k)) (a : Fin k → (Set.univ : Set ZFSet.{u}))
    (b : Fin k → N), (∀ i, (b i).1 = j (a i).1) → (φ.Realize a ↔ φ.Realize b)

/-- `κ` is the critical point of `j`: `j` fixes every ordinal below `κ` and moves `κ`. -/
def IsCriticalPoint (j : ZFSet.{u} → ZFSet.{u}) (κ : Ordinal.{u}) : Prop :=
  (∀ β < κ, j β.toZFSet = β.toZFSet) ∧ j κ.toZFSet ≠ κ.toZFSet

/-- **Woodin cardinal** (primer, Definition 1.5): `δ` is a cardinal and for every function
`f : δ → δ` there is `κ < δ` with `f[κ] ⊆ κ` and an elementary embedding `j : V → N` with
critical point `κ` such that `V_{j(f)(κ)} ⊆ N`. -/
def IsWoodin (δ : Ordinal.{u}) : Prop :=
  δ.card.ord = δ ∧
  ∀ f : ZFSet.{u}, IsFunc δ.toZFSet δ.toZFSet f →
    ∃ κ < δ, (∀ β < κ, ∀ y, pair β.toZFSet y ∈ f → y ∈ κ.toZFSet) ∧
      ∃ (j : ZFSet.{u} → ZFSet.{u}) (N : Set ZFSet.{u}),
        IsElementaryEmbedding j N ∧ IsCriticalPoint j κ ∧
        ∃ y, pair κ.toZFSet y ∈ j f ∧ ∀ x : ZFSet.{u}, x.rank < y.rank → x ∈ N

/-- There is a proper class of Woodin cardinals. -/
def ProperClassWoodin : Prop := ∀ γ : Ordinal.{u}, ∃ δ, γ < δ ∧ IsWoodin δ

/-- There is a proper class of strongly inaccessible cardinals. -/
def ProperClassInaccessible : Prop :=
  ∀ γ : Ordinal.{u}, ∃ κ : Cardinal.{u}, γ < κ.ord ∧ κ.IsInaccessible

end OmegaLogic


