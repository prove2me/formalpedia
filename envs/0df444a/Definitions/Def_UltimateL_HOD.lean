-- Prove2me | Definitions.Def_UltimateL_HOD
-- name    : UltimateL_HOD
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T21:26:12.646678+00:00
-- url     : https://prove2.me/theorems/c15abb7f-a3a7-4b3a-9927-ad3e89a27a18
-- title:
--   Ordinal-definable and hereditarily ordinal-definable sets; the class HOD
-- statement:
--   A set $x$ is **ordinal-definable in a class $N$** if $x\in N$ and there is a first-order formula $\varphi(y,\vec p)$ with ordinal parameters $\vec p$ from $N$ such that $x$ is exactly $\{y\in N:(N,\in)\models\varphi(y,\vec p)\}$. It is **hereditarily ordinal-definable in $N$** if it and every member of its transitive closure is ordinal-definable in $N$; the class of such sets is $\mathrm{HOD}^N$. Taking $N$ to be the whole ambient universe gives the usual notions $\mathrm{OD}$, $\mathrm{HOD}$, and the class $\mathrm{HOD}$. The relativized form is needed because the axiom $V=\mathrm{Ultimate}\text{-}L$ refers to $\mathrm{HOD}^{L(A,\mathbb R)}$ computed inside inner models.
-- source:
--   W. Hugh Woodin, In Search of Ultimate-L, BSL 23(1) (2017) 1-109, doi:10.1017/bsl.2016.34; the classes OD and HOD are standard (Kanamori, The Higher Infinite, 2nd ed., Springer 2003, §13; Myhill–Scott).

import Mathlib
import Definitions.Def_OmegaLogic_Semantics

namespace UltimateL

universe u

open ZFSet OmegaLogic

/-- `x` is ordinal-definable in the class `N`: `x ∈ N` and there is a first-order formula
`φ(y, p⃗)` with ordinal parameters `p⃗` drawn from `N` such that `x` is exactly the set of
`y ∈ N` satisfying `φ` in the structure `(N, ∈)`. -/
def IsODIn (N : Set ZFSet.{u}) (x : ZFSet.{u}) : Prop :=
  x ∈ N ∧ ∃ (k : ℕ) (φ : setLang.Formula (Fin (k + 1))) (p : Fin k → N),
    (∀ i, ∃ α : Ordinal.{u}, (p i).1 = α.toZFSet) ∧
    ∀ y : N, y.1 ∈ x ↔ φ.Realize (Fin.cons y p)

/-- `x` is hereditarily ordinal-definable in `N`: `x` and every member of its transitive
closure is ordinal-definable in `N`. -/
def IsHODIn (N : Set ZFSet.{u}) (x : ZFSet.{u}) : Prop :=
  ZFSet.Hereditarily (IsODIn N) x

/-- The class `HOD^N` of sets hereditarily ordinal-definable in `N`. -/
def HODIn (N : Set ZFSet.{u}) : Set ZFSet.{u} := {x | IsHODIn N x}

/-- `x` is ordinal-definable in the ambient universe. -/
def IsOD (x : ZFSet.{u}) : Prop := IsODIn Set.univ x

/-- `x` is hereditarily ordinal-definable. -/
def IsHOD (x : ZFSet.{u}) : Prop := IsHODIn Set.univ x

/-- The class `HOD` of hereditarily ordinal-definable sets. -/
def HOD : Set ZFSet.{u} := HODIn Set.univ

end UltimateL


