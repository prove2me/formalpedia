-- Prove2me | Definitions.Def_UltimateL_InnerModel
-- name    : UltimateL_InnerModel
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T21:24:27.054565+00:00
-- url     : https://prove2.me/theorems/031a7c1e-8a18-41fe-a1b1-c58cccbc5f27
-- title:
--   Inner models and weak extender models (Woodin, Definition 3.5)
-- statement:
--   A class $N$ of sets is a **transitive class model of ZFC** when it is transitive and, with the true membership relation, satisfies the ZFC axioms expressed as closure properties: pairing, union, power set as computed in $N$, infinity, the separation and collection schemas for every first-order formula with parameters from $N$, and choice. Extensionality and foundation are automatic for a transitive class. An **inner model** is such a class that additionally contains every ordinal. Following Woodin's Definition 3.5, $N$ is a **weak extender model for the supercompactness of $\delta$** if it is a transitive class model of ZFC and for every $\gamma>\delta$ there is a $\delta$-complete normal fine measure $U$ on $P_\delta(\gamma)$ such that $N\cap P_\delta(\gamma)\in U$ and $U\cap N\in N$. These two conditions are what make a weak extender model 'close to $V$'.
-- source:
--   W. Hugh Woodin, In Search of Ultimate-L, BSL 23(1) (2017) 1-109, doi:10.1017/bsl.2016.34, Definition 3.5 (weak extender model), p. 8; the closure-property presentation of ZFC for a transitive class follows the platform's OmegaLogic.IsZFCModel.

import Mathlib
import Definitions.Def_UltimateL_Ultrafilter
import Definitions.Def_OmegaLogic_Semantics

namespace UltimateL

universe u

open ZFSet OmegaLogic

/-- `N` is a transitive class model of ZFC for the true membership relation: closure under
pairing, union, power set (as computed in `N`), infinity, the separation and collection schemas
for every formula with parameters from `N`, and choice. Extensionality and foundation hold
automatically for a transitive class with the true membership. -/
def IsTransitiveZFCClass (N : Set ZFSet.{u}) : Prop :=
  (∀ x ∈ N, ∀ y ∈ x, y ∈ N) ∧
  (∀ x ∈ N, ∀ y ∈ N, ({x, y} : ZFSet) ∈ N) ∧
  (∀ x ∈ N, ⋃₀ x ∈ N) ∧
  (∀ x ∈ N, ZFSet.sep (· ∈ N) (ZFSet.powerset x) ∈ N) ∧
  ZFSet.omega ∈ N ∧
  (∀ (k : ℕ) (φ : setLang.Formula (Fin (k + 1))) (p : Fin k → N), ∀ a ∈ N,
    ZFSet.sep (fun x => ∃ hx : x ∈ N, φ.Realize (Fin.cons (⟨x, hx⟩ : N) p)) a ∈ N) ∧
  (∀ (k : ℕ) (φ : setLang.Formula (Fin (k + 2))) (p : Fin k → N), ∀ a ∈ N,
    (∀ (x : N), x.1 ∈ a → ∃ y : N, φ.Realize (Fin.cons x (Fin.cons y p))) →
    ∃ b ∈ N, ∀ (x : N), x.1 ∈ a →
      ∃ y : N, y.1 ∈ b ∧ φ.Realize (Fin.cons x (Fin.cons y p))) ∧
  (∀ x ∈ N, (∀ y ∈ x, y ≠ ∅) → (∀ y ∈ x, ∀ z ∈ x, y ≠ z → ∀ w ∈ y, w ∉ z) →
    ∃ c ∈ N, ∀ y ∈ x, ∃! w, w ∈ c ∧ w ∈ y)

/-- `N` is an inner model: a transitive class model of ZFC containing every ordinal. -/
def IsInnerModel (N : Set ZFSet.{u}) : Prop :=
  IsTransitiveZFCClass N ∧ ∀ α : Ordinal.{u}, α.toZFSet ∈ N

/-- `N` is a weak extender model for the supercompactness of `δ` (Woodin, Definition 3.5):
a transitive class model of ZFC such that for every `γ > δ` there is a `δ`-complete normal fine
measure `U` on `P_δ(γ)` with `N ∩ P_δ(γ) ∈ U` and `U ∩ N ∈ N`. -/
def IsWeakExtenderModel (N : Set ZFSet.{u}) (δ : Ordinal.{u}) : Prop :=
  IsTransitiveZFCClass N ∧
  ∀ γ > δ, ∃ U : ZFSet.{u},
    IsUltrafilterOn U (pSmall δ γ) ∧ IsComplete U δ ∧ IsFine U δ γ ∧ IsNormal U δ γ ∧
    ZFSet.sep (· ∈ N) (pSmall δ γ) ∈ U ∧
    ZFSet.sep (· ∈ N) U ∈ N

end UltimateL


