-- Prove2me | Definitions.Def_UltimateL_InternalUB
-- name    : UltimateL_InternalUB
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T21:40:48.982916+00:00
-- url     : https://prove2.me/theorems/75aa8bef-21e4-4cee-b17d-e6b341316c57
-- title:
--   Universally Baire sets computed inside an inner model
-- statement:
--   This file relativizes the notion of a universally Baire set to a class $N$, by coding topological spaces as sets belonging to $N$. It defines, all inside $N$: a topological space $(X,\tau)$, compactness (every open cover has a finite subcover), the Hausdorff property, the cylinders that form a basis of the Baire space $\omega^\omega$, continuity of maps into Baire space (preimages of cylinders are open), nowhere dense sets, meager sets (contained in a countable union of nowhere dense sets), and the property of Baire (differing from an open set by a meager set). Then $A$ is **universally Baire in $N$** if for every compact Hausdorff space $(X,\tau)$ in $N$ and every continuous $f:X\to\omega^\omega$ in $N$, the preimage $f^{-1}[A]$ has the property of Baire in $N$. This uses the compact-Hausdorff characterization, matching the platform's external `OmegaLogic.UniversallyBaire`; it is equivalent to Woodin's Definition 7.3 (all topological spaces) by the Feng–Magidor–Woodin theorem.
-- source:
--   W. Hugh Woodin, In Search of Ultimate-L, BSL 23(1) (2017) 1-109, doi:10.1017/bsl.2016.34, Definition 7.3 (universally Baire, Feng–Magidor–Woodin); the compact-Hausdorff characterization follows the platform's OmegaLogic.UniversallyBaire (after Bagaria–Castells–Larson, An Ω-logic primer, Proposition 2.2).

import Mathlib
import Definitions.Def_OmegaLogic_Provability

namespace UltimateL

universe u

open ZFSet OmegaLogic

/-- The set of (codes of) reals belonging to the class `N`. -/
noncomputable def realsOf (N : Set ZFSet.{u}) : ZFSet.{u} :=
  OmegaLogic.realsIn N Set.univ

/-- A set is finite in `N` if it is the surjective image of a natural number. -/
def IsFiniteIn (N : Set ZFSet.{u}) (F : ZFSet.{u}) : Prop :=
  ∃ n ∈ ZFSet.omega, ∃ g : ZFSet.{u}, g ∈ N ∧ IsFunc n F g ∧
    ∀ y ∈ F, ∃ i ∈ n, pair i y ∈ g

/-- `(X, τ)` is a topological space in `N`. -/
def IsTopologyIn (N : Set ZFSet.{u}) (X τ : ZFSet.{u}) : Prop :=
  X ∈ N ∧ τ ∈ N ∧ τ ⊆ ZFSet.powerset X ∧
  (∅ : ZFSet) ∈ τ ∧ X ∈ τ ∧
  (∀ A ∈ N, A ∈ τ → ∀ B ∈ N, B ∈ τ → A ∩ B ∈ τ) ∧
  (∀ S ∈ N, S ⊆ τ → (⋃₀ S) ∈ τ)

/-- `(X, τ)` is compact in `N`: every open cover in `N` has a finite subcover in `N`. -/
def IsCompactIn (N : Set ZFSet.{u}) (X τ : ZFSet.{u}) : Prop :=
  ∀ S ∈ N, S ⊆ τ → (⋃₀ S) = X →
    ∃ F ∈ N, F ⊆ S ∧ IsFiniteIn N F ∧ (⋃₀ F) = X

/-- `(X, τ)` is Hausdorff in `N`. -/
def IsT2In (N : Set ZFSet.{u}) (X τ : ZFSet.{u}) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
    ∃ U ∈ N, ∃ V ∈ N, U ∈ τ ∧ V ∈ τ ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅

/-- A basic open (cylinder) of the Baire space of `N`, determined by a finite sequence. -/
def IsCylinderIn (N : Set ZFSet.{u}) (C : ZFSet.{u}) : Prop :=
  ∃ (n s : ZFSet.{u}), n ∈ ZFSet.omega ∧ s ∈ N ∧ IsFunc n ZFSet.omega s ∧
    C = ZFSet.sep (fun r => ∀ i ∈ n, ∃ v, pair i v ∈ s ∧ pair i v ∈ r) (realsOf N)

/-- `f : X → ω^ω` is continuous in `N`: preimages of cylinders are open. -/
def IsContinuousToBaireIn (N : Set ZFSet.{u}) (X τ f : ZFSet.{u}) : Prop :=
  IsFunc X (realsOf N) f ∧
  ∀ C ∈ N, IsCylinderIn N C →
    ∃ U ∈ N, U ∈ τ ∧ U = ZFSet.sep (fun x => ∃ r, pair x r ∈ f ∧ r ∈ C) X

/-- `D` is nowhere dense in `(X, τ)` (in `N`). -/
def NowhereDenseIn (N : Set ZFSet.{u}) (X τ D : ZFSet.{u}) : Prop :=
  D ⊆ X ∧ ∀ U ∈ N, U ∈ τ → U ≠ ∅ →
    ∃ V ∈ N, V ∈ τ ∧ V ≠ ∅ ∧ V ⊆ U ∧ ∀ x ∈ V, x ∉ D

/-- `M` is meager in `(X, τ)` (in `N`): contained in a countable union of nowhere dense sets. -/
def MeagerIn (N : Set ZFSet.{u}) (X τ M : ZFSet.{u}) : Prop :=
  M ⊆ X ∧ ∃ S ∈ N, S ⊆ ZFSet.powerset X ∧
    (∀ D ∈ S, NowhereDenseIn N X τ D) ∧
    (∃ F ∈ N, IsFunc ZFSet.omega S F ∧ ∀ D ∈ S, ∃ n ∈ ZFSet.omega, pair n D ∈ F) ∧
    M ⊆ ⋃₀ S

/-- `A` has the property of Baire in `(X, τ)` (in `N`): it differs from an open set by a
meager set. -/
def HasBairePropertyIn (N : Set ZFSet.{u}) (X τ A : ZFSet.{u}) : Prop :=
  A ⊆ X ∧ ∃ U ∈ N, U ∈ τ ∧
    MeagerIn N X τ (ZFSet.sep (fun x => (x ∈ A ∧ x ∉ U) ∨ (x ∈ U ∧ x ∉ A)) X)

/-- `A` is universally Baire in `N` (the relativization of the platform's
`OmegaLogic.UniversallyBaire`, using the compact-Hausdorff characterization): for every compact
Hausdorff space `(X, τ)` in `N` and every continuous `f : X → ω^ω` in `N`, the preimage
`f⁻¹[A]` has the property of Baire in `N`. -/
def UniversallyBaireIn (N : Set ZFSet.{u}) (A : ZFSet.{u}) : Prop :=
  A ∈ N ∧ A ⊆ realsOf N ∧
  ∀ (X τ f : ZFSet.{u}), X ∈ N → τ ∈ N → f ∈ N →
    IsTopologyIn N X τ → IsCompactIn N X τ → IsT2In N X τ →
    IsContinuousToBaireIn N X τ f →
    HasBairePropertyIn N X τ (ZFSet.sep (fun x => ∃ r, pair x r ∈ f ∧ r ∈ A) X)

end UltimateL


