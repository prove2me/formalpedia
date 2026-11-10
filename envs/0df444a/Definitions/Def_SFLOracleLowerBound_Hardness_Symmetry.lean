-- Prove2me | Definitions.Def_SFLOracleLowerBound_Hardness_Symmetry
-- name    : SFLOracleLowerBound_Hardness_Symmetry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T02:26:45.649344+00:00
-- url     : https://prove2.me/theorems/19a340a8-9000-4dea-b863-bb3e1c9adcba
-- title:
--   Finite permutation symmetry and symmetric assignment optima
-- statement:
--   A concrete finite permutation group $\Gamma$ contains the identity and is closed under composition and inverses. The orbit $\Gamma(e)$ consists of all translates of $e$. Invariant sets are unions of orbits; an invariant set function satisfies $r(\gamma S)=r(S)$. For a set $S$, its orbit-average membership vector is
--   $$
--   x_e=\frac1{|\Gamma|}\sum_{\gamma\in\Gamma}\mathbf1_{\gamma S}(e).
--   $$
--   An assignment is whole-orbit if it is constant on every orbit. The symmetric optimum is the actual minimum of the allocation cost over feasible whole-orbit assignments. A symmetric assignment instance has a valid common facility cost, invariant facility and connection costs, and $g(P_i)\le |P_i|$ for each orbit $P_i$.
--
--   These separate notions let Lemma 7 use arbitrary real submodular functions, while the allocation results retain all of Definition 9's standing assumptions.
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), §2.3, p.8; Definition 9 and equation (3), p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_Allocation

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- A finite permutation group in its concrete action, §2.3 p.8. -/
def PermutationGroup {E : Type} [Fintype E] [DecidableEq E]
    (Γ : Finset (Equiv.Perm E)) : Prop :=
  (1 : Equiv.Perm E) ∈ Γ ∧ (∀ γ ∈ Γ, γ⁻¹ ∈ Γ) ∧
    ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ ∈ Γ

def orbit {E : Type} [Fintype E] [DecidableEq E]
    (Γ : Finset (Equiv.Perm E)) (e : E) : Finset E := Γ.image (fun γ => γ e)

def orbits {E : Type} [Fintype E] [DecidableEq E]
    (Γ : Finset (Equiv.Perm E)) : Finset (Finset E) := univ.image (orbit Γ)

def InvariantSet {E : Type} [Fintype E] [DecidableEq E]
    (Γ : Finset (Equiv.Perm E)) (S : Finset E) : Prop := ∀ γ ∈ Γ, S.image γ = S

def InvariantFunction {E : Type} [Fintype E] [DecidableEq E]
    (Γ : Finset (Equiv.Perm E)) (r : Finset E → ℝ) : Prop :=
  ∀ γ ∈ Γ, ∀ S, r (S.image γ) = r S

def orbitAverage {E : Type} [Fintype E] [DecidableEq E]
    (Γ : Finset (Equiv.Perm E)) (S : Finset E) (e : E) : ℝ :=
  (∑ γ ∈ Γ, if e ∈ S.image γ then (1 : ℝ) else 0) / Γ.card

def WholeOrbit {C F : Type} [Fintype C] [DecidableEq C]
    (Γ : Finset (Equiv.Perm C)) (σ : C → F) : Prop := ∀ c, ∀ u ∈ orbit Γ c, σ u = σ c

def symmetricOptimum {C F : Type} [Fintype C] [Fintype F] [DecidableEq C] [DecidableEq F]
    (D : PublicData C F) (g : Finset C → ℝ) (Γ : Finset (Equiv.Perm C)) : ℝ≥0∞ :=
  ⨅ σ : {σ : C → F // Feasible D σ ∧ WholeOrbit Γ σ}, allocationCost D g σ.val

/-- Definition 9, p.9, including the standing orbit bound (3). -/
def SymmetricInstance {C F : Type} [Fintype C] [Fintype F] [DecidableEq C]
    (D : PublicData C F) (g : Finset C → ℝ) (Γ : Finset (Equiv.Perm C)) : Prop :=
  PermutationGroup Γ ∧ FacilityCost g ∧ InvariantFunction Γ g ∧
  (∀ γ ∈ Γ, ∀ c f, D (γ c) f = D c f) ∧ ∀ P ∈ orbits Γ, g P ≤ P.card

end SFLOracleLowerBound.Hardness


