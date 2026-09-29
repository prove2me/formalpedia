-- Prove2me | Definitions.Def_ModularCurve_ComponentGroupHecke
-- name    : ModularCurve_ComponentGroupHecke
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/d06f1a4b-e535-5fa0-af8f-4b4ae2b419cd
-- title:
--   Hecke action on divisors, character lattice and component group
-- statement:
--   Fix a finite index set $\iota$. A matrix $B \in \mathrm{M}_\iota(\mathbb{Z})$ acts on divisors $\mathbb{Z}^\iota$ by `heckeDivisorAction B`, the $\mathbb{Z}$-linear map whose $j$-th coordinate is $D \mapsto \sum_{i} B_{ij} D_i$ (so by the transpose of $B$). Three predicates on such a matrix are introduced as abbreviations: `HeckeRowSums B n` says that every row sum of $B$ equals the integer $n$, i.e. $\sum_j B_{ij} = n$ for all $i$; `HeckeWeightSymm e B`, for a weight function $e : \iota \to \mathbb{N}$, says that $e_j B_{ij} = e_i B_{ji}$ for all $i,j$; and `HeckeOffDiagDivides e B` says that $e_i \mid B_{ij}$ whenever $i \neq j$. Under `HeckeRowSums B n` the degree map $D \mapsto \sum_x D_x$ satisfies $\deg(B\cdot D) = n \deg D$, so the action preserves the character lattice $X = \ker(\deg)$; `heckeCharacterAction B h` is the resulting endomorphism of $X$. Under `HeckeWeightSymm e B` the action is self-adjoint for the weighted pairing $\langle D, D'\rangle_e = \sum_x e_x D_x D'_x$, and consequently the Gram map $\mathrm{gram}_e : X \to X^\vee = \operatorname{Hom}_{\mathbb{Z}}(X,\mathbb{Z})$, $D \mapsto \langle D, -\rangle_e$, is equivariant: $\mathrm{gram}_e(B\cdot D) = (B\cdot)^\vee(\mathrm{gram}_e D)$. Hence the image of $\mathrm{gram}_e$ is carried into itself by the dual map, and `heckeComponentAction e B h hsym` is the induced endomorphism of the component group $\Phi_e = X^\vee / \operatorname{im}(\mathrm{gram}_e)$. The accompanying lemmas record the coordinate formula for the divisor action, the compatibility of the character-lattice action with its underlying map on $\mathbb{Z}^\iota$, the submodule inclusion just described, and the fact that the quotient projection $X^\vee \to \Phi_e$ intertwines the dual action with the action on $\Phi_e$.
--
--   **Relation to Mathlib.** Mathlib has no notion of the component group of a Néron model or of a Hecke action on it; this is the project's own combinatorial model, built from Mathlib's `Matrix`, `Module.Dual` and quotients of modules.
--
--   **Where it is used.** This equips the project's combinatorial presentation of the component group, given by the exact sequence $0 \to X \to X^\vee \to \Phi \to 0$ attached to a weighted intersection matrix, with the action of a single Hecke correspondence recorded as an integer matrix. Such equivariance, together with the off-diagonal divisibility condition, is what is needed for the component-group input to Mazur's principle and hence to level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ComponentGroupHecke.lean

import Definitions.Def_ModularCurve_ComponentGroup
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Finset

section DivisorAction
variable {ι : Type*} [Fintype ι]

def heckeDivisorAction (B : Matrix ι ι ℤ) : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) :=
  LinearMap.pi fun j => ∑ i : ι, B i j • LinearMap.proj i

@[simp] theorem heckeDivisorAction_apply (B : Matrix ι ι ℤ) (D : ι → ℤ) (j : ι) :
    heckeDivisorAction B D j = ∑ i : ι, B i j * D i := by
  simp [heckeDivisorAction, LinearMap.pi_apply, LinearMap.sum_apply]

abbrev HeckeRowSums (B : Matrix ι ι ℤ) (n : ℤ) : Prop :=
  ∀ i : ι, ∑ j : ι, B i j = n

abbrev HeckeWeightSymm (e : ι → ℕ) (B : Matrix ι ι ℤ) : Prop :=
  ∀ i j : ι, (e j : ℤ) * B i j = (e i : ℤ) * B j i

abbrev HeckeOffDiagDivides (e : ι → ℕ) (B : Matrix ι ι ℤ) : Prop :=
  ∀ i j : ι, i ≠ j → (e i : ℤ) ∣ B i j

theorem degreeOn_heckeDivisorAction {B : Matrix ι ι ℤ} {n : ℤ} (h : HeckeRowSums B n)
    (D : ι → ℤ) : degreeOn ι (heckeDivisorAction B D) = n * degreeOn ι D := by
  simp only [degreeOn_apply, heckeDivisorAction_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, h i]

theorem heckeDivisorAction_mem_characterLattice {B : Matrix ι ι ℤ} {n : ℤ}
    (h : HeckeRowSums B n) {D : ι → ℤ} (hD : D ∈ characterLattice ι) :
    heckeDivisorAction B D ∈ characterLattice ι := by
  rw [mem_characterLattice] at hD ⊢
  have := degreeOn_heckeDivisorAction h D
  rw [degreeOn_apply, degreeOn_apply, hD, mul_zero] at this
  exact this

def heckeCharacterAction (B : Matrix ι ι ℤ) {n : ℤ} (h : HeckeRowSums B n) :
    characterLattice ι →ₗ[ℤ] characterLattice ι :=
  (heckeDivisorAction B).restrict fun _ hD => heckeDivisorAction_mem_characterLattice h hD

@[simp] theorem heckeCharacterAction_coe (B : Matrix ι ι ℤ) {n : ℤ} (h : HeckeRowSums B n)
    (D : characterLattice ι) :
    (heckeCharacterAction B h D : ι → ℤ) = heckeDivisorAction B D.1 :=
  rfl

end DivisorAction

section Equivariance
variable {ι : Type*} [Fintype ι]

theorem widthPairing_heckeDivisorAction {e : ι → ℕ} {B : Matrix ι ι ℤ}
    (hsym : HeckeWeightSymm e B) (D D' : ι → ℤ) :
    widthPairing e (heckeDivisorAction B D) D' =
      widthPairing e D (heckeDivisorAction B D') := by
  simp only [widthPairing_apply, heckeDivisorAction_apply]
  have lhs_eq : ∀ j : ι, (e j : ℤ) * ((∑ i : ι, B i j * D i) * D' j) =
      ∑ i : ι, (e j : ℤ) * B i j * (D i * D' j) := fun j => by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have rhs_eq : ∀ i : ι, (e i : ℤ) * (D i * ∑ j : ι, B j i * D' j) =
      ∑ j : ι, (e i : ℤ) * B j i * (D i * D' j) := fun i => by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [lhs_eq, rhs_eq]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    linear_combination (D i * D' j) * hsym i j

theorem gramMap_heckeCharacterAction {e : ι → ℕ} {B : Matrix ι ι ℤ} {n : ℤ}
    (h : HeckeRowSums B n) (hsym : HeckeWeightSymm e B) (D : characterLattice ι) :
    gramMap e (heckeCharacterAction B h D) =
      (heckeCharacterAction B h).dualMap (gramMap e D) := by
  apply LinearMap.ext
  intro D'
  rw [LinearMap.dualMap_apply']
  show widthPairing e (heckeCharacterAction B h D : ι → ℤ) D'.1 =
    widthPairing e D.1 (heckeCharacterAction B h D' : ι → ℤ)
  rw [heckeCharacterAction_coe, heckeCharacterAction_coe]
  exact widthPairing_heckeDivisorAction hsym D.1 D'.1

theorem range_gramMap_le_comap_dualMap {e : ι → ℕ} {B : Matrix ι ι ℤ} {n : ℤ}
    (h : HeckeRowSums B n) (hsym : HeckeWeightSymm e B) :
    LinearMap.range (gramMap e) ≤
      Submodule.comap (heckeCharacterAction B h).dualMap (LinearMap.range (gramMap e)) := by
  rintro _ ⟨D, rfl⟩
  exact ⟨heckeCharacterAction B h D, gramMap_heckeCharacterAction h hsym D⟩

def heckeComponentAction (e : ι → ℕ) (B : Matrix ι ι ℤ) {n : ℤ} (h : HeckeRowSums B n)
    (hsym : HeckeWeightSymm e B) : componentGroup e →ₗ[ℤ] componentGroup e :=
  Submodule.mapQ _ _ (heckeCharacterAction B h).dualMap
    (range_gramMap_le_comap_dualMap h hsym)

@[simp] theorem componentGroupProj_heckeComponentAction {e : ι → ℕ} {B : Matrix ι ι ℤ} {n : ℤ}
    (h : HeckeRowSums B n) (hsym : HeckeWeightSymm e B)
    (φ : Module.Dual ℤ (characterLattice ι)) :
    heckeComponentAction e B h hsym (componentGroupProj e φ) =
      componentGroupProj e ((heckeCharacterAction B h).dualMap φ) :=
  rfl

end Equivariance

end ModularCurve


