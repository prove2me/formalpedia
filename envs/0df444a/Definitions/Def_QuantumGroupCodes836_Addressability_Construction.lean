-- Prove2me | Definitions.Def_QuantumGroupCodes836_Addressability_Construction
-- name    : QuantumGroupCodes836_Addressability_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T17:12:41.990195+00:00
-- url     : https://prove2.me/theorems/fa469a2a-dfd4-4133-bef6-f88e18330fc4
-- title:
--   Punctured CSS construction, canonical encoding and modulation
-- statement:
--   Choose full distinct orbits of the given free coordinate action and let $L$ be their union. The physical coordinates are the complement $J$, relabelled by a finite index type only after deletion. The two actual CSS subspaces are the shortened and punctured images.
--
--   $$\Lambda=sE(1_S\star\lambda\star u_L^{-1}).$$
--
--   Canonical encoding and an equivariant section are chosen only if the required mathematical objects exist; subsequent theorems establish that these options are populated. Module generators and their full restrictions are explicit. Construction outputs must agree with the original subspaces, coordinate action and logical labels, so an unrelated code or group cannot satisfy the construction predicates. Modulation is tested on every encoded state with the actual field-trace phase, for every equivariant section whose action is the shift on the remaining coordinates.
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Theorem 3.4, Lemmas 3.7–3.10 and Definition 3.9, pp.10–13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Mathlib
import Definitions.Def_QuantumGroupCodes836_Addressability_Families

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace QuantumGroupCodes836.Addressability

def reindexLinear {F I J : Type*} [Field F] (e : I ≃ J) : (I → F) ≃ₗ[F] (J → F) where
  toFun v j := v (e.symm j)
  invFun v i := v (e i)
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def remainingIndex {n : ℕ} (L : Set (Fin n)) : {j : Fin n // j ∉ L} ≃
    Fin (Nat.card {j : Fin n // j ∉ L}) := by
  classical
  exact (Fintype.equivFin _).trans (finCongr Nat.card_eq_fintype_card.symm)

/-- Both shortening and puncturing delete L before coordinates are relabelled. -/
def puncturedCSS {F : Type} [Field F] {n : ℕ} (C : Code F (Fin n)) (L : Set (Fin n)) : CSS F := by
  classical
  let e := reindexLinear (F := F) (remainingIndex L)
  refine ⟨Nat.card {j : Fin n // j ∉ L}, (shorten C L).map e.toLinearMap,
    (puncture C L).map e.toLinearMap, ?_⟩
  apply Submodule.map_mono
  exact Submodule.map_mono inf_le_left

def punctureWord {F : Type} [Field F] {n : ℕ} (C : Code F (Fin n))
    (L : Set (Fin n)) (c : C) : (puncturedCSS C L).classical := by
  classical
  refine ⟨reindexLinear (remainingIndex L) (restrictLinear Lᶜ c), ?_⟩
  exact ⟨restrictLinear Lᶜ c, ⟨c, c.2, rfl⟩, rfl⟩

def chosenOrbits {F G : Type} [Field F] [Group G] {n : ℕ} {C : Code F (Fin n)}
    (A : CodeAction F (Fin n) G C) {r : ℕ} (p : Fin r → Fin n) : Set (Fin n) :=
  {j | ∃ i, j ∈ Orbit A (p i)}

/-- All source assumptions, including the C2 correction d(Cᵖᵉʳᵖ)>r|G|. -/
def ConstructionAssumptions {F G : Type} [Field F] [Group G] [Fintype G]
    {n r : ℕ} (C : Code F (Fin n)) (A : CodeAction F (Fin n) G C)
    (p : Fin r → Fin n) (m : ℕ) (u : Fin n → F) : Prop :=
  2 ≤ m ∧ r * Fintype.card G < Module.finrank F C ∧
  MultiplicationWith C m u ∧ MultiplicationWith C 2 u ∧
  (r * Fintype.card G : ℕ∞) < distance (dual C) ∧
  (∀ i j, i ≠ j → Disjoint (Orbit A (p i)) (Orbit A (p j)))

def CanonicalEncoding {F : Type} [Field F] {n : ℕ}
    (C : Code F (Fin n)) (L : Set (Fin n))
    (E : (L → F) ≃ₗ[F] (puncturedCSS C L).Logical) : Prop :=
  ∀ c : C, E (restrictLinear L c) = (puncturedCSS C L).quotientMap (punctureWord C L c)

/-- Module section and generators are expressed on the actual punctured quotient. -/
def QuotientGenerators {F G : Type} [Field F] [Group G] [Fintype G]
    {n r : ℕ} (C : Code F (Fin n)) (A : CodeAction F (Fin n) G C)
    (p : Fin r → Fin n) : Prop :=
  let L := chosenOrbits A p
  let Q := puncturedCSS C L
  ∃ B : QuantumAction Q G, FreeQuantum B r ∧ ∃ generators : Fin r → C,
    (∀ i j g, (generators i : Fin n → F) (A.coordinates g (p j)) =
      if i = j ∧ g = 1 then 1 else 0) ∧
    ∃ basis : Module.Basis (Fin r × G) F Q.Logical,
      (∀ i g, basis (i,g) = Q.quotientMap (punctureWord C L
        ⟨permute (A.coordinates g) (generators i), A.preserves g _ (generators i).2⟩)) ∧
      (∀ i g, B.sectionMap (basis (i,g)) = punctureWord C L
        ⟨permute (A.coordinates g) (generators i), A.preserves g _ (generators i).2⟩) ∧
      (∀ g j, ((remainingIndex L).symm (B.action.coordinates g j) : Fin n) =
        A.coordinates g ((remainingIndex L).symm j))

/-- An output code is tied to the input action on both remaining and logical coordinates. -/
def ConstructionOutput {F G : Type} [Field F] [Group G] [Fintype G]
    {n r : ℕ} (C : Code F (Fin n)) (A : CodeAction F (Fin n) G C)
    (p : Fin r → Fin n) (Q : GroupCode F) : Prop :=
  let L := chosenOrbits A p
  ∃ groupIso : Q.group ≃* G,
    ∃ physicalLabels : Fin Q.code.n ≃ {j : Fin n // j ∉ L},
    ∃ logicalLabels : Fin Q.code.toCSS.logicalDimension ≃ L,
      Q.code.classical.map (reindexLinear physicalLabels).toLinearMap = puncture C L ∧
      Q.code.stabilizerX.map (reindexLinear physicalLabels).toLinearMap = shorten C L ∧
      (∀ g j, (physicalLabels (Q.physical.action.coordinates (groupIso.symm g) j) : Fin n) =
        A.coordinates g (physicalLabels j)) ∧
      (∀ g j, (logicalLabels (Q.logicalCoordinates (groupIso.symm g) j) : Fin n) =
        A.coordinates g (logicalLabels j)) ∧
      (∀ c : C, ∃ word : Q.code.classical,
        (∀ j, (word : Fin Q.code.n → F) j = (c : Fin n → F) (physicalLabels j)) ∧
        Q.code.encoding (fun j => (c : Fin n → F) (logicalLabels j)) = Q.code.toCSS.quotientMap word)

/-- Source-coordinate invariance of a union of full orbits. -/
theorem chosenOrbit_shift {F G : Type} [Field F] [Group G] {n r : ℕ}
    {C : Code F (Fin n)} (A : CodeAction F (Fin n) G C) (p : Fin r → Fin n)
    (g : G) {j : Fin n} (hj : j ∈ chosenOrbits A p) :
    A.coordinates g j ∈ chosenOrbits A p := by
  obtain ⟨i, h, hh⟩ := hj
  refine ⟨i, g * h, ?_⟩
  simp only [map_mul, Equiv.Perm.mul_apply, hh]

def logicalShift {F G : Type} [Field F] [Group G] {n r : ℕ}
    {C : Code F (Fin n)} (A : CodeAction F (Fin n) G C) (p : Fin r → Fin n)
    (g : G) : chosenOrbits A p ≃ chosenOrbits A p where
  toFun j := ⟨A.coordinates g j, chosenOrbit_shift A p g j.2⟩
  invFun j := ⟨A.coordinates g⁻¹ j, chosenOrbit_shift A p g⁻¹ j.2⟩
  left_inv j := by apply Subtype.ext; simp
  right_inv j := by apply Subtype.ext; simp

def complementShift {F G : Type} [Field F] [Group G] {n r : ℕ}
    {C : Code F (Fin n)} (A : CodeAction F (Fin n) G C) (p : Fin r → Fin n)
    (g : G) : {j : Fin n // j ∉ chosenOrbits A p} ≃ {j : Fin n // j ∉ chosenOrbits A p} where
  toFun j := ⟨A.coordinates g j, by
    intro h
    have h' := chosenOrbit_shift A p g⁻¹ h
    apply j.2
    simpa using h'⟩
  invFun j := ⟨A.coordinates g⁻¹ j, by
    intro h
    have h' := chosenOrbit_shift A p g h
    apply j.2
    simpa using h'⟩
  left_inv j := by apply Subtype.ext; simp
  right_inv j := by apply Subtype.ext; simp

def remainingShift {F G : Type} [Field F] [Group G] {n r : ℕ}
    {C : Code F (Fin n)} (A : CodeAction F (Fin n) G C) (p : Fin r → Fin n)
    (g : G) : Equiv.Perm (Fin (puncturedCSS C (chosenOrbits A p)).n) :=
  (remainingIndex (chosenOrbits A p)).symm.trans
    ((complementShift A p g).trans (remainingIndex (chosenOrbits A p)))

def canonicalEncodingOption {F : Type} [Field F] {n : ℕ}
    (C : Code F (Fin n)) (L : Set (Fin n)) :
    Option ((L → F) ≃ₗ[F] (puncturedCSS C L).Logical) :=
  if h : ∃ E, CanonicalEncoding C L E then some h.choose else none

def canonicalActionOption {F G : Type} [Field F] [Group G] {n r : ℕ}
    (C : Code F (Fin n)) (A : CodeAction F (Fin n) G C) (p : Fin r → Fin n) :
    Option (QuantumAction (puncturedCSS C (chosenOrbits A p)) G) :=
  if h : ∃ B : QuantumAction (puncturedCSS C (chosenOrbits A p)) G,
    ∀ g, B.action.coordinates g = remainingShift A p g then some h.choose else none

def tensorEncodingBy {F I : Type} [Field F] [Fintype F] [Fintype I]
    (Q : CSS F) (E : (I → F) ≃ₗ[F] Q.Logical) (b : ℕ)
    (ψ : (Fin b → I → F) → ℂ) (v : Fin b → Fin Q.n → F) : ℂ :=
  ∑ x, ψ x * ∏ j, Q.cosetState (E (x j)) (v j)

def ModulationIdentity {F G : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    [Group G] {n r : ℕ} (C : Code F (Fin n)) (A : CodeAction F (Fin n) G C)
    (p : Fin r → Fin n) (m : ℕ) (u : Fin n → F) : Prop :=
  let L := chosenOrbits A p
  let Q := puncturedCSS C L
  ∃ E, canonicalEncodingOption C L = some E ∧
    (∃ B, canonicalActionOption C A p = some B) ∧
    ∀ B : QuantumAction Q G, (∀ g, B.action.coordinates g = remainingShift A p g) →
    ∀ (S : Finset L) (weights : L → F) (σ : Fin m → G),
    (∀ a : Fin m, a.val = 0 → σ a = 1) →
    let modulation := B.sectionMap (E (fun j => if j ∈ S then weights j / u j else 0))
    ∀ ψ v,
      phase (∑ j, u ((remainingIndex L).symm j) * (modulation : Fin Q.n → F) j *
        ∏ a, v a (remainingShift A p (σ a) j)) * tensorEncodingBy Q E m ψ v =
      tensorEncodingBy Q E m
        (fun x => phase (∑ j ∈ S, weights j * ∏ a, x a (logicalShift A p (σ a) j)) * ψ x) v

end QuantumGroupCodes836.Addressability


