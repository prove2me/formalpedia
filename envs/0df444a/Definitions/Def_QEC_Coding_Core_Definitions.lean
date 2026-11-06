-- Prove2me | Definitions.Def_QEC_Coding_Core_Definitions
-- name    : QEC_Coding_Core_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:04:54.575824+00:00
-- url     : https://prove2.me/theorems/66c45221-3a08-4812-9808-5d76b86cd88c
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean

import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC
namespace Coding
universe u v w x
abbrev Word (F : Type u) (ι : Type v) := ι → F
noncomputable def canonicalBasisWord
    {F : Type u} {ι : Type v} [Zero F] [One F] (i : ι) : Word F ι := by
  classical
  exact Pi.single i 1
def wordPairing {F : Type u} {ι : Type v} [Field F] [Fintype ι] :
    LinearMap.BilinForm F (Word F ι) where
  toFun x :=
    { toFun := fun y => dotProduct x y
      map_add' := by
        intro y z
        exact dotProduct_add x y z
      map_smul' := by
        intro a y
        exact dotProduct_smul a x y }
  map_add' := by
    intro x y
    ext z
    exact add_dotProduct x y z
  map_smul' := by
    intro a x
    ext y
    exact smul_dotProduct a x y
@[simp]
theorem wordPairing_apply {F : Type u} {ι : Type v} [Field F] [Fintype ι]
    (x y : Word F ι) :
    wordPairing (F := F) (ι := ι) x y = dotProduct x y :=
  rfl
theorem wordPairing_nondegenerate {F : Type u} {ι : Type v} [Field F] [Fintype ι] :
    (wordPairing (F := F) (ι := ι)).Nondegenerate := by
  constructor
  · intro x hx
    exact dotProduct_eq_zero_iff.mp (fun y => by simpa [wordPairing_apply] using hx y)
  · intro y hy
    exact dotProduct_eq_zero_iff.mp (fun x => by
      rw [dotProduct_comm]
      simpa [wordPairing_apply] using hy x)
theorem word_eq_sum_single {F : Type u} {ι : Type v} [Field F] [Fintype ι]
    [DecidableEq ι] (x : Word F ι) :
    (Finset.univ.sum fun i : ι => Pi.single i (x i) : Word F ι) = x :=
  LinearMap.sum_single_apply (fun _ : ι => F) x
noncomputable def wordLinearMapTranspose
    {F : Type u} {ι : Type v} {κ : Type w} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ]
    (A : Word F ι →ₗ[F] Word F κ) : Word F κ →ₗ[F] Word F ι := by
  classical
  exact
    { toFun := fun y i =>
        Finset.univ.sum fun k : κ => y k * A (Pi.single i (1 : F) : Word F ι) k
      map_add' := by
        intro y z
        ext i
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a y
        ext i
        simp [Finset.mul_sum, mul_assoc] }
theorem wordPairing_wordLinearMapTranspose
    {F : Type u} {ι : Type v} {κ : Type w} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ]
    (A : Word F ι →ₗ[F] Word F κ) (y : Word F κ) (x : Word F ι) :
    wordPairing (F := F) (ι := ι) (wordLinearMapTranspose A y) x =
      wordPairing (F := F) (ι := κ) y (A x) := by
  classical
  have hA :
      A x = Finset.univ.sum fun i : ι => x i • A (Pi.single i (1 : F) : Word F ι) := by
    calc
      A x = A (Finset.univ.sum fun i : ι =>
          (Pi.single i (x i) : Word F ι)) := by
        rw [word_eq_sum_single (F := F) x]
      _ = Finset.univ.sum fun i : ι =>
          A (Pi.single i (x i) : Word F ι) := by
        rw [map_sum]
      _ = Finset.univ.sum fun i : ι => x i • A (Pi.single i (1 : F) : Word F ι) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← map_smul]
        congr 1
        rw [← Pi.single_smul]
        simp
  have hA_apply (k : κ) :
      A x k = Finset.univ.sum fun i : ι =>
        x i * A (Pi.single i (1 : F) : Word F ι) k := by
    rw [hA]
    simp [Pi.smul_apply]
  calc
    wordPairing (F := F) (ι := ι) (wordLinearMapTranspose A y) x
        = Finset.univ.sum fun i : ι =>
            (Finset.univ.sum fun k : κ =>
              y k * A (Pi.single i (1 : F) : Word F ι) k) * x i := by
          simp [wordPairing_apply, wordLinearMapTranspose, dotProduct]
    _ = Finset.univ.sum fun i : ι =>
          Finset.univ.sum fun k : κ =>
            (y k * A (Pi.single i (1 : F) : Word F ι) k) * x i := by
          simp [Finset.sum_mul]
    _ = Finset.univ.sum fun k : κ =>
          Finset.univ.sum fun i : ι =>
            (y k * A (Pi.single i (1 : F) : Word F ι) k) * x i := by
          rw [Finset.sum_comm]
    _ = Finset.univ.sum fun k : κ =>
          y k * (Finset.univ.sum fun i : ι =>
            x i * A (Pi.single i (1 : F) : Word F ι) k) := by
          apply Finset.sum_congr rfl
          intro k _
          simp [Finset.mul_sum, mul_left_comm, mul_comm]
    _ = Finset.univ.sum fun k : κ => y k * A x k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← hA_apply k]
    _ = wordPairing (F := F) (ι := κ) y (A x) := by
          simp [wordPairing_apply, dotProduct]
structure LinearCode (F : Type u) (ι : Type v) [Field F] [Fintype F] [Fintype ι] where
  carrier : Submodule F (Word F ι)
namespace LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
instance : Coe (LinearCode F ι) (Submodule F (Word F ι)) where
  coe C := C.carrier
def dual (C : LinearCode F ι) : LinearCode F ι where
  carrier := (LinearMap.BilinForm.flipHom (wordPairing (F := F) (ι := ι))).orthogonal C.carrier
@[simp]
theorem dual_carrier (C : LinearCode F ι) :
    (C.dual).carrier =
      (LinearMap.BilinForm.flipHom (wordPairing (F := F) (ι := ι))).orthogonal C.carrier :=
  rfl
theorem mem_dual (C : LinearCode F ι) (x : Word F ι) :
    x ∈ C.dual.carrier ↔
      ∀ c : Word F ι, c ∈ C.carrier → wordPairing (F := F) (ι := ι) x c = 0 := by
  simp [dual, LinearMap.BilinForm.isOrtho_def, LinearMap.BilinForm.flip_apply]
theorem orthogonal_of_mem_dual (C : LinearCode F ι) {x c : Word F ι}
    (hx : x ∈ C.dual.carrier) (hc : c ∈ C.carrier) :
    wordPairing (F := F) (ι := ι) x c = 0 :=
  (C.mem_dual x).1 hx c hc
theorem dual_orthogonal (C : LinearCode F ι) {c x : Word F ι}
    (hc : c ∈ C.carrier) (hx : x ∈ C.dual.carrier) :
    wordPairing (F := F) (ι := ι) c x = 0 := by
  rw [wordPairing_apply, dotProduct_comm]
  exact C.orthogonal_of_mem_dual hx hc
theorem le_dual_of_le_dual (C D : LinearCode F ι)
    (h : D.carrier ≤ C.dual.carrier) :
    C.carrier ≤ D.dual.carrier := by
  intro c hc
  refine (D.mem_dual c).2 ?_
  intro d hd
  exact C.dual_orthogonal hc (h hd)
end LinearCode
def hammingSupport {F : Type u} {ι : Type v} [Zero F] [DecidableEq F] [Fintype ι]
    (x : Word F ι) : Finset ι :=
  Finset.univ.filter fun i => x i ≠ 0
def HammingWeight {F : Type u} {ι : Type v} [Zero F] [DecidableEq F] [Fintype ι]
    (x : Word F ι) : Nat :=
  (hammingSupport x).card
@[simp]
theorem HammingWeight_eq_card_hammingSupport {F : Type u} {ι : Type v} [Zero F]
    [DecidableEq F] [Fintype ι] (x : Word F ι) :
    HammingWeight x = (hammingSupport x).card :=
  rfl
@[simp]
theorem hammingSupport_zero {F : Type u} {ι : Type v} [Zero F] [DecidableEq F]
    [Fintype ι] :
    hammingSupport (0 : Word F ι) = ∅ := by
  ext i
  simp [hammingSupport]
@[simp]
theorem HammingWeight_zero {F : Type u} {ι : Type v} [Zero F] [DecidableEq F]
    [Fintype ι] :
    HammingWeight (0 : Word F ι) = 0 := by
  simp [HammingWeight]
@[simp]
theorem HammingWeight_eq_zero_iff {F : Type u} {ι : Type v} [Zero F]
    [DecidableEq F] [Fintype ι] (x : Word F ι) :
    HammingWeight x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    by_contra hxi
    have hxi0 : x i ≠ 0 := by
      simpa using hxi
    have hi : i ∈ hammingSupport x := by
      simp [hammingSupport, hxi0]
    have hcard : (hammingSupport x).card = 0 := by
      simpa [HammingWeight] using hx
    have hempty : hammingSupport x = ∅ := Finset.card_eq_zero.mp hcard
    have hnot : i ∉ hammingSupport x := by
      simp [hempty]
    exact hnot hi
  · intro hx
    rw [hx]
    exact HammingWeight_zero
def Length (_F : Type u) (ι : Type v) [Fintype ι] : Nat :=
  Fintype.card ι
@[simp]
theorem finrank_word_eq_length {F : Type u} {ι : Type v} [Field F] [Fintype ι] :
    Module.finrank F (Word F ι) = Length F ι := by
  rw [Length, Module.finrank_fintype_fun_eq_card]
noncomputable def Dimension {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [Fintype ι] (C : LinearCode F ι) : Nat :=
  Module.finrank F C.carrier
@[simp]
theorem Dimension_eq_finrank_carrier {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [Fintype ι] (C : LinearCode F ι) :
    Dimension C = Module.finrank F C.carrier :=
  rfl
namespace LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
end LinearCode
def MinimumDistance {F : Type u} {ι : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] (C : LinearCode F ι) (d : Nat) : Prop :=
  ∃ x : Word F ι,
    x ∈ C.carrier ∧ x ≠ 0 ∧ HammingWeight x = d ∧
      ∀ y : Word F ι, y ∈ C.carrier → y ≠ 0 → d ≤ HammingWeight y
def RelativeMinimumDistance {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (ambient trivial : LinearCode F ι) (d : Nat) : Prop :=
  ∃ x : Word F ι,
    x ∈ ambient.carrier ∧ x ∉ trivial.carrier ∧ HammingWeight x = d ∧
      ∀ y : Word F ι,
        y ∈ ambient.carrier → y ∉ trivial.carrier → d ≤ HammingWeight y
def PureXLogicalMinimumDistance {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (xCode zCode : LinearCode F ι) (d : Nat) : Prop :=
  RelativeMinimumDistance zCode.dual xCode d
def PureZLogicalMinimumDistance {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (xCode zCode : LinearCode F ι) (d : Nat) : Prop :=
  RelativeMinimumDistance xCode.dual zCode d
def AlgebraicCSSMinimumDistance {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (xCode zCode : LinearCode F ι) (d : Nat) : Prop :=
  ∃ x : Word F ι,
    ((x ∈ zCode.dual.carrier ∧ x ∉ xCode.carrier) ∨
      (x ∈ xCode.dual.carrier ∧ x ∉ zCode.carrier)) ∧
    HammingWeight x = d ∧
      ∀ y : Word F ι,
        ((y ∈ zCode.dual.carrier ∧ y ∉ xCode.carrier) ∨
          (y ∈ xCode.dual.carrier ∧ y ∉ zCode.carrier)) →
        d ≤ HammingWeight y
structure CodeParameters (F : Type u) (ι : Type v) [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] where
  code : LinearCode F ι
  length : Nat
  dimension : Nat
  minimumDistance : Nat
  length_eq : length = Length F ι
  dimension_eq : dimension = Dimension code
  distance_spec : MinimumDistance code minimumDistance
structure SymplecticVector (F : Type u) (ι : Type v) [Field F] [Fintype F]
    [Fintype ι] where
  xPart : Word F ι
  zPart : Word F ι
def symplecticForm {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
    (a b : SymplecticVector F ι) : F :=
  Finset.sum Finset.univ (fun i : ι => a.xPart i * b.zPart i - a.zPart i * b.xPart i)
def SymplecticOrthogonal {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [Fintype ι] (S : Set (SymplecticVector F ι)) (v : SymplecticVector F ι) :
    Prop :=
  ∀ w : SymplecticVector F ι, w ∈ S → symplecticForm v w = 0
namespace LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
end LinearCode
structure PauliSymplectic (F : Type u) (ι : Type v) [Field F] [Fintype F]
    [Fintype ι] where
  phase : F
  vector : SymplecticVector F ι
namespace PauliSymplectic
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
def Commutes (P Q : PauliSymplectic F ι) : Prop :=
  symplecticForm P.vector Q.vector = 0
end PauliSymplectic
structure StabilizerCode (F : Type u) (ι : Type v) (H : Type w)
    [Field F] [Fintype F] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H] where
  stabilizers : Set (PauliSymplectic F ι)
  code : Semantics.QuantumCode H
  isotropic : ∀ P : PauliSymplectic F ι, P ∈ stabilizers →
    ∀ Q : PauliSymplectic F ι, Q ∈ stabilizers → PauliSymplectic.Commutes P Q
structure CSSCode (F : Type u) (ι : Type v) (H : Type w)
    [Field F] [Fintype F] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H] where
  xCode : LinearCode F ι
  zCode : LinearCode F ι
  stabilizer : StabilizerCode F ι H
  orthogonal : ∀ x : Word F ι, x ∈ xCode.carrier →
    ∀ z : Word F ι, z ∈ zCode.carrier →
      symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector F ι)
        ({ xPart := 0, zPart := z } : SymplecticVector F ι) = 0
structure ChainComplexData (F : Type u) (C0 C1 C2 : Type x) [Field F]
    [AddCommGroup C0] [Module F C0] [AddCommGroup C1] [Module F C1]
    [AddCommGroup C2] [Module F C2] where
  boundary1 : C1 →ₗ[F] C0
  boundary2 : C2 →ₗ[F] C1
  boundary_squared : boundary1.comp boundary2 = 0
namespace ChainComplexData
variable {F : Type u} {ι : Type v} {C0 C2 : Type (max u v)} [Field F] [Fintype F]
    [Fintype ι] [AddCommGroup C0] [Module F C0] [AddCommGroup C2] [Module F C2]
def middleCycleCode (K : ChainComplexData F C0 (Word F ι) C2) : LinearCode F ι where
  carrier := LinearMap.ker K.boundary1
def middleBoundaryCode (K : ChainComplexData F C0 (Word F ι) C2) : LinearCode F ι where
  carrier := LinearMap.range K.boundary2
noncomputable def firstCoboundaryCheckCode {κ : Type v} [Fintype κ]
    (K : ChainComplexData F (Word F κ) (Word F ι) C2) : LinearCode F ι where
  carrier := LinearMap.range (wordLinearMapTranspose K.boundary1)
@[simp]
theorem mem_middleCycleCode_iff (K : ChainComplexData F C0 (Word F ι) C2)
    (x : Word F ι) :
    x ∈ K.middleCycleCode.carrier ↔ K.boundary1 x = 0 := by
  rfl
@[simp]
theorem mem_middleBoundaryCode_iff (K : ChainComplexData F C0 (Word F ι) C2)
    (x : Word F ι) :
    x ∈ K.middleBoundaryCode.carrier ↔ ∃ y, K.boundary2 y = x := by
  rfl
@[simp]
theorem mem_firstCoboundaryCheckCode_iff {κ : Type v} [Fintype κ]
    (K : ChainComplexData F (Word F κ) (Word F ι) C2) (x : Word F ι) :
    x ∈ K.firstCoboundaryCheckCode.carrier ↔
      ∃ y : Word F κ, wordLinearMapTranspose K.boundary1 y = x := by
  exact LinearMap.mem_range
theorem middleBoundaryCode_le_middleCycleCode
    (K : ChainComplexData F C0 (Word F ι) C2) :
    K.middleBoundaryCode.carrier ≤ K.middleCycleCode.carrier := by
  intro x hx
  rw [mem_middleCycleCode_iff]
  rcases (mem_middleBoundaryCode_iff K x).1 hx with ⟨y, hy⟩
  rw [← hy]
  change (K.boundary1.comp K.boundary2) y = 0
  rw [K.boundary_squared]
  rfl
noncomputable def middleBoundaryInCycles
    (K : ChainComplexData F C0 (Word F ι) C2) :
    Submodule F K.middleCycleCode.carrier :=
  K.middleBoundaryCode.carrier.comap K.middleCycleCode.carrier.subtype
noncomputable def middleBoundaryInCyclesEquiv
    (K : ChainComplexData F C0 (Word F ι) C2) :
    K.middleBoundaryInCycles ≃ₗ[F] K.middleBoundaryCode.carrier :=
  Submodule.comapSubtypeEquivOfLe K.middleBoundaryCode_le_middleCycleCode
noncomputable abbrev middleHomology
    (K : ChainComplexData F C0 (Word F ι) C2) :=
  K.middleCycleCode.carrier ⧸ K.middleBoundaryInCycles
@[simp]
theorem finrank_middleBoundaryInCycles_eq
    (K : ChainComplexData F C0 (Word F ι) C2) :
    Module.finrank F K.middleBoundaryInCycles = Dimension K.middleBoundaryCode := by
  rw [Dimension_eq_finrank_carrier]
  exact K.middleBoundaryInCyclesEquiv.finrank_eq
theorem firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode {κ : Type v} [Fintype κ]
    (K : ChainComplexData F (Word F κ) (Word F ι) C2) :
    K.firstCoboundaryCheckCode.dual.carrier = K.middleCycleCode.carrier := by
  ext x
  constructor
  · intro hx
    rw [mem_middleCycleCode_iff]
    have hpair : ∀ y : Word F κ, wordPairing (F := F) (ι := κ) y (K.boundary1 x) = 0 := by
      intro y
      have hmem : wordLinearMapTranspose K.boundary1 y ∈ K.firstCoboundaryCheckCode.carrier := by
        exact (mem_firstCoboundaryCheckCode_iff K (wordLinearMapTranspose K.boundary1 y)).2
          ⟨y, rfl⟩
      have hxpair := (LinearCode.mem_dual K.firstCoboundaryCheckCode x).1 hx
        (wordLinearMapTranspose K.boundary1 y) hmem
      rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply] at hxpair
      rw [wordPairing_wordLinearMapTranspose] at hxpair
      exact hxpair
    exact (wordPairing_nondegenerate (F := F) (ι := κ)).right (K.boundary1 x) hpair
  · intro hx
    refine (LinearCode.mem_dual K.firstCoboundaryCheckCode x).2 ?_
    intro c hc
    rcases (mem_firstCoboundaryCheckCode_iff K c).1 hc with ⟨y, rfl⟩
    rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply]
    rw [wordPairing_wordLinearMapTranspose]
    rw [(mem_middleCycleCode_iff K x).1 hx]
    simp
theorem middleBoundaryCode_le_firstCoboundaryCheckCode_dual {κ : Type v} [Fintype κ]
    (K : ChainComplexData F (Word F κ) (Word F ι) C2) :
    K.middleBoundaryCode.carrier ≤ K.firstCoboundaryCheckCode.dual.carrier := by
  intro z hz
  refine (LinearCode.mem_dual K.firstCoboundaryCheckCode z).2 ?_
  intro x hx
  rcases (mem_middleBoundaryCode_iff K z).1 hz with ⟨c2, hc2⟩
  rcases (mem_firstCoboundaryCheckCode_iff K x).1 hx with ⟨y, hy⟩
  rw [← hy]
  rw [wordPairing_apply, dotProduct_comm]
  change wordPairing (F := F) (ι := ι) (wordLinearMapTranspose K.boundary1 y) z = 0
  rw [wordPairing_wordLinearMapTranspose]
  rw [← hc2]
  change wordPairing (F := F) (ι := κ) y ((K.boundary1.comp K.boundary2) c2) = 0
  rw [K.boundary_squared]
  simp
noncomputable def middleCocycleCode {lambda : Type v} [Fintype lambda]
    (K : ChainComplexData F C0 (Word F ι) (Word F lambda)) : LinearCode F ι where
  carrier := LinearMap.ker (wordLinearMapTranspose K.boundary2)
@[simp]
theorem mem_middleCocycleCode_iff {lambda : Type v} [Fintype lambda]
    (K : ChainComplexData F C0 (Word F ι) (Word F lambda)) (x : Word F ι) :
    x ∈ K.middleCocycleCode.carrier ↔ wordLinearMapTranspose K.boundary2 x = 0 := by
  rfl
@[simp]
theorem mem_middleBoundaryCode_dual_iff {lambda : Type v} [Fintype lambda]
    (K : ChainComplexData F C0 (Word F ι) (Word F lambda)) (x : Word F ι) :
    x ∈ K.middleBoundaryCode.dual.carrier ↔
      wordLinearMapTranspose K.boundary2 x = 0 := by
  constructor
  · intro hx
    apply (wordPairing_nondegenerate (F := F) (ι := lambda)).left
    intro y
    rw [wordPairing_wordLinearMapTranspose]
    exact (LinearCode.mem_dual K.middleBoundaryCode x).1 hx
      (K.boundary2 y) ((K.mem_middleBoundaryCode_iff (K.boundary2 y)).2 ⟨y, rfl⟩)
  · intro hx
    refine (LinearCode.mem_dual K.middleBoundaryCode x).2 ?_
    intro c hc
    rcases (K.mem_middleBoundaryCode_iff c).1 hc with ⟨y, rfl⟩
    rw [← wordPairing_wordLinearMapTranspose K.boundary2 x y, hx]
    simp
theorem middleBoundaryCode_dual_carrier_eq_middleCocycleCode {lambda : Type v}
    [Fintype lambda]
    (K : ChainComplexData F C0 (Word F ι) (Word F lambda)) :
    K.middleBoundaryCode.dual.carrier = K.middleCocycleCode.carrier := by
  ext x
  rw [K.mem_middleBoundaryCode_dual_iff, K.mem_middleCocycleCode_iff]
theorem firstCoboundaryCheckCode_le_middleBoundaryCode_dual {κ : Type v} [Fintype κ]
    (K : ChainComplexData F (Word F κ) (Word F ι) C2) :
    K.firstCoboundaryCheckCode.carrier ≤ K.middleBoundaryCode.dual.carrier :=
  LinearCode.le_dual_of_le_dual K.firstCoboundaryCheckCode K.middleBoundaryCode
    K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual
noncomputable def middleCoboundaryInCocycles {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    Submodule F K.middleCocycleCode.carrier :=
  K.firstCoboundaryCheckCode.carrier.comap K.middleCocycleCode.carrier.subtype
theorem firstCoboundaryCheckCode_le_middleCocycleCode {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.firstCoboundaryCheckCode.carrier ≤ K.middleCocycleCode.carrier := by
  rw [← K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
  exact K.firstCoboundaryCheckCode_le_middleBoundaryCode_dual
noncomputable def middleCoboundaryInCocyclesEquiv {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.middleCoboundaryInCocycles ≃ₗ[F] K.firstCoboundaryCheckCode.carrier :=
  Submodule.comapSubtypeEquivOfLe K.firstCoboundaryCheckCode_le_middleCocycleCode
noncomputable abbrev middleCohomology {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :=
  K.middleCocycleCode.carrier ⧸ K.middleCoboundaryInCocycles
noncomputable def firstCoboundaryInMiddleBoundaryDual {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    Submodule F K.middleBoundaryCode.dual.carrier :=
  K.firstCoboundaryCheckCode.carrier.comap K.middleBoundaryCode.dual.carrier.subtype
noncomputable def firstCoboundaryInMiddleBoundaryDualEquiv {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.firstCoboundaryInMiddleBoundaryDual ≃ₗ[F] K.firstCoboundaryCheckCode.carrier :=
  Submodule.comapSubtypeEquivOfLe K.firstCoboundaryCheckCode_le_middleBoundaryCode_dual
noncomputable abbrev pureXLogicalQuotient {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :=
  K.middleBoundaryCode.dual.carrier ⧸ K.firstCoboundaryInMiddleBoundaryDual
noncomputable def middleBoundaryInFirstCoboundaryDual {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    Submodule F K.firstCoboundaryCheckCode.dual.carrier :=
  K.middleBoundaryCode.carrier.comap K.firstCoboundaryCheckCode.dual.carrier.subtype
noncomputable def middleBoundaryInFirstCoboundaryDualEquiv {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.middleBoundaryInFirstCoboundaryDual ≃ₗ[F] K.middleBoundaryCode.carrier :=
  Submodule.comapSubtypeEquivOfLe K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual
noncomputable abbrev pureZLogicalQuotient {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :=
  K.firstCoboundaryCheckCode.dual.carrier ⧸ K.middleBoundaryInFirstCoboundaryDual
noncomputable def middleBoundaryDualEquivMiddleCocycleCode {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.middleBoundaryCode.dual.carrier ≃ₗ[F] K.middleCocycleCode.carrier :=
  LinearEquiv.ofEq _ _ K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode
theorem map_firstCoboundaryInMiddleBoundaryDual_eq_middleCoboundaryInCocycles
    {κ lambda : Type v} [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.firstCoboundaryInMiddleBoundaryDual.map
        K.middleBoundaryDualEquivMiddleCocycleCode.toLinearMap =
      K.middleCoboundaryInCocycles := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (y : Word F ι) ∈ K.firstCoboundaryCheckCode.carrier at hy
    change (K.middleBoundaryDualEquivMiddleCocycleCode y : Word F ι) ∈
      K.firstCoboundaryCheckCode.carrier
    simpa only [middleBoundaryDualEquivMiddleCocycleCode, LinearEquiv.coe_ofEq_apply] using hy
  · intro hx
    refine ⟨K.middleBoundaryDualEquivMiddleCocycleCode.symm x, ?_, ?_⟩
    · change (x : Word F ι) ∈ K.firstCoboundaryCheckCode.carrier at hx
      change (K.middleBoundaryDualEquivMiddleCocycleCode.symm x : Word F ι) ∈
        K.firstCoboundaryCheckCode.carrier
      simpa only [middleBoundaryDualEquivMiddleCocycleCode, LinearEquiv.ofEq_symm,
        LinearEquiv.coe_ofEq_apply] using hx
    · exact K.middleBoundaryDualEquivMiddleCocycleCode.apply_symm_apply x
noncomputable def pureXLogicalQuotientEquivMiddleCohomology {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.pureXLogicalQuotient ≃ₗ[F] K.middleCohomology :=
  Submodule.Quotient.equiv K.firstCoboundaryInMiddleBoundaryDual
    K.middleCoboundaryInCocycles K.middleBoundaryDualEquivMiddleCocycleCode
    K.map_firstCoboundaryInMiddleBoundaryDual_eq_middleCoboundaryInCocycles
@[simp]
theorem pureXLogicalQuotientEquivMiddleCohomology_mk {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda))
    (x : K.middleBoundaryCode.dual.carrier) :
    K.pureXLogicalQuotientEquivMiddleCohomology (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (K.middleBoundaryDualEquivMiddleCocycleCode x) := by
  rfl
noncomputable def firstCoboundaryDualEquivMiddleCycleCode {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.firstCoboundaryCheckCode.dual.carrier ≃ₗ[F] K.middleCycleCode.carrier :=
  LinearEquiv.ofEq _ _ K.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode
theorem map_middleBoundaryInFirstCoboundaryDual_eq_middleBoundaryInCycles
    {κ lambda : Type v} [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.middleBoundaryInFirstCoboundaryDual.map
        K.firstCoboundaryDualEquivMiddleCycleCode.toLinearMap =
      K.middleBoundaryInCycles := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (y : Word F ι) ∈ K.middleBoundaryCode.carrier at hy
    change (K.firstCoboundaryDualEquivMiddleCycleCode y : Word F ι) ∈
      K.middleBoundaryCode.carrier
    simpa only [firstCoboundaryDualEquivMiddleCycleCode, LinearEquiv.coe_ofEq_apply] using hy
  · intro hx
    refine ⟨K.firstCoboundaryDualEquivMiddleCycleCode.symm x, ?_, ?_⟩
    · change (x : Word F ι) ∈ K.middleBoundaryCode.carrier at hx
      change (K.firstCoboundaryDualEquivMiddleCycleCode.symm x : Word F ι) ∈
        K.middleBoundaryCode.carrier
      simpa only [firstCoboundaryDualEquivMiddleCycleCode, LinearEquiv.ofEq_symm,
        LinearEquiv.coe_ofEq_apply] using hx
    · exact K.firstCoboundaryDualEquivMiddleCycleCode.apply_symm_apply x
noncomputable def pureZLogicalQuotientEquivMiddleHomology {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda)) :
    K.pureZLogicalQuotient ≃ₗ[F] K.middleHomology :=
  Submodule.Quotient.equiv K.middleBoundaryInFirstCoboundaryDual K.middleBoundaryInCycles
    K.firstCoboundaryDualEquivMiddleCycleCode
    K.map_middleBoundaryInFirstCoboundaryDual_eq_middleBoundaryInCycles
end ChainComplexData
structure ChainComplexCode (F : Type u) (ι : Type v) (H : Type w)
    (C0 C1 C2 : Type x) [Field F] [Fintype F] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [AddCommGroup C0] [Module F C0] [AddCommGroup C1] [Module F C1]
    [AddCommGroup C2] [Module F C2] where
  complex : ChainComplexData F C0 C1 C2
  css : CSSCode F ι H
  cycles : LinearCode F ι
  boundaries : LinearCode F ι
  boundary_subset_cycles : ∀ word : Word F ι, word ∈ boundaries.carrier → word ∈ cycles.carrier
structure LocalityProfile where
  maxCheckWeight : Nat
  maxVariableDegree : Nat
def BoundedLocality (profile : LocalityProfile) (bound : Nat) : Prop :=
  profile.maxCheckWeight ≤ bound ∧ profile.maxVariableDegree ≤ bound
structure QLDPCProperty (F : Type u) (ι : Type v) (H : Type w)
    (C0 C1 C2 : Type x) [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [AddCommGroup C0] [Module F C0] [AddCommGroup C1] [Module F C1]
    [AddCommGroup C2] [Module F C2] where
  chainCode : ChainComplexCode F ι H C0 C1 C2
  parameters : CodeParameters F ι
  locality : LocalityProfile
  localityBound : Nat
  bounded_locality : BoundedLocality locality localityBound
structure SemanticAlgebraicBridge (F : Type u) (ι : Type v) (H K : Type w)
    [Field F] [Fintype F] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K] where
  css : CSSCode F ι H
  errors : Set (Semantics.Operator H)
  noise : Semantics.QuantumChannel H K
  recovery : Semantics.QuantumChannel K H
  knill_laflamme : Semantics.KnillLaflammeCriterion H css.stabilizer.code errors
  correctable : Semantics.Correctable H K css.stabilizer.code noise recovery
end Coding
end QEC


