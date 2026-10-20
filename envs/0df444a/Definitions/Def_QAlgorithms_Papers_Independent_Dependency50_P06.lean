-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06
-- name    : QAlgorithms_Papers_Independent_Dependency50_P06
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T13:19:09.705826+00:00
-- url     : https://prove2.me/theorems/920c8475-7c90-4d33-b6fd-62135b1c7765
-- title:
--   Definitions for Necessary and Sufficient Conditions on Measurements of Quantum Channels
-- statement:
--   The objects the formalized statements of *Necessary and Sufficient Conditions on Measurements of Quantum Channels* (arXiv:1904.09161) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `QMap`: PDF pp.1,8–10: a quantum-map candidate, including non-Hermitian inputs.
--   - `linearFromChoi`: PDF p.10, (B.1): bundle the accepted input-first Choi reconstruction as a complex-linear map. Its action on every operator is the frozen fromChoi.
--   - `IsTNI`: PDF pp.8–9: trace non-increase on normalized density matrices.
--   - `IsCPTNI`: PDF p.9: completely positive, trace non-increasing maps.
--   - `Supermap`: PDF pp.10–11: a supermap in full Choi coordinates; no positivity built in.
--   - `superApply`: PDF pp.10–11, (B.2): action on an arbitrary input map.
--   - `superChoi`: PDF p.10: supermap Choi matrix ordered A0,A1,B0,B1.
--   - `superExtend`: PDF pp.2–3: identity supermap on R tensored with S. Off-diagonal R0,R1 blocks are retained. The explicit reindexing is the only factor identification.
--   - `IsCPP`: PDF p.2, (2.1): operational complete CP preservation, before any Choi characterization. Ancillary spaces have arbitrary positive finite dimensions.
--   - `IsCPTNIPreserving`: PDF pp.2,9, (2.2): CPP and channel-to-CPTNI preservation.
--   - `IsCompletelyCPTNIPreserving`: PDF p.3, (3.1): complete CPTNI preservation, including CPP.
--   - `IsSuperchannel`: PDF pp.1,9: CPP and complete channel preservation. Neither realization nor existence of a complementary branch defines a superchannel.
--   - `superMarginal`: PDF pp.2–3,11: the supermap AB0 marginal traces B1 only, retaining B0.
--   - `testerMarginal`: PDF pp.3,12: trace A1 out of a matrix on A0,A1,B0.
--   - `linkedTester`: PDF p.12, Lemma B.1: entry expansion of Tr_R0[(sigma_R0B0 tensor I_A)((Tr_R1 J_N)^(T_R0) tensor I_B0)]. Only R0 is traced outside; the R1 marginal is taken first. The partial transpose swaps R0 indices without conjugating any entry.
--   - `IsTester`: PDF p.3, (4.2): admissible tester, allowing singular normalized rho.
--   - `singlet`: PDF pp.13–14: normalized singlet projector on A1,B0.
--   - `counterChoi`: PDF p.13: I_A0 tensor psi_minus tensor u_B1 in A0,A1,B0,B1 order. The construction permits any nonzero finite B1, as in Appendix C.
--   - `counterSupermap`: PDF pp.2,13–15: explicit counterexample on all input maps.
--   - `counterTester`: PDF p.14: violating tester, the full transpose of the B1 marginal.
--   - `pauliY`: PDF p.2, (2.4): Pauli Y in the fixed computational basis.
--   - `IsSupermeasurement`: PDF pp.2,10: supermeasurement branches are CPTNI-preserving and sum to a superchannel. Complete branch preservation remains a conclusion of the paper.
--   - `mapWithMemory`: PDF pp.4,19, (E.3): input map on A, memory on the right. All off-diagonal memory blocks are retained.
--   - `combApply`: PDF pp.4,18–19: pre/input/post circuit on every operator.
--   - `discardEffect`: PDF p.22: feed rho and discard the output. Defined on all maps, not just normalized channels.
--   - `IsDeterministicTester`: PDF pp.21–22: actual deterministic one-comb tester: prepare a density matrix with arbitrary finite memory and trace the final output. No complete normalization inequality defines physicality.
--   - `OperationalTheory`: PDF pp.20–21: primitive tests and circuit probabilities, with ordinary composition/coarse-graining axioms, rather than the conclusions of F.10. List positions label outcomes and preserve multiplicities. Hom spaces are real spans. Only independent tests are composed: conditional choice of a later test is not imposed, since that would silently restrict noncausal theories.
--   - `IsPhysical`: PDF p.21: physical events belong to allowed operational tests.
--   - `IsDeterministic`: PDF p.21: deterministic processes are singleton tests.
--   - `InStateCone`: PDF p.20: finite conical combinations of physical states. States themselves are events and may be subnormalized.
--   - `SingleUpperBound`: PDF p.24, (F.7): every deterministic input state and output effect, without selecting a preferred discard effect in a noncausal theory.
--   - `CompleteUpperBound`: PDF p.23, F.10(2): ancillary inequality, using the ambient tensor action on all candidates, without assuming local tomography.
--   - `IsCausal`: PDF p.21: the equivalent unique-deterministic-effect definition of causality. The candidate transformation is not required to be physical.
--   - `HasSeparableDeterministicStates`: PDF pp.25–26: deterministic bipartite states are finite convex combinations of product deterministic states; no claim about all cone elements.
--   - `HasSeparableDeterministicEffects`: PDF p.26: the dual finite convex combination of product deterministic effects. Unit identification is explicit after the tensor product.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, https://arxiv.org/abs/1904.09161v5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

/-!
Burniston et al., arXiv:1904.09161v5. Paper-local interfaces only.
Quantum maps are complex-linear on all matrices. A supermap is represented by
its complex-linear action on map Choi matrices, an invertible change of coordinates,
not a positivity restriction. Input factors precede output factors throughout.
Theorem 6.2 is deferred in HARD.md. Compilation is pending the batch handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P06

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)

/-- PDF pp.1,8–10: a quantum-map candidate, including non-Hermitian inputs. -/
abbrev QMap (I O : Type) := Op I →ₗ[ℂ] Op O

/-- PDF p.10, (B.1): bundle the accepted input-first Choi reconstruction
as a complex-linear map. Its action on every operator is the frozen fromChoi. -/
def linearFromChoi {I O : Type} [Fintype I] (J : Op (I × O)) : QMap I O where
  toFun := QAlgorithms.Papers.Independent.Information100.P34.fromChoi J
  map_add' X Y := by
    ext i j
    change (∑ a, ∑ b, (X a b + Y a b) * J (a, i) (b, j)) =
      (∑ a, ∑ b, X a b * J (a, i) (b, j)) +
        (∑ a, ∑ b, Y a b * J (a, i) (b, j))
    simp only [add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext i j
    change (∑ a, ∑ b, (c * X a b) * J (a, i) (b, j)) =
      c * (∑ a, ∑ b, X a b * J (a, i) (b, j))
    simp only [mul_assoc, Finset.mul_sum]

/-- PDF pp.8–9: trace non-increase on normalized density matrices. -/
def IsTNI {I O : Type} [Fintype I] [Fintype O] (E : QMap I O) : Prop :=
  ∀ X : Op I, IsDensityMatrix X → (E X).trace.re ≤ 1

/-- PDF p.9: completely positive, trace non-increasing maps. -/
def IsCPTNI {I O : Type} [Fintype I] [Fintype O] (E : QMap I O) : Prop :=
  Entanglement.IsCompletelyPositive E ∧ IsTNI E

/-- PDF pp.10–11: a supermap in full Choi coordinates; no positivity built in. -/
abbrev Supermap (A0 A1 B0 B1 : Type) := Op (A0 × A1) →ₗ[ℂ] Op (B0 × B1)

/-- PDF pp.10–11, (B.2): action on an arbitrary input map. -/
def superApply {A0 A1 B0 B1 : Type} [Fintype A0] [Fintype B0]
    (S : Supermap A0 A1 B0 B1) (E : QMap A0 A1) : QMap B0 B1 :=
  linearFromChoi (S (choi E))

/-- PDF p.10: supermap Choi matrix ordered A0,A1,B0,B1. -/
def superChoi {A0 A1 B0 B1 : Type} [Fintype A0] [Fintype A1]
    (S : Supermap A0 A1 B0 B1) : Op ((A0 × A1) × (B0 × B1)) := choi S

/-- PDF pp.2–3: identity supermap on R tensored with S. Off-diagonal R0,R1
blocks are retained. The explicit reindexing is the only factor identification. -/
def superExtend {A0 A1 B0 B1 R0 R1 : Type}
    [Fintype A0] [Fintype B0] [Fintype R0]
    (S : Supermap A0 A1 B0 B1) (N : QMap (R0 × A0) (R1 × A1)) :
    QMap (R0 × B0) (R1 × B1) :=
  linearFromChoi (fun p q =>
    S (fun a b => choi N ((p.1.1, a.1), (p.2.1, a.2))
      ((q.1.1, b.1), (q.2.1, b.2))) (p.1.2, p.2.2) (q.1.2, q.2.2))

/-- PDF p.2, (2.1): operational complete CP preservation, before any Choi
characterization. Ancillary spaces have arbitrary positive finite dimensions. -/
def IsCPP {A0 A1 B0 B1 : Type} [Fintype A0] [Fintype A1]
    [Fintype B0] [Fintype B1]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1] (S : Supermap A0 A1 B0 B1) : Prop :=
  ∀ r0 r1 : ℕ, 0 < r0 → 0 < r1 →
    ∀ N : QMap (Fin r0 × A0) (Fin r1 × A1),
      Entanglement.IsCompletelyPositive N →
        Entanglement.IsCompletelyPositive (superExtend S N)

/-- PDF pp.2,9, (2.2): CPP and channel-to-CPTNI preservation. -/
def IsCPTNIPreserving {A0 A1 B0 B1 : Type} [Fintype A0] [Fintype A1]
    [Fintype B0] [Fintype B1]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1] (S : Supermap A0 A1 B0 B1) : Prop :=
  IsCPP S ∧ ∀ N : QMap A0 A1, IsChannel N → IsCPTNI (superApply S N)

/-- PDF p.3, (3.1): complete CPTNI preservation, including CPP. -/
def IsCompletelyCPTNIPreserving {A0 A1 B0 B1 : Type} [Fintype A0] [Fintype A1]
    [Fintype B0] [Fintype B1]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1] (S : Supermap A0 A1 B0 B1) : Prop :=
  IsCPP S ∧ ∀ r0 r1 : ℕ, 0 < r0 → 0 < r1 →
    ∀ N : QMap (Fin r0 × A0) (Fin r1 × A1), IsChannel N →
      IsCPTNI (superExtend S N)

/-- PDF pp.1,9: CPP and complete channel preservation. Neither realization
nor existence of a complementary branch defines a superchannel. -/
def IsSuperchannel {A0 A1 B0 B1 : Type} [Fintype A0] [Fintype A1]
    [Fintype B0] [Fintype B1]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1] (S : Supermap A0 A1 B0 B1) : Prop :=
  IsCPP S ∧ ∀ r0 r1 : ℕ, 0 < r0 → 0 < r1 →
    ∀ N : QMap (Fin r0 × A0) (Fin r1 × A1), IsChannel N →
      IsChannel (superExtend S N)

/-- PDF pp.2–3,11: the supermap AB0 marginal traces B1 only, retaining B0. -/
def superMarginal {A0 A1 B0 B1 : Type} [Fintype B1]
    (J : Op ((A0 × A1) × (B0 × B1))) : Op ((A0 × A1) × B0) :=
  fun p q => ∑ b1, J (p.1, (p.2, b1)) (q.1, (q.2, b1))

/-- PDF pp.3,12: trace A1 out of a matrix on A0,A1,B0. -/
def testerMarginal {A0 A1 B0 : Type} [Fintype A1]
    (M : Op ((A0 × A1) × B0)) : Op (A0 × B0) :=
  fun p q => ∑ a1, M ((p.1, a1), p.2) ((q.1, a1), q.2)

/-- PDF p.12, Lemma B.1: entry expansion of
Tr_R0[(sigma_R0B0 tensor I_A)((Tr_R1 J_N)^(T_R0) tensor I_B0)].
Only R0 is traced outside; the R1 marginal is taken first. The partial
transpose swaps R0 indices without conjugating any entry. -/
def linkedTester {A0 A1 B0 R0 R1 : Type}
    [Fintype A0] [Fintype R0] [Fintype R1]
    (N : QMap (R0 × A0) (R1 × A1)) (sigma : Op (R0 × B0)) :
    Op ((A0 × A1) × B0) :=
  fun p q => ∑ r, ∑ s, sigma (r, p.2) (s, q.2) *
    ∑ t, choi N ((r, p.1.1), (t, p.1.2)) ((s, q.1.1), (t, q.1.2))

/-- PDF p.3, (4.2): admissible tester, allowing singular normalized rho. -/
def IsTester {A0 A1 B0 : Type} [Fintype A0] [Fintype A1] [Fintype B0]
    (M : Op ((A0 × A1) × B0)) : Prop :=
  M.PosSemidef ∧ ∃ rho : Op B0, IsDensityMatrix rho ∧
    testerMarginal M = Matrix.kronecker (1 : Op A0) rho

/-- PDF pp.13–14: normalized singlet projector on A1,B0. -/
def singlet : Op (Fin 2 × Fin 2) :=
  let v : Fin 2 × Fin 2 → ℂ := fun p =>
    if p = (0, 1) then (Real.sqrt 2 : ℂ)⁻¹
    else if p = (1, 0) then -(Real.sqrt 2 : ℂ)⁻¹ else 0
  fun p q => v p * conj (v q)

/-- PDF p.13: I_A0 tensor psi_minus tensor u_B1 in A0,A1,B0,B1 order.
The construction permits any nonzero finite B1, as in Appendix C. -/
def counterChoi (B1 : Type) [Fintype B1] :
    Op ((Fin 2 × Fin 2) × (Fin 2 × B1)) :=
  fun p q => (if p.1.1 = q.1.1 then 1 else 0) *
    singlet (p.1.2, p.2.1) (q.1.2, q.2.1) * mixed B1 p.2.2 q.2.2

/-- PDF pp.2,13–15: explicit counterexample on all input maps. -/
def counterSupermap (B1 : Type) [Fintype B1] : Supermap (Fin 2) (Fin 2) (Fin 2) B1 :=
  linearFromChoi (counterChoi B1)

/-- PDF p.14: violating tester, the full transpose of the B1 marginal. -/
def counterTester : Op ((Fin 2 × Fin 2) × Fin 2) :=
  (superMarginal (counterChoi (Fin 2))).transpose

/-- PDF p.2, (2.4): Pauli Y in the fixed computational basis. -/
def pauliY : Op (Fin 2) := !![0, -Complex.I; Complex.I, 0]

/-- PDF pp.2,10: supermeasurement branches are CPTNI-preserving and sum to a
superchannel. Complete branch preservation remains a conclusion of the paper. -/
def IsSupermeasurement {A0 A1 B0 B1 X : Type} [Fintype A0] [Fintype A1]
    [Fintype B0] [Fintype B1] [Fintype X]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1]
    (S : X → Supermap A0 A1 B0 B1) : Prop :=
  (∀ x, IsCPTNIPreserving (S x)) ∧ IsSuperchannel (∑ x, S x)

/-- PDF pp.4,19, (E.3): input map on A, memory on the right. All off-diagonal
memory blocks are retained. -/
def mapWithMemory {I O E : Type} (N : QMap I O) (X : Op (I × E)) : Op (O × E) :=
  fun p q => N (fun i j => X (i, p.2) (j, q.2)) p.1 q.1

/-- PDF pp.4,18–19: pre/input/post circuit on every operator. -/
def combApply {A0 A1 B0 B1 E : Type}
    (pre : QMap B0 (A0 × E)) (post : QMap (A1 × E) B1)
    (N : QMap A0 A1) (X : Op B0) : Op B1 :=
  post (mapWithMemory N (pre X))

/-- PDF p.22: feed rho and discard the output. Defined on all maps, not just
normalized channels. -/
def discardEffect {A0 A1 : Type} [Fintype A1] (rho : Op A0)
    (N : QMap A0 A1) : ℝ := (N rho).trace.re

/-- PDF pp.21–22: actual deterministic one-comb tester: prepare a density
matrix with arbitrary finite memory and trace the final output. No complete
normalization inequality defines physicality. -/
def IsDeterministicTester {A0 A1 : Type} [Fintype A0] [Fintype A1]
    (f : QMap A0 A1 → ℝ) : Prop :=
  ∃ e : ℕ, 0 < e ∧ ∃ sigma : Op (A0 × Fin e), IsDensityMatrix sigma ∧
    ∀ N : QMap A0 A1, f N = (mapWithMemory N sigma).trace.re

/-- Sanity: Choi recovery evaluates all entries, not just diagonal states. -/
example {I O : Type} [Fintype I] (J : Op (I × O)) (X : Op I) (i j : O) :
    linearFromChoi J X i j = ∑ a, ∑ b, X a b * J (a, i) (b, j) := rfl

/-- Sanity: no spurious nonzero output on the zero operator. -/
example {I O : Type} [Fintype I] (J : Op (I × O)) : linearFromChoi J 0 = 0 :=
  (linearFromChoi J).map_zero

/-- Sanity: Y_01 = -i and Y_10 = i. -/
example : pauliY 0 1 = -Complex.I ∧ pauliY 1 0 = Complex.I := by
  simp [pauliY]

section QuantumResults

variable {A0 A1 B0 B1 : Type}
variable [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
variable [hA0 : Nonempty A0] [hA1 : Nonempty A1] [hB0 : Nonempty B0] [hB1 : Nonempty B1]

end QuantumResults

/-! OPTs: real-linear symmetric monoidal process spaces with primitive allowed
tests. Morphisms are the real span of events, not automatically physical.
Finite tests suffice here: any event can be isolated from its original test by
coarse-graining the remaining outcomes. No local tomography or dimension bound. -/

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v

section OperationalDefinitions

/-- PDF pp.20–21: primitive tests and circuit probabilities, with ordinary
composition/coarse-graining axioms, rather than the conclusions of F.10.
List positions label outcomes and preserve multiplicities. Hom spaces are real spans.
Only independent tests are composed: conditional choice of a later test is not
imposed, since that would silently restrict noncausal theories. -/
structure OperationalTheory (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℝ C]
    [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalPreadditive C] [MonoidalLinear ℝ C] where
  tests : (A B : C) → Set (List (A ⟶ B))
  scalar : ((𝟙_ C) ⟶ (𝟙_ C)) ≃ₗ[ℝ] ℝ
  scalar_id : scalar (𝟙 (𝟙_ C)) = 1
  tests_nonempty : ∀ {A B} {t : List (A ⟶ B)}, t ∈ tests A B → t ≠ []
  identity_test : ∀ A, [𝟙 A] ∈ tests A A
  sequential_tests : ∀ {A B D} (t : List (A ⟶ B)) (s : List (B ⟶ D)),
    t ∈ tests A B → s ∈ tests B D →
    t.flatMap (fun f => s.map (fun g => f ≫ g)) ∈ tests A D
  parallel_tests : ∀ {A B D E} (t : List (A ⟶ B)) (s : List (D ⟶ E)),
    t ∈ tests A B → s ∈ tests D E →
    t.flatMap (fun f => s.map (fun g => f ⊗ₘ g)) ∈ tests (A ⊗ D) (B ⊗ E)
  reorder_test : ∀ {A B} {t s : List (A ⟶ B)},
    t.Perm s → t ∈ tests A B → s ∈ tests A B
  merge_test : ∀ {A B} (f g : A ⟶ B) (t : List (A ⟶ B)),
    (f :: g :: t) ∈ tests A B → ((f + g) :: t) ∈ tests A B
  left_unitor_test : ∀ A, [(λ_ A).hom] ∈ tests ((𝟙_ C) ⊗ A) A
  left_unitor_inverse_test : ∀ A, [(λ_ A).inv] ∈ tests A ((𝟙_ C) ⊗ A)
  right_unitor_test : ∀ A, [(ρ_ A).hom] ∈ tests (A ⊗ (𝟙_ C)) A
  right_unitor_inverse_test : ∀ A, [(ρ_ A).inv] ∈ tests A (A ⊗ (𝟙_ C))
  associator_test : ∀ A B D,
    [(α_ A B D).hom] ∈ tests ((A ⊗ B) ⊗ D) (A ⊗ (B ⊗ D))
  associator_inverse_test : ∀ A B D,
    [(α_ A B D).inv] ∈ tests (A ⊗ (B ⊗ D)) ((A ⊗ B) ⊗ D)
  symmetry_test : ∀ A B, [(β_ A B).hom] ∈ tests (A ⊗ B) (B ⊗ A)
  closed_test : ∀ t : List ((𝟙_ C) ⟶ (𝟙_ C)), t ∈ tests (𝟙_ C) (𝟙_ C) →
    (∀ f ∈ t, 0 ≤ scalar f) ∧ (t.map (fun f => scalar f)).sum = 1
  span_events : ∀ A B, Submodule.span ℝ
    {f : A ⟶ B | ∃ t ∈ tests A B, f ∈ t} = ⊤
  state_separation : ∀ A (rho sigma : (𝟙_ C) ⟶ A),
    (∀ d : A ⟶ (𝟙_ C), (∃ t ∈ tests A (𝟙_ C), d ∈ t) →
      scalar (rho ≫ d) = scalar (sigma ≫ d)) → rho = sigma
  process_separation : ∀ A B (f g : A ⟶ B),
    (∀ S (rho : (𝟙_ C) ⟶ (A ⊗ S)) (d : (B ⊗ S) ⟶ (𝟙_ C)),
      (∃ t ∈ tests (𝟙_ C) (A ⊗ S), rho ∈ t) →
      (∃ t ∈ tests (B ⊗ S) (𝟙_ C), d ∈ t) →
      scalar (rho ≫ (f ⊗ₘ 𝟙 S) ≫ d) = scalar (rho ≫ (g ⊗ₘ 𝟙 S) ≫ d)) → f = g

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℝ C]
variable [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear ℝ C]

/-- PDF p.21: physical events belong to allowed operational tests. -/
def IsPhysical (T : OperationalTheory C) {A B : C} (f : A ⟶ B) : Prop :=
  ∃ t ∈ T.tests A B, f ∈ t

/-- PDF p.21: deterministic processes are singleton tests. -/
def IsDeterministic (T : OperationalTheory C) {A B : C} (f : A ⟶ B) : Prop :=
  [f] ∈ T.tests A B

/-- PDF p.20: finite conical combinations of physical states. States themselves
are events and may be subnormalized. -/
def InStateCone (T : OperationalTheory C) (A : C) (rho : (𝟙_ C) ⟶ A) : Prop :=
  ∃ n : ℕ, ∃ w : Fin n → ℝ, ∃ s : Fin n → ((𝟙_ C) ⟶ A),
    (∀ i, 0 ≤ w i ∧ IsPhysical T (s i)) ∧ rho = ∑ i, w i • s i

/-- PDF p.24, (F.7): every deterministic input state and output effect,
without selecting a preferred discard effect in a noncausal theory. -/
def SingleUpperBound (T : OperationalTheory C) {A B : C} (f : A ⟶ B) : Prop :=
  ∀ rho : (𝟙_ C) ⟶ A, IsDeterministic T rho →
    ∀ d : B ⟶ (𝟙_ C), IsDeterministic T d → T.scalar (rho ≫ f ≫ d) ≤ 1

/-- PDF p.23, F.10(2): ancillary inequality, using the ambient tensor action
on all candidates, without assuming local tomography. -/
def CompleteUpperBound (T : OperationalTheory C) {A B : C} (f : A ⟶ B) : Prop :=
  ∀ S : C, ∀ rho : (𝟙_ C) ⟶ (A ⊗ S), IsDeterministic T rho →
    ∀ d : (B ⊗ S) ⟶ (𝟙_ C), IsDeterministic T d →
      T.scalar (rho ≫ (f ⊗ₘ 𝟙 S) ≫ d) ≤ 1

/-- PDF p.21: the equivalent unique-deterministic-effect definition of causality.
The candidate transformation is not required to be physical. -/
def IsCausal (T : OperationalTheory C) : Prop :=
  ∀ A : C, ∃! d : A ⟶ (𝟙_ C), IsDeterministic T d

/-- PDF pp.25–26: deterministic bipartite states are finite convex combinations
of product deterministic states; no claim about all cone elements. -/
def HasSeparableDeterministicStates (T : OperationalTheory C) : Prop :=
  ∀ A B : C, ∀ rho : (𝟙_ C) ⟶ (A ⊗ B), IsDeterministic T rho →
    ∃ n : ℕ, ∃ w : Fin n → ℝ,
      ∃ a : Fin n → ((𝟙_ C) ⟶ A), ∃ b : Fin n → ((𝟙_ C) ⟶ B),
        (∀ i, 0 ≤ w i ∧ IsDeterministic T (a i) ∧ IsDeterministic T (b i)) ∧
        (∑ i, w i) = 1 ∧
        rho = ∑ i, w i • ((λ_ (𝟙_ C)).inv ≫ (a i ⊗ₘ b i))

/-- PDF p.26: the dual finite convex combination of product deterministic effects.
Unit identification is explicit after the tensor product. -/
def HasSeparableDeterministicEffects (T : OperationalTheory C) : Prop :=
  ∀ A B : C, ∀ d : (A ⊗ B) ⟶ (𝟙_ C), IsDeterministic T d →
    ∃ n : ℕ, ∃ w : Fin n → ℝ,
      ∃ a : Fin n → (A ⟶ (𝟙_ C)), ∃ b : Fin n → (B ⟶ (𝟙_ C)),
        (∀ i, 0 ≤ w i ∧ IsDeterministic T (a i) ∧ IsDeterministic T (b i)) ∧
        (∑ i, w i) = 1 ∧
        d = ∑ i, w i • ((a i ⊗ₘ b i) ≫ (λ_ (𝟙_ C)).hom)

/-- Sanity: a singleton-test event is physical without any preservation axiom. -/
example (T : OperationalTheory C) {A B : C} (f : A ⟶ B)
    (hf : IsDeterministic T f) : IsPhysical T f :=
  ⟨[f], hf, by simp⟩

/-- Sanity: the zero vector is in the state cone via the empty conical sum. -/
example (T : OperationalTheory C) (A : C) : InStateCone T A 0 := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · simp

end OperationalDefinitions

end QAlgorithms.Papers.Independent.Dependency50.P06


