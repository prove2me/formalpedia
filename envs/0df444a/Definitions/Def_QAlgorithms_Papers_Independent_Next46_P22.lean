-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22
-- name    : QAlgorithms_Papers_Independent_Next46_P22
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T13:34:10.925522+00:00
-- url     : https://prove2.me/theorems/c6d91cc3-39d2-49ad-84ce-84492c9456b3
-- title:
--   Definitions for Structure of H-(co)module Lie algebras
-- statement:
--   The objects the formalized statements of *Structure of H-(co)module Lie algebras* (arXiv:1205.0778) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `tensorSum`: Finite Sweedler summation, §1.2, PDF p.3. Only bilinear contractions are used below. Mathlib supplies existence of the finite tensor expansion.
--   - `LinearFunction`: Linearity of a constructed function is a conclusion, not assumed data.
--   - `LeftIntegral`: Left integral on H, §1.2, PDF p.3: sum t(a₂)a₁=t(a)1.
--   - `AdInvariant`: Ad-invariance, §1.2, PDF p.3, retaining the antipode order.
--   - `NormalizedAdIntegral`: Normalized ad-invariant LEFT integral, §1.2, PDF p.3.
--   - `RightComodule`: Right H-comodule, §1.3, PDF p.4: linear, coassociative and counital.
--   - `coactionTensorImage`: Image of U tensor H inside V tensor H, PDF p.5.
--   - `CoStable`: H-subcomodule of the supplied right coaction, PDF p.5.
--   - `Colinear`: Colinearity, also applicable to constructed linear functions, PDF p.5.
--   - `averageFromCoactions`: The explicit tensor formula for averaging, PDF pp.7–8,12. Raw coaction maps are allowed so the graded formula can refer to its canonical construction.
--   - `hopfAverage`: Explicit averaging for the supplied comodules, Lemmas 4,8, PDF pp.7–8,12.
--   - `ActionStable`: Stable subspace of the particular left action, §1.4, PDF p.5.
--   - `ModuleLie`: Compatibility of the fixed left Hopf action with the bracket, PDF p.5.
--   - `ComoduleLie`: Compatibility of the given right coaction with the bracket, PDF p.4.
--   - `lieNilpotentRadical`: Actual nilpotent radical, §§2,7: supremum of nilpotent Lie ideals. This is the field-general version of the accepted real-scalar lieNilpotentRadical interface.
--   - `Semisimple`: Semisimple means zero solvable radical, the characteristic-zero convention.
--   - `MaximalSemisimple`: Maximal among semisimple Lie subalgebras; no prior Levi factor is assumed.
--   - `SplitsRadical`: Complement inside the actual radical R, rather than all of L, PDF p.14.
--   - `RadicalDecomposition`: Full internal decomposition, PDF p.14. All summands are stable; S is only a subspace, and the sole additional commuting relation is [B,S]=0.
--   - `IdealSubspace`: Ideal property for an F-subspace.
--   - `Centralizer`: Centralizer of an arbitrary F-subspace, §5, PDF p.11.
--   - `actionHull`: F-span of h i, with I an ordinary ideal, Lemma 2, PDF p.5.
--   - `SimpleStableIdeal`: H-simplicity tests ideals of P itself, not merely ideals of the ambient L, §5, PDF pp.11–12. P is separately an ambient ideal.
--   - `SimpleIdealDecomposition`: Finite internal sum of ambient stable H-simple ideals. Fin 0 covers L=0.
--   - `Grading`: Internal G-grading, §1.1, PDF p.2: finite-support homogeneous decomposition with orthogonal idempotent projections summing to the identity on each vector.
--   - `Homogeneous`: Homogeneous vectors are fixed by the corresponding projection.
--   - `GradedSubspace`: Graded subspaces are closed under homogeneous projections, PDF p.2.
--   - `GradedLie`: Lie grading with the ordered product gh, PDF p.2.
--   - `gradedCoaction`: The coaction actually constructed from the supplied grading, PDF p.4.
--   - `gradedAverage`: Sum p_W,g r p_V,g, finite on each vector, remark after Lemma 4, PDF p.8.
--   - `GradedMap`: Degree-preserving map for the two particular gradings.
--   - `identityCoefficient`: The coefficient-at-identity functional, Example 3, PDF p.3.
--   - `LieStable`: Invariant subspace of the given L-representation, §6, PDF p.12.
--   - `CompletelyReducible`: Complete reducibility of the underlying L-module, PDF p.12: every invariant subspace has an invariant complement. For finite V this is the usual notion.
--   - `CoCompatible`: Right-comodule (H,L)-compatibility, §3, PDF p.7.
--   - `SymmetricComodule`: Symmetry also requires the reversed product v₁ a₁, PDF p.7.
--   - `ActionCompatible`: Left-action (H,L)-compatibility, §6, PDF p.13.
--   - `GradedCompatible`: Graded L-module with the ordered product gh, PDF p.13.
--   - `IrreducibleIn`: Irreducibility within U tests all simultaneous invariant subspaces of U.
--   - `IrreducibleDecomposition`: Finite internal sum of irreducible simultaneous submodules; n=0 is allowed.
--   - `ColinearTwo`: Colinear alternating two-cochains, §3, PDF p.7.
--   - `LieIntertwiner`: L-linearity of the particular constructed function.
--   - `blockElement`: The two-by-two block matrix from Example 12, PDF p.10.
--   - `bahturinBlockLieAlgebra`: Canonical Lie span of the exact displayed matrices, Example 12, PDF p.10. The example theorem includes equality with that displayed set, so no closure or radical computation is assumed as a hypothesis.
--   - `blockRadical`: The displayed off-diagonal subspace R, Example 12, PDF p.10.
--   - `blockShift`: The actual matrix formula phi(C,D)=(C,C+D), Example 12, PDF p.10.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, https://arxiv.org/abs/1205.0778v7

import Mathlib

/-! Gordienko, arXiv:1205.0778v7. Paper-local interfaces; mechanical compilation pending.
All Sweedler sums are finite algebraic tensor expansions. No analytic sums occur. -/

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct
open Classical

section TensorNotation

variable {F A B : Type*} [Field F]
  [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]

/-- Finite Sweedler summation, §1.2, PDF p.3. Only bilinear contractions
are used below. Mathlib supplies existence of the finite tensor expansion. -/
def tensorSum {X : Type*} [AddCommMonoid X] (z : A ⊗[F] B) (f : A → B → X) : X :=
  ((TensorProduct.exists_finset z).choose).sum (fun p => f p.1 p.2)

/-- The expansion reconstructs the original tensor. -/
example (z : A ⊗[F] B) : tensorSum z (fun a b => a ⊗ₜ[F] b) = z :=
  (TensorProduct.exists_finset z).choose_spec.symm

/-- Linearity of a constructed function is a conclusion, not assumed data. -/
def LinearFunction (f : A → B) : Prop :=
  (∀ x y, f (x + y) = f x + f y) ∧ ∀ (c : F) x, f (c • x) = c • f x

example : LinearFunction (F := F) (fun x : A => x) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end TensorNotation

section HopfInterfaces

variable {F H : Type*} [Field F] [Ring H] [HopfAlgebra F H]

/-- Left integral on H, §1.2, PDF p.3: sum t(a₂)a₁=t(a)1. -/
def LeftIntegral (t : H →ₗ[F] F) : Prop :=
  ∀ a : H, tensorSum (Coalgebra.comul (R := F) a) (fun a1 a2 => t a2 • a1) = t a • (1 : H)

/-- Ad-invariance, §1.2, PDF p.3, retaining the antipode order. -/
def AdInvariant (t : H →ₗ[F] F) : Prop :=
  ∀ a b : H, tensorSum (Coalgebra.comul (R := F) a)
    (fun a1 a2 => t (a1 * b * HopfAlgebra.antipode F a2)) = Coalgebra.counit a * t b

/-- Normalized ad-invariant LEFT integral, §1.2, PDF p.3. -/
def NormalizedAdIntegral (t : H →ₗ[F] F) : Prop :=
  LeftIntegral t ∧ AdInvariant t ∧ t 1 = 1

/-- Right H-comodule, §1.3, PDF p.4: linear, coassociative and counital. -/
structure RightComodule (F H V : Type*) [Field F] [Ring H] [HopfAlgebra F H]
    [AddCommGroup V] [Module F V] where
  rho : V →ₗ[F] V ⊗[F] H
  coassoc : ∀ x, TensorProduct.assoc F V H H
    (TensorProduct.map rho (LinearMap.id : H →ₗ[F] H) (rho x)) =
    TensorProduct.map (LinearMap.id : V →ₗ[F] V) (Coalgebra.comul (R := F)) (rho x)
  counital : ∀ x, TensorProduct.rid F V
    (TensorProduct.map (LinearMap.id : V →ₗ[F] V) (Coalgebra.counit (R := F)) (rho x)) = x

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Image of U tensor H inside V tensor H, PDF p.5. -/
def coactionTensorImage (U : Submodule F V) : Submodule F (V ⊗[F] H) :=
  Submodule.span F {z | ∃ v ∈ U, ∃ h : H, z = v ⊗ₜ[F] h}

/-- H-subcomodule of the supplied right coaction, PDF p.5. -/
def CoStable (rho : RightComodule F H V) (U : Submodule F V) : Prop :=
  ∀ v ∈ U, rho.rho v ∈ coactionTensorImage U

/-- Colinearity, also applicable to constructed linear functions, PDF p.5. -/
def Colinear (rhoV : RightComodule F H V) (rhoW : RightComodule F H W) (f : V → W) : Prop :=
  ∀ x, rhoW.rho (f x) = tensorSum (rhoV.rho x) (fun v h => f v ⊗ₜ[F] h)

/-- The explicit tensor formula for averaging, PDF pp.7–8,12. Raw coaction
maps are allowed so the graded formula can refer to its canonical construction. -/
def averageFromCoactions (rhoV : V → V ⊗[F] H) (rhoW : W → W ⊗[F] H)
    (t : H →ₗ[F] F) (r : V →ₗ[F] W) (x : V) : W :=
  tensorSum (rhoV x) (fun v h =>
    tensorSum (rhoW (r v)) (fun w k => t (k * HopfAlgebra.antipode F h) • w))

/-- Explicit averaging for the supplied comodules, Lemmas 4,8, PDF pp.7–8,12. -/
def hopfAverage (rhoV : RightComodule F H V) (rhoW : RightComodule F H W)
    (t : H →ₗ[F] F) (r : V →ₗ[F] W) : V → W :=
  averageFromCoactions rhoV.rho rhoW.rho t r

/-- Stable subspace of the particular left action, §1.4, PDF p.5. -/
def ActionStable (alpha : H →ₐ[F] Module.End F V) (U : Submodule F V) : Prop :=
  ∀ h : H, ∀ v ∈ U, alpha h v ∈ U

example (alpha : H →ₐ[F] Module.End F V) : ActionStable alpha ⊤ := by
  intro h v hv
  trivial

end HopfInterfaces

section LieInterfaces

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- Compatibility of the fixed left Hopf action with the bracket, PDF p.5. -/
def ModuleLie (alpha : H →ₐ[F] Module.End F L) : Prop :=
  ∀ h : H, ∀ a b : L, alpha h ⁅a, b⁆ = tensorSum (Coalgebra.comul (R := F) h)
    (fun h1 h2 => ⁅alpha h1 a, alpha h2 b⁆)

/-- Compatibility of the given right coaction with the bracket, PDF p.4. -/
def ComoduleLie (rho : RightComodule F H L) : Prop :=
  ∀ a b : L, rho.rho ⁅a, b⁆ = tensorSum (rho.rho a) (fun a0 a1 =>
    tensorSum (rho.rho b) (fun b0 b1 => ⁅a0, b0⁆ ⊗ₜ[F] (a1 * b1)))

/-- Actual nilpotent radical, §§2,7: supremum of nilpotent Lie ideals.
This is the field-general version of the accepted real-scalar lieNilpotentRadical interface. -/
def lieNilpotentRadical (F L : Type*) [Field F] [LieRing L] [LieAlgebra F L] : LieIdeal F L :=
  sSup {I : LieIdeal F L | LieModule.IsNilpotent I I}

/-- Semisimple means zero solvable radical, the characteristic-zero convention. -/
def Semisimple (F L : Type*) [Field F] [LieRing L] [LieAlgebra F L] : Prop :=
  LieAlgebra.radical F L = ⊥

/-- Maximal among semisimple Lie subalgebras; no prior Levi factor is assumed. -/
def MaximalSemisimple (B : LieSubalgebra F L) : Prop :=
  Semisimple F B ∧ ∀ C : LieSubalgebra F L, B ≤ C → Semisimple F C → C = B

/-- Complement inside the actual radical R, rather than all of L, PDF p.14. -/
def SplitsRadical (S : Submodule F L) : Prop :=
  S ⊓ (lieNilpotentRadical F L).toSubmodule = ⊥ ∧
  S ⊔ (lieNilpotentRadical F L).toSubmodule = (LieAlgebra.radical F L).toSubmodule

/-- Full internal decomposition, PDF p.14. All summands are stable; S is only a
subspace, and the sole additional commuting relation is [B,S]=0. -/
def RadicalDecomposition (stable : Submodule F L → Prop)
    (B : LieSubalgebra F L) (S : Submodule F L) : Prop :=
  MaximalSemisimple B ∧ stable B.toSubmodule ∧ stable S ∧
  stable (lieNilpotentRadical F L).toSubmodule ∧ stable (LieAlgebra.radical F L).toSubmodule ∧
  SplitsRadical S ∧ IsCompl B.toSubmodule (LieAlgebra.radical F L).toSubmodule ∧
  ∀ b ∈ B, ∀ s ∈ S, ⁅b, s⁆ = 0

/-- Ideal property for an F-subspace. -/
def IdealSubspace (U : Submodule F L) : Prop := ∀ a : L, ∀ b ∈ U, ⁅a, b⁆ ∈ U

/-- Centralizer of an arbitrary F-subspace, §5, PDF p.11. -/
def Centralizer (M : Submodule F L) : Submodule F L where
  carrier := {a | ∀ b ∈ M, ⁅a, b⁆ = 0}
  zero_mem' := by intro b hb; simp
  add_mem' := by intro a c ha hc b hb; simp [add_lie, ha b hb, hc b hb]
  smul_mem' := by intro r a ha b hb; simp [smul_lie, ha b hb]

/-- F-span of h i, with I an ordinary ideal, Lemma 2, PDF p.5. -/
def actionHull (alpha : H →ₐ[F] Module.End F L) (I : LieIdeal F L) : Submodule F L :=
  Submodule.span F {v | ∃ h : H, ∃ i ∈ I, v = alpha h i}

/-- H-simplicity tests ideals of P itself, not merely ideals of the ambient L,
§5, PDF pp.11–12. P is separately an ambient ideal. -/
def SimpleStableIdeal (stable : Submodule F L → Prop) (P : LieIdeal F L) : Prop :=
  ∀ U : Submodule F L, U ≤ P.toSubmodule →
    (∀ a ∈ P, ∀ b ∈ U, ⁅a, b⁆ ∈ U) → stable U → U = ⊥ ∨ U = P.toSubmodule

/-- Finite internal sum of ambient stable H-simple ideals. Fin 0 covers L=0. -/
def SimpleIdealDecomposition (stable : Submodule F L → Prop) : Prop :=
  ∃ n : ℕ, ∃ P : Fin n → LieIdeal F L,
    iSupIndep (fun i => (P i).toSubmodule) ∧ (⨆ i, (P i).toSubmodule) = ⊤ ∧
    ∀ i, stable (P i).toSubmodule ∧ SimpleStableIdeal stable (P i)

example (M : Submodule F L) : (0 : L) ∈ Centralizer M := by
  intro b hb
  simp

end LieInterfaces

section GradingInterfaces

variable {F G V W L : Type*} [Field F] [Group G]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [LieRing L] [LieAlgebra F L]

/-- Internal G-grading, §1.1, PDF p.2: finite-support homogeneous decomposition
with orthogonal idempotent projections summing to the identity on each vector. -/
structure Grading (F G V : Type*) [Field F] [Group G] [AddCommGroup V] [Module F V] where
  decomp : V →ₗ[F] G →₀ V
  total : ∀ v, (decomp v).sum (fun _ x => x) = v
  diagonal : ∀ v g, decomp (decomp v g) g = decomp v g
  offDiagonal : ∀ v g h, h ≠ g → decomp (decomp v g) h = 0

/-- Homogeneous vectors are fixed by the corresponding projection. -/
def Homogeneous (D : Grading F G V) (g : G) (v : V) : Prop := D.decomp v g = v

/-- Graded subspaces are closed under homogeneous projections, PDF p.2. -/
def GradedSubspace (D : Grading F G V) (U : Submodule F V) : Prop :=
  ∀ v ∈ U, ∀ g, D.decomp v g ∈ U

/-- Lie grading with the ordered product gh, PDF p.2. -/
def GradedLie (D : Grading F G L) : Prop :=
  ∀ g h a b, Homogeneous D g a → Homogeneous D h b → Homogeneous D (g * h) ⁅a, b⁆

/-- The coaction actually constructed from the supplied grading, PDF p.4. -/
def gradedCoaction (D : Grading F G V) (v : V) : V ⊗[F] MonoidAlgebra F G :=
  (D.decomp v).sum (fun g x => x ⊗ₜ[F] MonoidAlgebra.single g 1)

/-- Sum p_W,g r p_V,g, finite on each vector, remark after Lemma 4, PDF p.8. -/
def gradedAverage (D : Grading F G V) (E : Grading F G W) (r : V →ₗ[F] W) (v : V) : W :=
  (D.decomp v).sum (fun g x => E.decomp (r x) g)

/-- Degree-preserving map for the two particular gradings. -/
def GradedMap (D : Grading F G V) (E : Grading F G W) (f : V → W) : Prop :=
  ∀ g v, Homogeneous D g v → Homogeneous E g (f v)

/-- The coefficient-at-identity functional, Example 3, PDF p.3. -/
def identityCoefficient : MonoidAlgebra F G →ₗ[F] F :=
  (Finsupp.lapply (1 : G)).comp (MonoidAlgebra.coeffLinearEquiv F).toLinearMap

example (D : Grading F G V) (v : V) :
    (D.decomp v).sum (fun _ x => x) = v := D.total v

end GradingInterfaces

section RepresentationInterfaces

variable {F H G L V W : Type*} [Field F] [Ring H] [HopfAlgebra F H] [Group G]
  [LieRing L] [LieAlgebra F L]
  [AddCommGroup V] [Module F V] [LieRingModule L V] [LieModule F L V]
  [AddCommGroup W] [Module F W] [LieRingModule L W] [LieModule F L W]

/-- Invariant subspace of the given L-representation, §6, PDF p.12. -/
def LieStable (U : Submodule F V) : Prop := ∀ a : L, ∀ v ∈ U, ⁅a, v⁆ ∈ U

/-- Complete reducibility of the underlying L-module, PDF p.12: every invariant
subspace has an invariant complement. For finite V this is the usual notion. -/
def CompletelyReducible (F L V : Type*) [Field F] [LieRing L] [LieAlgebra F L]
    [AddCommGroup V] [Module F V] [LieRingModule L V] [LieModule F L V] : Prop :=
  ∀ U : Submodule F V, LieStable (L := L) U →
    ∃ W : Submodule F V, LieStable (L := L) W ∧ IsCompl U W

/-- Right-comodule (H,L)-compatibility, §3, PDF p.7. -/
def CoCompatible (rhoL : RightComodule F H L) (rhoV : RightComodule F H V) : Prop :=
  ∀ a v, rhoV.rho ⁅a, v⁆ = tensorSum (rhoL.rho a) (fun a0 a1 =>
    tensorSum (rhoV.rho v) (fun v0 v1 => ⁅a0, v0⁆ ⊗ₜ[F] (a1 * v1)))

/-- Symmetry also requires the reversed product v₁ a₁, PDF p.7. -/
def SymmetricComodule (rhoL : RightComodule F H L) (rhoV : RightComodule F H V) : Prop :=
  CoCompatible rhoL rhoV ∧ ∀ a v, rhoV.rho ⁅a, v⁆ = tensorSum (rhoL.rho a) (fun a0 a1 =>
    tensorSum (rhoV.rho v) (fun v0 v1 => ⁅a0, v0⁆ ⊗ₜ[F] (v1 * a1)))

/-- Left-action (H,L)-compatibility, §6, PDF p.13. -/
def ActionCompatible (alphaL : H →ₐ[F] Module.End F L)
    (alphaV : H →ₐ[F] Module.End F V) : Prop :=
  ∀ h a v, alphaV h ⁅a, v⁆ = tensorSum (Coalgebra.comul (R := F) h)
    (fun h1 h2 => ⁅alphaL h1 a, alphaV h2 v⁆)

/-- Graded L-module with the ordered product gh, PDF p.13. -/
def GradedCompatible (D : Grading F G L) (E : Grading F G V) : Prop :=
  ∀ g h a v, Homogeneous D g a → Homogeneous E h v → Homogeneous E (g * h) ⁅a, v⁆

/-- Irreducibility within U tests all simultaneous invariant subspaces of U. -/
def IrreducibleIn (stable : Submodule F V → Prop) (U : Submodule F V) : Prop :=
  LieStable (L := L) U ∧ stable U ∧ ∀ W : Submodule F V,
    W ≤ U → LieStable (L := L) W → stable W → W = ⊥ ∨ W = U

/-- Finite internal sum of irreducible simultaneous submodules; n=0 is allowed. -/
def IrreducibleDecomposition (stable : Submodule F V → Prop) : Prop :=
  ∃ n : ℕ, ∃ U : Fin n → Submodule F V,
    iSupIndep U ∧ (⨆ i, U i) = ⊤ ∧ ∀ i, IrreducibleIn (L := L) stable (U i)

/-- Colinear alternating two-cochains, §3, PDF p.7. -/
def ColinearTwo (rhoL : RightComodule F H L) (rhoV : RightComodule F H V)
    (omega : LieModule.Cohomology.twoCochain F L V) : Prop :=
  ∀ a b, rhoV.rho (omega a b) = tensorSum (rhoL.rho a) (fun a0 a1 =>
    tensorSum (rhoL.rho b) (fun b0 b1 => omega a0 b0 ⊗ₜ[F] (a1 * b1)))

/-- L-linearity of the particular constructed function. -/
def LieIntertwiner (f : V → W) : Prop := ∀ (a : L) (v : V), f ⁅a, v⁆ = ⁅a, f v⁆

example : LieStable (L := L) (⊤ : Submodule F V) := by
  intro a v hv
  trivial

end RepresentationInterfaces

section ConcreteAlgebras

attribute [local instance] LieRing.ofAssociativeRing

/-- The two-by-two block matrix from Example 12, PDF p.10. -/
def blockElement {F : Type*} [Field F] (m : ℕ)
    (C D : Matrix (Fin m) (Fin m) F) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F :=
  Matrix.fromBlocks C D 0 0

/-- Canonical Lie span of the exact displayed matrices, Example 12, PDF p.10.
The example theorem includes equality with that displayed set, so no closure or
radical computation is assumed as a hypothesis. -/
def bahturinBlockLieAlgebra (F : Type*) [Field F] (m : ℕ) :=
  LieSubalgebra.lieSpan F (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F)
    {X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F |
    ∃ C D : Matrix (Fin m) (Fin m) F, Matrix.trace C = 0 ∧ X = blockElement m C D}

/-- The displayed off-diagonal subspace R, Example 12, PDF p.10. -/
def blockRadical (F : Type*) [Field F] (m : ℕ) : Submodule F (bahturinBlockLieAlgebra F m) :=
  (Submodule.span F {X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F |
    ∃ D : Matrix (Fin m) (Fin m) F, X = blockElement m 0 D}).comap
      (bahturinBlockLieAlgebra F m).toSubmodule.subtype

/-- The actual matrix formula phi(C,D)=(C,C+D), Example 12, PDF p.10. -/
def blockShift {F : Type*} [Field F] (m : ℕ) (a : bahturinBlockLieAlgebra F m) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F :=
  blockElement m (fun i j => (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (Sum.inl i) (Sum.inl j))
    (fun i j => (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (Sum.inl i) (Sum.inl j) +
      (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (Sum.inl i) (Sum.inr j))

example {F : Type*} [Field F] (m : ℕ) (C D : Matrix (Fin m) (Fin m) F)
    (i j : Fin m) : blockElement m C D (Sum.inl i) (Sum.inr j) = D i j := rfl

end ConcreteAlgebras

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

section BlockExamples

attribute [local instance] LieRing.ofAssociativeRing

end BlockExamples

section LieModules

variable [LieRingModule L V] [LieModule F L V] [LieRingModule L W] [LieModule F L W]

end LieModules

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22


