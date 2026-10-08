-- Prove2me | Definitions.Def_VertexAlgebraNet
-- name    : VertexAlgebraNet
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:57.37912+00:00
-- url     : https://prove2.me/theorems/430e49ff-2663-474b-bd25-2316c2bcb615
-- statement:
--   This block sets up vertex algebras over ℂ and a framework for conformal nets on the circle. A state field is a linear map Y from V to vertex operators on W, with modes Y(a)_n; JacobiIdentity is the stated mode-level Jacobi identity with binomial coefficients and finite sums over j. A VertexAlgebra on V consists of a vacuum, a state field, vacuum modes equal to the identity at n=-1 and zero otherwise, the creation property Y(a)_{-1}vacuum = a, vanishing of Y(a)_n vacuum for n ≥ 0, and the Jacobi identity. It defines the translation operator a ↦ Y(a)_{-2}vacuum, the C2 subspace spanned by all Y(a)_{-2}b, C2-cofiniteness (finite-dimensional quotient V/C2), ideals (closed under all modes and translation), and simplicity (nonzero vacuum and only the trivial ideals). A WeakModule is a state field into W with the vacuum acting as identity and a module Jacobi identity, with invariant submodules and complete reducibility (every invariant subspace has an invariant complement). A CFTTypeVOA adds a conformal vector, central charge, an ℕ-grading by finite-dimensional pieces with grade 0 spanned by the vacuum, the conformal vector in grade 2, L₀-type eigenvalue conditions, translation covariance, and Virasoro commutation relations. On it the block defines Virasoro modes, energyShift 1+L₀, admissible modules (compatible ℤ-gradings bounded below), rationality (every admissible weak module is completely reducible), self-contragredience via a linear isomorphism with the graded dual, and IsStronglyRational as self-contragredient, rational and C2-cofinite. In the inner-product setting it defines polynomial energy bounds, a UnitaryStructure (an antilinear involution fixing vacuum and conformal vector, compatible with modes, unit vacuum norm, and an invariance formula for the inner product), smeared fields on the completion using rapidly decaying Fourier coefficients of smooth 2π-periodic functions, their closures, local von Neumann algebras generated from graph entries of closed fields supported in open sets, interval algebras on proper circle arcs, and CKLWStrongLocal, a defined proposition that all vectors satisfy polynomial energy bounds and each interval algebra lies in the commutant of its complementary interval algebra. It also develops the circle diffeomorphism group, Möbius subgroup, projective unitary group, and a flow constructed from a self-adjoint operator by resolvent approximations. Finally IrreducibleConformalNetStructure packages a family of von Neumann algebras indexed by proper arcs with separability, isotony, locality, a continuous Möbius representation, a continuous projective representation of circle diffeomorphisms extending it, covariance, locality of support, a unit invariant vacuum unique up to scalars and cyclic, a positive self-adjoint Hamiltonian generating the rotation flow, and irreducibility of the commutant.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/VertexAlgebraNet.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/VertexAlgebraNet.lean; bytes 16..47277
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

/-! The strongly rational unitary vertex operator algebra main result, clause (1). -/

noncomputable section
universe u v w

namespace OAI.StronglyRationalVOA
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

noncomputable abbrev StateField (V : Type u) (W : Type v)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :=
  V →ₗ[ℂ] VertexOperator ℂ W

noncomputable def mode {W : Type v} [AddCommGroup W] [Module ℂ W]
    (Y : OAI.StronglyRationalVOA.StateField V W) (a : V) (n : ℤ) : Module.End ℂ W :=
  VertexOperator.ncoeff (Y a) n

noncomputable def JacobiIdentity (Y : OAI.StronglyRationalVOA.StateField V V) : Prop :=
  ∀ (a b c : V) (m n k : ℤ),
    (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j •
      OAI.StronglyRationalVOA.mode Y (OAI.StronglyRationalVOA.mode Y a (n + j) b) (m + k - j) c) =
    ∑ᶠ j : ℕ, ((-1 : ℂ) ^ j * Ring.choose (n : ℂ) j) •
      (OAI.StronglyRationalVOA.mode Y a (m + n - j) (OAI.StronglyRationalVOA.mode Y b (k + j) c) -
        (-1 : ℂ) ^ n • OAI.StronglyRationalVOA.mode Y b (n + k - j) (OAI.StronglyRationalVOA.mode Y a (m + j) c))

structure VertexAlgebra (V : Type u) [AddCommGroup V] [Module ℂ V] where
  vacuum : V
  fields : OAI.StronglyRationalVOA.StateField V V
  vacuum_mode : ∀ (n : ℤ), OAI.StronglyRationalVOA.mode fields vacuum n = if n = -1 then 1 else 0
  creation : ∀ a : V, OAI.StronglyRationalVOA.mode fields a (-1) vacuum = a
  creation_truncation : ∀ (a : V) (n : ℤ), 0 ≤ n → OAI.StronglyRationalVOA.mode fields a n vacuum = 0
  jacobi : OAI.StronglyRationalVOA.JacobiIdentity fields

end OAI.StronglyRationalVOA

namespace OAI.StronglyRationalVOA.VertexAlgebra
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (A : VertexAlgebra V)

noncomputable def translation : Module.End ℂ V where
  toFun a := OAI.StronglyRationalVOA.mode A.fields a (-2) A.vacuum
  map_add' a b := by simp [OAI.StronglyRationalVOA.mode]
  map_smul' z a := by simp [OAI.StronglyRationalVOA.mode]

noncomputable def c2 : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ a b : V, x = OAI.StronglyRationalVOA.mode A.fields a (-2) b}

noncomputable def C2Cofinite : Prop := FiniteDimensional ℂ (V ⧸ A.c2)

noncomputable def IsIdeal (I : Submodule ℂ V) : Prop :=
  (∀ a : V, ∀ n : ℤ, ∀ x ∈ I, OAI.StronglyRationalVOA.mode A.fields a n x ∈ I) ∧
  ∀ x ∈ I, A.translation x ∈ I

noncomputable def IsSimple : Prop :=
  A.vacuum ≠ 0 ∧ ∀ I : Submodule ℂ V, A.IsIdeal I → I = ⊥ ∨ I = ⊤

end OAI.StronglyRationalVOA.VertexAlgebra

namespace OAI.StronglyRationalVOA
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

noncomputable def ModuleJacobiIdentity {W : Type v} [AddCommGroup W] [Module ℂ W]
    (A : OAI.StronglyRationalVOA.VertexAlgebra V) (Y : OAI.StronglyRationalVOA.StateField V W) : Prop :=
  ∀ (a b : V) (c : W) (m n k : ℤ),
    (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j •
      OAI.StronglyRationalVOA.mode Y (OAI.StronglyRationalVOA.mode A.fields a (n + j) b) (m + k - j) c) =
    ∑ᶠ j : ℕ, ((-1 : ℂ) ^ j * Ring.choose (n : ℂ) j) •
      (OAI.StronglyRationalVOA.mode Y a (m + n - j) (OAI.StronglyRationalVOA.mode Y b (k + j) c) -
        (-1 : ℂ) ^ n • OAI.StronglyRationalVOA.mode Y b (n + k - j) (OAI.StronglyRationalVOA.mode Y a (m + j) c))

structure WeakModule (A : OAI.StronglyRationalVOA.VertexAlgebra V) (W : Type v)
    [AddCommGroup W] [Module ℂ W] where
  fields : OAI.StronglyRationalVOA.StateField V W
  vacuum_mode : ∀ n : ℤ, OAI.StronglyRationalVOA.mode fields A.vacuum n = if n = -1 then 1 else 0
  jacobi : OAI.StronglyRationalVOA.ModuleJacobiIdentity A fields

end OAI.StronglyRationalVOA

namespace OAI.StronglyRationalVOA.WeakModule
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : Type v} [AddCommGroup W] [Module ℂ W]
    {A : VertexAlgebra V} (M : WeakModule A W)

noncomputable def IsInvariant (I : Submodule ℂ W) : Prop :=
  ∀ a : V, ∀ n : ℤ, ∀ x ∈ I, OAI.StronglyRationalVOA.mode M.fields a n x ∈ I

noncomputable def CompletelyReducible : Prop :=
  ∀ I : Submodule ℂ W, M.IsInvariant I →
    ∃ J : Submodule ℂ W, M.IsInvariant J ∧ IsCompl I J

end OAI.StronglyRationalVOA.WeakModule

namespace OAI.StronglyRationalVOA
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

structure CFTTypeVOA (V : Type u) [AddCommGroup V] [Module ℂ V]
    extends OAI.StronglyRationalVOA.VertexAlgebra V where
  conformalVector : V
  centralCharge : ℂ
  grade : ℕ → Submodule ℂ V
  grading_internal : DirectSum.IsInternal grade
  grade_finite : ∀ d, FiniteDimensional ℂ (grade d)
  vacuum_ne_zero : vacuum ≠ 0
  grade_zero : grade 0 = ℂ ∙ vacuum
  conformal_mem : conformalVector ∈ grade 2
  conformal_energy : ∀ d, ∀ a ∈ grade d,
    OAI.StronglyRationalVOA.mode fields conformalVector 1 a = (d : ℂ) • a
  conformal_translation : OAI.StronglyRationalVOA.mode fields conformalVector 0 = toVertexAlgebra.translation
  translation_covariance : ∀ a : V, ∀ n : ℤ,
    OAI.StronglyRationalVOA.mode fields (toVertexAlgebra.translation a) n =
      (-(n : ℂ)) • OAI.StronglyRationalVOA.mode fields a (n - 1)
  virasoro : ∀ m n : ℤ,
    (OAI.StronglyRationalVOA.mode fields conformalVector (m + 1)).comp (OAI.StronglyRationalVOA.mode fields conformalVector (n + 1)) -
      (OAI.StronglyRationalVOA.mode fields conformalVector (n + 1)).comp (OAI.StronglyRationalVOA.mode fields conformalVector (m + 1)) =
    ((m - n : ℤ) : ℂ) • OAI.StronglyRationalVOA.mode fields conformalVector (m + n + 1) +
      (if m + n = 0 then (centralCharge / 12) * ((m : ℂ)^3 - m) else 0) •
        (1 : Module.End ℂ V)

end OAI.StronglyRationalVOA

namespace OAI.StronglyRationalVOA.CFTTypeVOA
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (A : CFTTypeVOA V)

noncomputable def virasoroMode (m : ℤ) : Module.End ℂ V :=
  OAI.StronglyRationalVOA.mode A.fields A.conformalVector (m + 1)

noncomputable def physicalMode (a : V) (d : ℕ) (m : ℤ) : Module.End ℂ V :=
  OAI.StronglyRationalVOA.mode A.fields a (m + d - 1)

noncomputable def energyShift : Module.End ℂ V := 1 + A.virasoroMode 0

noncomputable def gradingEquiv : V ≃ₗ[ℂ] DirectSum ℕ (fun d => A.grade d) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap A.grade) A.grading_internal).symm

noncomputable def IsAdmissible {W : Type v} [AddCommGroup W] [Module ℂ W]
    (M : OAI.StronglyRationalVOA.WeakModule A.toVertexAlgebra W) : Prop :=
  ∃ G : ℤ → Submodule ℂ W,
    DirectSum.IsInternal G ∧ (∀ k : ℤ, k < 0 → G k = ⊥) ∧
      ∀ d : ℕ, ∀ a ∈ A.grade d, ∀ n k : ℤ, ∀ x ∈ G k,
        OAI.StronglyRationalVOA.mode M.fields a n x ∈ G (k + d - n - 1)

noncomputable def IsRational : Prop :=
  ∀ (W : Type v) [AddCommGroup W] [Module ℂ W]
    (M : OAI.StronglyRationalVOA.WeakModule A.toVertexAlgebra W),
    A.IsAdmissible M → M.CompletelyReducible

end OAI.StronglyRationalVOA.CFTTypeVOA

namespace OAI.StronglyRationalVOA.CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

noncomputable def PolynomialEnergyBound (a : V) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ p k : ℕ, ∀ (n : ℤ) (b : V),
    ‖OAI.StronglyRationalVOA.mode A.fields a n b‖ ≤ C * (1 + |(n : ℝ)|) ^ p * ‖(A.energyShift ^ k) b‖

noncomputable def PolynomialEnergyBounds : Prop := ∀ a : V, A.PolynomialEnergyBound a

structure UnitaryStructure where
  pct : V →ₛₗ[starRingEnd ℂ] V
  pct_involutive : Function.Involutive pct
  pct_vacuum : pct A.vacuum = A.vacuum
  pct_conformal : pct A.conformalVector = A.conformalVector
  pct_modes : ∀ (a b : V) (n : ℤ),
    pct (OAI.StronglyRationalVOA.mode A.fields a n b) = OAI.StronglyRationalVOA.mode A.fields (pct a) n (pct b)
  vacuum_norm : ‖A.vacuum‖ = 1
  invariant : ∀ d : ℕ, ∀ a ∈ A.grade d, ∀ n : ℤ, ∀ b c : V,
    inner ℂ (OAI.StronglyRationalVOA.mode A.fields a n b) c =
      inner ℂ b (((-1 : ℂ) ^ d) •
        ∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) •
          OAI.StronglyRationalVOA.mode A.fields ((A.virasoroMode 1 ^ j) (pct a))
            (2 * (d : ℤ) - j - n - 2) c)

end OAI.StronglyRationalVOA.CFTTypeVOA

namespace OAI.StronglyRationalVOA.HilbertCore
open Filter
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.space (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    Submodule ℂ (Completion V) :=
  LinearMap.range (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.equiv (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    V ≃ₗ[ℂ] (OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.space V) :=
  LinearEquiv.ofInjective (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap
    (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.operator (T : V →ₗ[ℂ] Completion V) : Completion V →ₗ.[ℂ] Completion V where
  domain := (OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.space V)
  toFun := T.comp (OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.equiv V).symm.toLinearMap

end OAI.StronglyRationalVOA.HilbertCore

namespace OAI.StronglyRationalVOA
open Filter

noncomputable def RapidCoefficients (f : ℤ → ℂ) : Prop :=
  ∀ p : ℕ, Summable (fun n : ℤ => ‖f n‖*(1+|(n : ℝ)|)^p)

end OAI.StronglyRationalVOA

namespace OAI.StronglyRationalVOA.SummableLinearFamily
open Filter
variable {ι V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup H] [NormedSpace ℂ H]

noncomputable def tsumMap (T : ι → V →ₗ[ℂ] H) (hT : ∀ v, Summable (fun n => T n v)) : V →ₗ[ℂ] H where
  toFun v := ∑' n, T n v
  map_add' v w := by simpa only [map_add] using (hT v).tsum_add (hT w)
  map_smul' z v := by
    simpa only [map_smul, RingHom.id_apply] using (hT v).tsum_const_smul z

end OAI.StronglyRationalVOA.SummableLinearFamily

namespace OAI.StronglyRationalVOA
open Filter
open scoped ContDiff

structure SmoothCircleFunction where
  toFun : ℝ → ℂ
  periodic : Function.Periodic toFun (2*Real.pi)
  smooth : ContDiff ℝ ∞ toFun

end OAI.StronglyRationalVOA

namespace OAI.StronglyRationalVOA.SmoothCircleFunction
open Filter
open scoped ContDiff

noncomputable instance : CoeFun OAI.StronglyRationalVOA.SmoothCircleFunction (fun _ => ℝ → ℂ) := ⟨OAI.StronglyRationalVOA.SmoothCircleFunction.toFun⟩

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleFunction.coefficient (f : OAI.StronglyRationalVOA.SmoothCircleFunction) (n : ℤ) : ℂ := by
  classical
  have h_OAI_StronglyRationalVOA_SmoothCircleFunction_period_pos  : 0 < 2*Real.pi := by positivity
  exact
    fourierCoeffOn h_OAI_StronglyRationalVOA_SmoothCircleFunction_period_pos f n

end OAI.StronglyRationalVOA.SmoothCircleFunction

namespace OAI.StronglyRationalVOA.ClosedGraphData
open Filter
open scoped ContDiff
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable abbrev _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double (H : Type u) := WithLp 2 (H × H)

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.graph (T : H →ₗ.[ℂ] H) : Submodule ℂ (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H) :=
  T.graph.comap (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toLinearEquiv.toLinearMap

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.projection (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) : (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H) →L[ℂ] (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H) := by
  classical
  have h_OAI_StronglyRationalVOA_ClosedGraphData_graph_closed {H : Type u} [instLocal1 : NormedAddCommGroup H] [instLocal2 : InnerProductSpace ℂ H]  {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) :
      IsClosed ((OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.graph T) : Set (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H)) :=
    hT.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ H H).continuous
  letI : IsClosed ((OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.graph T) : Set (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H)) := (h_OAI_StronglyRationalVOA_ClosedGraphData_graph_closed hT)
  exact (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.graph T).starProjection

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.inclusion (i : Bool) : H →L[ℂ] (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (if i then ContinuousLinearMap.inr ℂ H H else ContinuousLinearMap.inl ℂ H H)

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.coordinate (i : Bool) : (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H) →L[ℂ] H :=
  (if i then ContinuousLinearMap.snd ℂ H H else ContinuousLinearMap.fst ℂ H H).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toContinuousLinearMap

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.entry (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (i j : Bool) : H →L[ℂ] H :=
  (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.coordinate i).comp ((OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.projection T hT).comp (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.inclusion j))

end OAI.StronglyRationalVOA.ClosedGraphData

namespace OAI.StronglyRationalVOA.LocalOperatorAlgebra
open Filter
open scoped ContDiff
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open scoped Pointwise

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.LocalOperatorAlgebra.generated (s : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))) =
        (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))
    rw [StarSubalgebra.coe_centralizer_centralizer]
    rw [Set.centralizer_centralizer_centralizer]

end OAI.StronglyRationalVOA.LocalOperatorAlgebra

namespace OAI.StronglyRationalVOA.SmoothCircleFunction
open Filter
open scoped ContDiff

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleFunction.onCircle (f : OAI.StronglyRationalVOA.SmoothCircleFunction) : AddCircle (2*Real.pi) → ℂ :=
  f.periodic.lift

end OAI.StronglyRationalVOA.SmoothCircleFunction

namespace OAI.StronglyRationalVOA
open Filter
open scoped ContDiff

structure ProperCircleArc where
  left : ℝ
  right : ℝ
  nonempty' : left < right
  nondense' : right < left + 2*Real.pi

end OAI.StronglyRationalVOA

namespace OAI.StronglyRationalVOA.ProperCircleArc
open Filter
open scoped ContDiff

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier (I : OAI.StronglyRationalVOA.ProperCircleArc) : Set (AddCircle (2*Real.pi)) :=
  (fun t : ℝ => (t : AddCircle (2*Real.pi))) '' Set.Ioo I.left I.right

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.complement (I : OAI.StronglyRationalVOA.ProperCircleArc) : OAI.StronglyRationalVOA.ProperCircleArc where
  left := I.right
  right := I.left + 2*Real.pi
  nonempty' := I.nondense'
  nondense' := by linarith [I.nonempty']

end OAI.StronglyRationalVOA.ProperCircleArc

namespace OAI.StronglyRationalVOA.BoundedFlow
open scoped Topology
open Filter
open scoped Topology
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.BoundedFlow.boundedFlowRationalNormedAlgebra : NormedAlgebra ℚ (H →L[ℂ] H) :=
  .restrictScalars ℚ ℂ (H →L[ℂ] H)

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.BoundedFlow.flow (K : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H := NormedSpace.exp (t • K)

end OAI.StronglyRationalVOA.BoundedFlow

namespace OAI.StronglyRationalVOA
open scoped ContDiff

structure SmoothCircleLift where
  toOrderIso : ℝ ≃o ℝ
  smooth : ContDiff ℝ ∞ toOrderIso
  inverse_smooth : ContDiff ℝ ∞ toOrderIso.symm
  period : ∀ t, toOrderIso (t+2*Real.pi)=toOrderIso t+2*Real.pi

end OAI.StronglyRationalVOA

namespace OAI.StronglyRationalVOA.SmoothCircleLift
open scoped ContDiff

noncomputable instance : CoeFun OAI.StronglyRationalVOA.SmoothCircleLift (fun _ => ℝ → ℝ) := ⟨fun F => F.toOrderIso⟩

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.identity : OAI.StronglyRationalVOA.SmoothCircleLift where
  toOrderIso := OrderIso.refl ℝ
  smooth := contDiff_id
  inverse_smooth := contDiff_id
  period := fun _ => rfl

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.compose (F G : OAI.StronglyRationalVOA.SmoothCircleLift) : OAI.StronglyRationalVOA.SmoothCircleLift where
  toOrderIso := G.toOrderIso.trans F.toOrderIso
  smooth := F.smooth.comp G.smooth
  inverse_smooth := G.inverse_smooth.comp F.inverse_smooth
  period := by intro t; change F (G (t+2*Real.pi))=F (G t)+2*Real.pi; rw [G.period,F.period]

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.inverse (F : OAI.StronglyRationalVOA.SmoothCircleLift) : OAI.StronglyRationalVOA.SmoothCircleLift where
  toOrderIso := F.toOrderIso.symm
  smooth := F.inverse_smooth
  inverse_smooth := F.smooth
  period := by
    intro t
    apply F.toOrderIso.injective
    rw [F.toOrderIso.apply_symm_apply,F.period,F.toOrderIso.apply_symm_apply]

noncomputable instance _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup : Group OAI.StronglyRationalVOA.SmoothCircleLift := by
  classical
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_ext  {F G : OAI.StronglyRationalVOA.SmoothCircleLift} (h : ∀ t, F t=G t) : F=G := by
    cases F with
    | mk f hf hfi hp =>
      cases G with
      | mk g hg hgi hgp =>
        have he : f=g := DFunLike.ext _ _ h
        subst g
        rfl
  exact {
    mul := OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.compose
    one := OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.identity
    inv := OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.inverse
    npow := @npowRec OAI.StronglyRationalVOA.SmoothCircleLift
      ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.identity⟩
      ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.compose⟩
    div := fun F G => OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.compose F
      (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.inverse G)
    zpow := @zpowRec OAI.StronglyRationalVOA.SmoothCircleLift
      ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.identity⟩
      ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.compose⟩
      ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.inverse⟩
      (@npowRec OAI.StronglyRationalVOA.SmoothCircleLift
        ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.identity⟩
        ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.compose⟩)
    mul_assoc F G H := by apply h_OAI_StronglyRationalVOA_SmoothCircleLift_ext; intro t; rfl
    one_mul F := by apply h_OAI_StronglyRationalVOA_SmoothCircleLift_ext; intro t; rfl
    mul_one F := by apply h_OAI_StronglyRationalVOA_SmoothCircleLift_ext; intro t; rfl
    inv_mul_cancel F := by apply h_OAI_StronglyRationalVOA_SmoothCircleLift_ext; intro t; exact F.toOrderIso.symm_apply_apply t
  }

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle (F : OAI.StronglyRationalVOA.SmoothCircleLift) : AddCircle (2*Real.pi) → AddCircle (2*Real.pi) := by
  classical
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_one_apply  (t : ℝ) : (1 : OAI.StronglyRationalVOA.SmoothCircleLift) t=t := rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_mul_apply  (F G : OAI.StronglyRationalVOA.SmoothCircleLift) (t : ℝ) : (F*G) t=F (G t) := rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_circle_periodic  (F : OAI.StronglyRationalVOA.SmoothCircleLift) : Function.Periodic (fun t : ℝ => (F t : AddCircle (2*Real.pi))) (2*Real.pi) := by
    intro t
    change ((F.toOrderIso (t+2*Real.pi) : ℝ) : AddCircle (2*Real.pi)) =
      (F.toOrderIso t : AddCircle (2*Real.pi))
    rw [F.period,AddCircle.coe_add]
    simp
  exact
    (h_OAI_StronglyRationalVOA_SmoothCircleLift_circle_periodic F).lift

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleHomeomorph (F : OAI.StronglyRationalVOA.SmoothCircleLift) :
    AddCircle (2*Real.pi) ≃ₜ AddCircle (2*Real.pi) := by
  classical
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_one_apply  (t : ℝ) : (1 : OAI.StronglyRationalVOA.SmoothCircleLift) t=t := rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_one  (t : AddCircle (2*Real.pi)) : (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle 1 t)=t := by
    induction t using QuotientAddGroup.induction_on with
    | H t => rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_mul  (F G : OAI.StronglyRationalVOA.SmoothCircleLift) (t : AddCircle (2*Real.pi)) :
      (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle (F * G) t)=(OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle G t)) := by
    induction t using QuotientAddGroup.induction_on with
    | H t => rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_inverse  (F : OAI.StronglyRationalVOA.SmoothCircleLift) (t : AddCircle (2*Real.pi)) : (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F⁻¹ (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F t))=t := by
    rw [← h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_mul,inv_mul_cancel,h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_one]
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_continuous_onCircle  (F : OAI.StronglyRationalVOA.SmoothCircleLift) : Continuous (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F) := by
    exact ((AddCircle.continuous_mk' (2*Real.pi)).comp F.smooth.continuous).quotient_liftOn' _
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_mul_apply  (F G : OAI.StronglyRationalVOA.SmoothCircleLift) (t : ℝ) : (F*G) t=F (G t) := rfl
  exact {
    toFun := (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F)
    invFun := (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F⁻¹)
    left_inv := (h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_inverse F)
    right_inv := by intro t; simpa [h_OAI_StronglyRationalVOA_SmoothCircleLift_one_apply, h_OAI_StronglyRationalVOA_SmoothCircleLift_mul_apply] using (h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_inverse F⁻¹ t)
    continuous_toFun := (h_OAI_StronglyRationalVOA_SmoothCircleLift_continuous_onCircle F)
    continuous_invFun := (h_OAI_StronglyRationalVOA_SmoothCircleLift_continuous_onCircle F⁻¹)
  }

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction : OAI.StronglyRationalVOA.SmoothCircleLift →* Equiv.Perm (AddCircle (2*Real.pi)) := by
  classical
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_one  (t : AddCircle (2*Real.pi)) : (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle 1 t)=t := by
    induction t using QuotientAddGroup.induction_on with
    | H t => rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_mul  (F G : OAI.StronglyRationalVOA.SmoothCircleLift) (t : AddCircle (2*Real.pi)) :
      (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle (F * G) t)=(OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle G t)) := by
    induction t using QuotientAddGroup.induction_on with
    | H t => rfl
  exact {
    toFun F := (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleHomeomorph F).toEquiv
    map_one' := by ext x; exact (h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_one x)
    map_mul' F G := by ext x; exact (h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_mul F G x)
  }

end OAI.StronglyRationalVOA.SmoothCircleLift

namespace OAI.StronglyRationalVOA
open scoped ContDiff

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism := OAI.StronglyRationalVOA.SmoothCircleLift ⧸ (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).ker

noncomputable instance _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.instGroupSmoothCircleDiffeomorphism : Group OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism := inferInstanceAs
  (Group (OAI.StronglyRationalVOA.SmoothCircleLift ⧸ (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).ker))

end OAI.StronglyRationalVOA

namespace OAI.StronglyRationalVOA
open UniformSpace

noncomputable def scalarPhaseSubgroup (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Subgroup (H ≃ₗᵢ[ℂ] H) where
  carrier := {E | ∃ c : ℂ, ‖c‖=1 ∧ ∀ x : H, E x=c • x}
  one_mem' := ⟨1,by simp,fun x => (one_smul ℂ x).symm⟩
  mul_mem' := by
    rintro E F ⟨c,hc,he⟩ ⟨d,hd,hf⟩
    refine ⟨c*d,by rw [norm_mul,hc,hd,one_mul],?_⟩
    intro x
    change E (F x)=(c*d) • x
    rw [hf,he,mul_smul]
  inv_mem' := by
    rintro E ⟨c,hc,he⟩
    have hn : c ≠ 0 := by intro h; rw [h,norm_zero] at hc; norm_num at hc
    refine ⟨c⁻¹,by rw [norm_inv,hc,inv_one],?_⟩
    intro x
    apply E.injective
    change E (E.symm x)=E (c⁻¹ • x)
    rw [E.apply_symm_apply,map_smul,he,smul_smul,inv_mul_cancel₀ hn,one_smul]

noncomputable instance scalarPhaseSubgroup_normal (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (OAI.StronglyRationalVOA.scalarPhaseSubgroup H).Normal where
  conj_mem := by
    rintro E ⟨c,hc,he⟩ F
    refine ⟨c,hc,?_⟩
    intro x
    change F (E (F.symm x))=c • x
    rw [he,map_smul,F.apply_symm_apply]

noncomputable abbrev ProjectiveUnitaryGroup (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  (H ≃ₗᵢ[ℂ] H) ⧸ OAI.StronglyRationalVOA.scalarPhaseSubgroup H

end OAI.StronglyRationalVOA

namespace OAI.StronglyRationalVOA.SmoothCircleLift
open Filter Set
open scoped Topology ContDiff

noncomputable def jet (F : OAI.StronglyRationalVOA.SmoothCircleLift) (k : ℕ) : C(ℝ,ℝ) :=
  ⟨iteratedDeriv k F, F.smooth.continuous_iteratedDeriv k
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))⟩

noncomputable instance : TopologicalSpace OAI.StronglyRationalVOA.SmoothCircleLift :=
  TopologicalSpace.induced (fun F => OAI.StronglyRationalVOA.SmoothCircleLift.jet F) inferInstance

end OAI.StronglyRationalVOA.SmoothCircleLift

namespace OAI.StronglyRationalVOA
open UniformSpace Filter Set
open scoped Topology

noncomputable instance unitaryStrongTopology (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    TopologicalSpace (H ≃ₗᵢ[ℂ] H) :=
  TopologicalSpace.induced (fun E : H ≃ₗᵢ[ℂ] H => (E : H → H)) inferInstance

noncomputable instance _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.instTopologicalSpaceSmoothCircleDiffeomorphism : TopologicalSpace OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism := inferInstanceAs
  (TopologicalSpace (OAI.StronglyRationalVOA.SmoothCircleLift ⧸ (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).ker))

end OAI.StronglyRationalVOA

namespace OAI.StronglyRationalVOA.CircleMobiusGeometry
open Set
open scoped MatrixGroups

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Rel (M : SL(2,ℝ)) (x y : ℝ) : Prop :=
  (M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2))*Real.sin (y/2)=
    (M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2))*Real.cos (y/2)

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements (M : SL(2,ℝ)) (F : OAI.StronglyRationalVOA.SmoothCircleLift) : Prop := ∀ x, (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Rel M x ((OAI.StronglyRationalVOA.SmoothCircleLift.toOrderIso F) x))

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.lifts : Subgroup OAI.StronglyRationalVOA.SmoothCircleLift := by
  classical
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_one_apply  (t : ℝ) : (1 : OAI.StronglyRationalVOA.SmoothCircleLift) t=t := rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_mul_apply  (F G : OAI.StronglyRationalVOA.SmoothCircleLift) (t : ℝ) : (F*G) t=F (G t) := rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_apply_inv_apply  (F : OAI.StronglyRationalVOA.SmoothCircleLift) (t : ℝ) : F (F⁻¹ t)=t := F.toOrderIso.apply_symm_apply t
  have h_OAI_StronglyRationalVOA_CircleMobiusGeometry_implements_inv  {M : SL(2,ℝ)} {F : OAI.StronglyRationalVOA.SmoothCircleLift}
      (hF : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements M F)) : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements M⁻¹ F⁻¹) := by
    intro x
    have h := hF (F⁻¹ x)
    rw [OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Rel,(h_OAI_StronglyRationalVOA_SmoothCircleLift_apply_inv_apply F)] at h
    simp only [OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Rel,Matrix.SpecialLinearGroup.SL2_inv_expl,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one]
    linear_combination -h
  have h_OAI_StronglyRationalVOA_CircleMobiusGeometry_implements_one  : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements 1 1) := by
    intro x
    simp [h_OAI_StronglyRationalVOA_SmoothCircleLift_one_apply, OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Rel,mul_comm]
  have h_OAI_StronglyRationalVOA_CircleMobiusGeometry_collinear_unit  {p q c s : ℝ} (hu : c^2+s^2=1) (h : p*s=q*c) :
      (p*c+q*s)*c=p ∧ (p*c+q*s)*s=q := by
    constructor
    · linear_combination p*hu-s*h
    · linear_combination q*hu+c*h
  have h_OAI_StronglyRationalVOA_CircleMobiusGeometry_cos_sq_add_sin_sq  (x : ℝ) : Real.cos x^2+Real.sin x^2=1 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have h_OAI_StronglyRationalVOA_CircleMobiusGeometry_implements_mul  {M N : SL(2,ℝ)} {F G : OAI.StronglyRationalVOA.SmoothCircleLift}
      (hF : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements M F)) (hG : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements N G)) : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements (M * N) (F * G)) := by
    intro x
    have hh := hF (G x)
    have hg := hG x
    obtain ⟨hr1,hr2⟩ := (h_OAI_StronglyRationalVOA_CircleMobiusGeometry_collinear_unit
    (h_OAI_StronglyRationalVOA_CircleMobiusGeometry_cos_sq_add_sin_sq
      ((OAI.StronglyRationalVOA.SmoothCircleLift.toOrderIso G) x / 2))
    hg)
    let r := (N 0 0*Real.cos (x/2)+N 0 1*Real.sin (x/2))*Real.cos (G x/2)+
      (N 1 0*Real.cos (x/2)+N 1 1*Real.sin (x/2))*Real.sin (G x/2)
    change r*Real.cos (G x/2)=N 0 0*Real.cos (x/2)+N 0 1*Real.sin (x/2) at hr1
    change r*Real.sin (G x/2)=N 1 0*Real.cos (x/2)+N 1 1*Real.sin (x/2) at hr2
    change (M 0 0*Real.cos (G x/2)+M 0 1*Real.sin (G x/2))*Real.sin (F (G x)/2)=
      (M 1 0*Real.cos (G x/2)+M 1 1*Real.sin (G x/2))*Real.cos (F (G x)/2) at hh
    simp only [OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Rel,(h_OAI_StronglyRationalVOA_SmoothCircleLift_mul_apply),Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Fin.sum_univ_two]
    linear_combination r*hh+(M 1 0*Real.cos (F (G x)/2)-M 0 0*Real.sin (F (G x)/2))*hr1+
      (M 1 1*Real.cos (F (G x)/2)-M 0 1*Real.sin (F (G x)/2))*hr2
  exact {
    carrier := {F | ∃ M : SL(2,ℝ), (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements M F)}
    one_mem' := ⟨1,h_OAI_StronglyRationalVOA_CircleMobiusGeometry_implements_one⟩
    mul_mem' := by rintro F G ⟨M,hM⟩ ⟨N,hN⟩; exact ⟨M*N,(h_OAI_StronglyRationalVOA_CircleMobiusGeometry_implements_mul hM hN)⟩
    inv_mem' := by rintro F ⟨M,hM⟩; exact ⟨M⁻¹,(h_OAI_StronglyRationalVOA_CircleMobiusGeometry_implements_inv hM)⟩
  }

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.rotationMatrix (s : ℝ) : SL(2,ℝ) := by
  classical
  have h_OAI_StronglyRationalVOA_CircleMobiusGeometry_cos_sq_add_sin_sq  (x : ℝ) : Real.cos x^2+Real.sin x^2=1 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  exact
    ⟨!![Real.cos (s/2),-Real.sin (s/2);Real.sin (s/2),Real.cos (s/2)],by
        simp only [Matrix.det_fin_two_of]
        nlinarith [(h_OAI_StronglyRationalVOA_CircleMobiusGeometry_cos_sq_add_sin_sq (s / 2))]⟩

noncomputable abbrev _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Group := OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.lifts ⧸ ((OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).comp OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.lifts.subtype).ker

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.inclusion : OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Group →* OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism :=
  QuotientGroup.lift ((OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).comp OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.lifts.subtype).ker
    ((QuotientGroup.mk' (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).ker).comp OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.lifts.subtype) (by
      intro F hF
      exact (QuotientGroup.eq_one_iff _).mpr hF)

end OAI.StronglyRationalVOA.CircleMobiusGeometry

namespace OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism
open Set
open scoped Topology MatrixGroups

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism.action : OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism →* Equiv.Perm (AddCircle (2*Real.pi)) :=
  QuotientGroup.lift (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).ker (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction)
    (fun _ h => h)

end OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism

namespace OAI.StronglyRationalVOA
open Set
open scoped Topology MatrixGroups

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.projectiveConjugation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : OAI.StronglyRationalVOA.ProjectiveUnitaryGroup H → ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)) := by
  classical
  have h_OAI_StronglyRationalVOA_projective_equality_conjugation  {H : Type _} [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (E F : H ≃ₗᵢ[ℂ] H)
      (h : (QuotientGroup.mk E : OAI.StronglyRationalVOA.ProjectiveUnitaryGroup H)=QuotientGroup.mk F) :
      E.conjStarAlgEquiv=F.conjStarAlgEquiv := by
    obtain ⟨c,_,hc⟩ := QuotientGroup.eq.mp h
    have he (x : H) : F x=c • E x := by
      have H := congrArg E (hc x)
      change E (E.symm (F x))=E (c • x) at H
      simpa only [E.apply_symm_apply,map_smul] using H
    ext B x
    change E (B (E.symm x))=F (B (F.symm x))
    have hi : E.symm x=c • F.symm x := by
      apply E.injective
      rw [E.apply_symm_apply,map_smul,← he,F.apply_symm_apply]
    rw [hi,map_smul,map_smul,← he]
  exact
    Quotient.lift (fun E : H ≃ₗᵢ[ℂ] H => E.conjStarAlgEquiv) (by
        intro E F h
        exact (h_OAI_StronglyRationalVOA_projective_equality_conjugation E F (Quotient.sound h)))

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.globalObservableAlgebra {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : OAI.StronglyRationalVOA.ProperCircleArc → VonNeumannAlgebra H) :
    Subalgebra ℂ (H →L[ℂ] H) :=
  Algebra.adjoin ℂ (⋃ I, (N I : Set (H →L[ℂ] H)))

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.globalCyclicSpace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : OAI.StronglyRationalVOA.ProperCircleArc → VonNeumannAlgebra H) (Ω : H) : Submodule ℂ H :=
  (Submodule.span ℂ {x | ∃ B ∈ (OAI.MinimalVertex.Code.StronglyRationalVOA.globalObservableAlgebra N), x=B Ω}).topologicalClosure

end OAI.StronglyRationalVOA

namespace OAI.StronglyRationalVOA.CFTTypeVOA
variable {V : Type u} [AddCommGroup V] [Module ℂ V] (A : CFTTypeVOA V)

noncomputable abbrev GradedDual := DirectSum ℕ (fun d => Module.Dual ℂ (A.grade d))

noncomputable def gradedDualPairing (φ : A.GradedDual) (b : V) : ℂ := by
  classical
  exact φ.sum (fun d f => f (A.gradingEquiv b d))

noncomputable def IsSelfContragredient : Prop :=
  ∃ e : V ≃ₗ[ℂ] A.GradedDual,
    ∀ d : ℕ, ∀ a ∈ A.grade d, ∀ n : ℤ, ∀ b c : V,
      A.gradedDualPairing (e (OAI.StronglyRationalVOA.mode A.fields a n b)) c =
        ((-1 : ℂ)^d) * ∑ j ∈ Finset.range (d+1), ((j.factorial : ℂ)⁻¹) *
          A.gradedDualPairing (e b)
            (OAI.StronglyRationalVOA.mode A.fields ((A.virasoroMode 1 ^ j) a) (2*(d:ℤ)-j-n-2) c)

noncomputable def IsStronglyRational : Prop :=
  A.IsSelfContragredient ∧ A.IsRational.{u,v} ∧ A.toVertexAlgebra.C2Cofinite

end OAI.StronglyRationalVOA.CFTTypeVOA

namespace OAI.MinimalVertex
open Filter Set UniformSpace
open scoped Topology MatrixGroups
open StronglyRationalVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V}

noncomputable def smearedMap (A : OAI.StronglyRationalVOA.CFTTypeVOA V) (a : V) (d : ℕ) (_ha : A.PolynomialEnergyBound a)
    (f : ℤ → ℂ) (_hf : OAI.StronglyRationalVOA.RapidCoefficients f) : V →ₗ[ℂ] Completion V := by
  classical
  let family : ℤ → (V →ₗ[ℂ] Completion V) := fun m =>
    f m • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp
      (A.physicalMode a d m)
  exact if h : ∀ v, Summable (fun m => family m v) then
    SummableLinearFamily.tsumMap family h
  else 0

noncomputable def smoothSmearedField (_U : A.UnitaryStructure) (_hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : OAI.StronglyRationalVOA.SmoothCircleFunction) : Completion V →ₗ.[ℂ] Completion V := by
  classical
  exact if h : A.PolynomialEnergyBounds ∧ OAI.StronglyRationalVOA.RapidCoefficients (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleFunction.coefficient f) then
    (OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.operator
  (OAI.MinimalVertex.smearedMap A a d (And.left h a) (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleFunction.coefficient f)
    (And.right h)))
  else 0

noncomputable def closedSmoothField (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : OAI.StronglyRationalVOA.SmoothCircleFunction) : Completion V →ₗ.[ℂ] Completion V :=
  (OAI.MinimalVertex.smoothSmearedField U hc a d f).closure

noncomputable def localGraphData (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : Set (Completion V →L[ℂ] Completion V) :=
  {x | ∃ (a : V) (d : ℕ), a ∈ A.grade d ∧ ∃ (f : OAI.StronglyRationalVOA.SmoothCircleFunction),
      tsupport (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleFunction.onCircle f) ⊆ O ∧ ∃ (h : (OAI.MinimalVertex.closedSmoothField U hc a d f).IsClosed),
        ∃ i j : Bool, x = (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.entry (OAI.MinimalVertex.closedSmoothField U hc a d f) h i j)}

noncomputable def localAlgebra (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : VonNeumannAlgebra (Completion V) :=
  (OAI.MinimalVertex.Code.StronglyRationalVOA.LocalOperatorAlgebra.generated (OAI.MinimalVertex.localGraphData U hc O))

noncomputable def intervalAlgebra (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (I : OAI.StronglyRationalVOA.ProperCircleArc) : VonNeumannAlgebra (Completion V) :=
  OAI.MinimalVertex.localAlgebra U hc (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier I)

noncomputable def CKLWStrongLocal (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite) : Prop :=
  (∀ a : V, A.PolynomialEnergyBound a) ∧
    ∀ I : OAI.StronglyRationalVOA.ProperCircleArc, OAI.MinimalVertex.intervalAlgebra U hc I ≤
      (OAI.MinimalVertex.intervalAlgebra U hc (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.complement I)).commutant

end OAI.MinimalVertex

namespace OAI.MinimalVertex
open Filter Set UniformSpace
open scoped Topology MatrixGroups
open StronglyRationalVOA
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def resolvent (T : H →ₗ.[ℂ] H) (_hs : IsSelfAdjoint T) (z : ℂ) (_hz : 1 ≤ |z.im|) :
    H →L[ℂ] H := by
  classical
  exact if h : ∃ R : H →L[ℂ] H, ∀ y, (R y, y + z • R y) ∈ T.graph then h.choose
  else 0

noncomputable def boundedGenerator (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) : H →L[ℂ] H :=
  ((r : ℂ)^2/2) •
    (OAI.MinimalVertex.resolvent T hs ((r : ℂ)*Complex.I) (by simpa [abs_of_nonneg (by linarith : 0 ≤ r)] using hr) +
     OAI.MinimalVertex.resolvent T hs (-((r : ℂ)*Complex.I)) (by simpa [abs_of_nonneg (by linarith : 0 ≤ r)] using hr))

noncomputable def approximatingFlow (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (n : ℕ) (t : ℝ) : H →L[ℂ] H :=
  (OAI.MinimalVertex.Code.StronglyRationalVOA.BoundedFlow.flow
  (Complex.I • OAI.MinimalVertex.boundedGenerator T hs (↑n + 1) (le_add_of_nonneg_left (Nat.cast_nonneg n))) t)

end OAI.MinimalVertex

namespace OAI.MinimalVertex
open Filter Set UniformSpace
open scoped Topology MatrixGroups
open StronglyRationalVOA

noncomputable def flow {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) : H →L[ℂ] H := by
  classical
  exact if h : ∃ L : H →L[ℂ] H, ∀ x,
      Tendsto (fun n => OAI.MinimalVertex.approximatingFlow T hs n t x) atTop (𝓝 (L x)) then
    h.choose
  else 0

noncomputable def projectiveStandardAction : PSL(2,ℝ) →* (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Group) := by
  classical
  exact if h : ∃ L : PSL(2,ℝ) →* (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Group),
      ∀ M : SL(2,ℝ), ∃ F : OAI.StronglyRationalVOA.SmoothCircleLift, ∃ hF : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements M F),
        L (QuotientGroup.mk M) =
          QuotientGroup.mk (⟨F, M, hF⟩ : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.lifts)) then h.choose
  else 1

structure IrreducibleConformalNetStructure {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : OAI.StronglyRationalVOA.ProperCircleArc → VonNeumannAlgebra H) where
  separable : TopologicalSpace.SeparableSpace H
  carrier_congr : ∀ I J, (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier I)=(OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier J) → N I=N J
  isotony : ∀ I J, (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier I) ⊆ (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier J) → N I ≤ N J
  locality : ∀ I J, Disjoint (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier I) (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier J) → N I ≤ (N J).commutant
  mobius : PSL(2,ℝ) →* (H ≃ₗᵢ[ℂ] H)
  mobius_continuous : Continuous mobius
  diffeomorphism : OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism →* OAI.StronglyRationalVOA.ProjectiveUnitaryGroup H
  diffeomorphism_continuous : Continuous diffeomorphism
  extends_mobius : ∀ F, diffeomorphism ((OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.inclusion) (OAI.MinimalVertex.projectiveStandardAction F))=QuotientGroup.mk (mobius F)
  covariance : ∀ F I J, (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier J)=(OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism.action) F '' (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier I) →
    ∀ B : H →L[ℂ] H, OAI.MinimalVertex.Code.StronglyRationalVOA.projectiveConjugation (diffeomorphism F) B ∈ N J ↔ B ∈ N I
  local_action : ∀ F I, (∀ x ∈ (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier I), (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism.action) F x=x) →
    ∀ B ∈ N I, OAI.MinimalVertex.Code.StronglyRationalVOA.projectiveConjugation (diffeomorphism F) B=B
  vacuum : H
  vacuum_norm : ‖vacuum‖=1
  vacuum_invariant : ∀ F, mobius F vacuum=vacuum
  vacuum_unique : ∀ x : H, (∀ F, mobius F x=x) → ∃ c : ℂ, x=c • vacuum
  vacuum_cyclic : (OAI.MinimalVertex.Code.StronglyRationalVOA.globalCyclicSpace N vacuum)=⊤
  hamiltonian : H →ₗ.[ℂ] H
  hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian
  positive_energy : ∀ x y, (x,y) ∈ hamiltonian.graph → 0 ≤ (inner ℂ x y).re
  rotation_flow : ∀ t : ℝ,
    (mobius (QuotientGroup.mk (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.rotationMatrix t))).toLinearIsometry.toContinuousLinearMap=
      OAI.MinimalVertex.flow hamiltonian hamiltonian_selfAdjoint t
  irreducible : ∀ Q : H →L[ℂ] H, (∀ I, Q ∈ (N I).commutant) →
    ∃ c : ℂ, Q=c • (1 : H →L[ℂ] H)

end OAI.MinimalVertex

namespace OAI.MinimalVertex
open Filter Set UniformSpace
open scoped Topology MatrixGroups
open StronglyRationalVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)



end OAI.MinimalVertex
end


