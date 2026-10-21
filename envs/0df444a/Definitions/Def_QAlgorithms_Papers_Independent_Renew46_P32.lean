-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32
-- name    : QAlgorithms_Papers_Independent_Renew46_P32
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T03:08:55.532812+00:00
-- url     : https://prove2.me/theorems/dcbe8d13-7836-45a3-b604-26a023a2bc64
-- title:
--   Definitions for Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields
-- statement:
--   The objects the formalized statements of *Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields* (arXiv:math/0303300) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsScalarHomogeneous`: Appendix A, PDF p. 64: scalar homogeneity, including degree zero.
--   - `linearization`: Appendix A, PDF p. 64: iterated finite differences, before imposing any linearity, topology, or scalar homogeneity.
--   - `IsMultiadditive`: Appendix A, PDF p. 65: additivity separately in every argument. At arity zero this imposes no conditions, which is why Proposition A.3 uses k>0.
--   - `IsHomogeneousForm`: Definition A.1, PDF p. 64: a form is homogeneous and its k-th linearization at zero is multilinear; no diagonal representation is assumed.
--   - `IsHomogeneousPolynomial`: Definition A.5, PDF p. 66: quantify over every free-module surjection. This is distinct from merely asking for a multilinear diagonal on E itself.
--   - `jetDomain`: Definition 2.1, PDF p. 10, specialized as in Part III, PDF p. 48. Triple association is x,(v,t), and the entire domain is retained.
--   - `fieldCk`: Definitions 2.1/4.1, PDF pp. 10,16: recursive continuous extended difference quotients in the topological-field concept of Part III (p. 48). Successor regularity requires a quotient on ALL of U^[1], including t=0. The quotient is constrained by the difference identity, not by a prescribed derivative or by the theorem being stated. All model-type parameters are explicit binders so recursion may pass from E to E × E × K.
--   - `fieldCr`: Finite or infinite order, PDF p. 48. Lower finite orders are included; this is equivalent to the recursive finite-order definition on open domains.
--   - `fieldSmooth`: Smoothness, Definition 4.1, PDF p. 16: every finite order.
--   - `rawCurve`: Definition 6.3, PDF p. 27: the raw curve divided difference. Outside the pairwise-distinct domain this total function has no claimed meaning.
--   - `distinctTuples`: Distinct-tuple domain from Definition 6.3, PDF p. 27.
--   - `fieldSchikhof`: Definition 6.3 in the topological-field concept: existence of the highest continuous extension alone, with no lower-order implications built in.
--   - `subspaceCorestriction`: Lemma 10.1, PDF p. 48: co-restrict on U; the value outside U is zero and never enters a regularity conclusion on U.
--   - `alternatingSequence`: Interleaving in Lemma 10.8, PDF p. 51; subsequences use strictly increasing indices.
--   - `projectiveLimitSubmodule`: Lemma 10.3, PDF p. 49: compatible tuples form the actual inverse-limit subspace of the product. No surjectivity of the bonding maps is required.
--   - `IsUltrametricField`: The strong triangle inequality, with the norm inducing the field topology.
--   - `IsRealOrUltrametric`: The field alternatives in Theorems 11.3 and 12.4. The real case is transported by a norm-preserving field isomorphism, ensuring the usual topology.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, https://arxiv.org/abs/math/0303300v1

import Mathlib

/-!
Bertram--Glockner--Neeb, arXiv:math/0303300v1.
The new definitions below implement the topological-field specialization of
Definitions 2.1/4.1 and the algebraic Appendix A. They do not identify that
specialization with the arbitrary C^0-concepts of Parts I--II.
All theorem proofs are intentionally deferred. Compilation is pending handoff.
-/

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

section AlgebraicDefinitions

variable {K : Type u} [CommRing K]
variable {E : Type u} [AddCommGroup E] [Module K E]
variable {F : Type u} [AddCommGroup F] [Module K F]

/-- Appendix A, PDF p. 64: scalar homogeneity, including degree zero. -/
def IsScalarHomogeneous (k : ℕ) (q : E → F) : Prop :=
  ∀ t : K, ∀ x : E, q (t • x) = t ^ k • q x

/-- Appendix A, PDF p. 64: iterated finite differences, before imposing any
linearity, topology, or scalar homogeneity. -/
def linearization {A : Type u} [AddCommGroup A]
    {B : Type u} [AddCommGroup B] (q : A → B) (x : A) :
    (k : ℕ) → (Fin k → A) → B
  | 0, _ => q x
  | k + 1, h => linearization (fun y => q (y + h 0) - q y) x k (Fin.tail h)

/-- Appendix A, PDF p. 65: additivity separately in every argument. At
arity zero this imposes no conditions, which is why Proposition A.3 uses k>0. -/
def IsMultiadditive {A : Type u} [AddCommGroup A]
    {B : Type u} [AddCommGroup B] {k : ℕ} (m : (Fin k → A) → B) : Prop :=
  ∀ (i : Fin k) (h : Fin k → A) (a b : A),
    m (Function.update h i (a + b)) =
      m (Function.update h i a) + m (Function.update h i b)

/-- Definition A.1, PDF p. 64: a form is homogeneous and its k-th
linearization at zero is multilinear; no diagonal representation is assumed. -/
def IsHomogeneousForm (k : ℕ) (q : E → F) : Prop :=
  IsScalarHomogeneous (K := K) k q ∧
    ∃ m : MultilinearMap K (fun _ : Fin k => E) F,
      ∀ h, m h = linearization q 0 k h

/-- Definition A.5, PDF p. 66: quantify over every free-module surjection.
This is distinct from merely asking for a multilinear diagonal on E itself. -/
def IsHomogeneousPolynomial (k : ℕ) (q : E → F) : Prop :=
  ∀ (D : Type u) [AddCommGroup D] [Module K D] [Module.Free K D],
    ∀ phi : D →ₗ[K] E, Function.Surjective phi →
      ∃ m : MultilinearMap K (fun _ : Fin k => D) F,
        ∀ x : D, q (phi x) = m (fun _ => x)

/-- Sanity: the zeroth linearization is evaluation, including at zero. -/
example (q : E → F) (x : E) (h : Fin 0 → E) :
    linearization q x 0 h = q x := rfl

/-- Sanity: the first finite difference has the source's forward sign. -/
example (q : E → F) (x h : E) :
    linearization q x 1 (fun _ => h) = q (x + h) - q x := rfl

/-- Sanity: constants are homogeneous of degree zero, with 0^0=1. -/
example (b : F) : IsScalarHomogeneous (K := K) 0 (fun _ : E => b) := by
  intro t x
  simp

/-- Sanity: the zero polynomial meets the EVERY-surjection quantifier. -/
example (k : ℕ) : IsHomogeneousPolynomial (K := K) k (fun _ : E => (0 : F)) := by
  intro D _ _ _ phi hphi
  exact ⟨0, fun _ => rfl⟩

/-- Sanity: zero-argument additivity has no constraints. -/
example {A : Type u} [AddCommGroup A] {B : Type u} [AddCommGroup B]
    (m : (Fin 0 → A) → B) : IsMultiadditive m := by
  intro i
  exact Fin.elim0 i

/-- Sanity: degree-zero forms include every constant, not just zero. -/
example (b : F) : IsHomogeneousForm (K := K) 0 (fun _ : E => b) := by
  refine ⟨?_, MultilinearMap.constOfIsEmpty (R := K) (fun _ : Fin 0 => E) b, ?_⟩
  · intro t x
    simp
  · intro h
    rfl

end AlgebraicDefinitions

section TopologicalCalculusDefinitions

variable {K : Type} [Field K] [TopologicalSpace K]
variable {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
variable {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F]

/-- Definition 2.1, PDF p. 10, specialized as in Part III, PDF p. 48.
Triple association is x,(v,t), and the entire domain is retained. -/
def jetDomain (U : Set E) : Set (E × E × K) :=
  {z | z.1 ∈ U ∧ z.1 + z.2.2 • z.2.1 ∈ U}

/-- Definitions 2.1/4.1, PDF pp. 10,16: recursive continuous extended
difference quotients in the topological-field concept of Part III (p. 48).
Successor regularity requires a quotient on ALL of U^[1], including t=0.
The quotient is constrained by the difference identity, not by a prescribed
derivative or by the theorem being stated. All model-type parameters are
explicit binders so recursion may pass from E to E × E × K. -/
def fieldCk {K : Type} [Field K] [TopologicalSpace K] (n : ℕ)
    {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F]
    (U : Set E) (f : E → F) : Prop :=
  match n with
  | 0 => ContinuousOn f U
  | n + 1 => ContinuousOn f U ∧
      ∃ g : (E × E × K) → F,
        fieldCk (K := K) n (E := E × E × K) (F := F)
          (jetDomain (K := K) U) g ∧
          ∀ z ∈ jetDomain (K := K) U,
            f (z.1 + z.2.2 • z.2.1) - f z.1 = z.2.2 • g z
termination_by n

/-- Finite or infinite order, PDF p. 48. Lower finite orders are included;
this is equivalent to the recursive finite-order definition on open domains. -/
def fieldCr (r : WithTop ℕ) (U : Set E) (f : E → F) : Prop :=
  ∀ n : ℕ, (n : WithTop ℕ) ≤ r → fieldCk (K := K) n U f

/-- Smoothness, Definition 4.1, PDF p. 16: every finite order. -/
def fieldSmooth (U : Set E) (f : E → F) : Prop :=
  ∀ n : ℕ, fieldCk (K := K) n U f

/-- Definition 6.3, PDF p. 27: the raw curve divided difference. Outside
the pairwise-distinct domain this total function has no claimed meaning. -/
def rawCurve (f : K → F) : (n : ℕ) → (Fin (n + 1) → K) → F
  | 0, t => f (t 0)
  | n + 1, t => (t 0 - t 1)⁻¹ •
      (rawCurve f n (Fin.cons (t 0) (Fin.tail (Fin.tail t))) -
        rawCurve f n (Fin.tail t))

/-- Distinct-tuple domain from Definition 6.3, PDF p. 27. -/
def distinctTuples (U : Set K) (n : ℕ) : Set (Fin (n + 1) → K) :=
  {t | (∀ i, t i ∈ U) ∧ Function.Injective t}

/-- Definition 6.3 in the topological-field concept: existence of the
highest continuous extension alone, with no lower-order implications built in. -/
def fieldSchikhof (n : ℕ) (U : Set K) (f : K → F) : Prop :=
  ∃ g : (Fin (n + 1) → K) → F,
    ContinuousOn g {t | ∀ i, t i ∈ U} ∧
      Set.EqOn g (rawCurve f n) (distinctTuples U n)

/-- Lemma 10.1, PDF p. 48: co-restrict on U; the value outside U is zero
and never enters a regularity conclusion on U. -/
noncomputable def subspaceCorestriction (S : Submodule K F) (U : Set E)
    (f : E → F) (hf : ∀ x ∈ U, f x ∈ S) : E → S := by
  classical
  exact fun x => if hx : x ∈ U then ⟨f x, hf x hx⟩ else 0

/-- Sanity: quotient triples with zero scalar require exactly x∈U. -/
example (U : Set E) (x v : E) :
    (x, v, (0 : K)) ∈ jetDomain (K := K) U ↔ x ∈ U := by
  simp [jetDomain]

/-- Sanity: order zero is precisely continuity, with no derivative condition. -/
example (U : Set E) (f : E → F) :
    fieldCk (K := K) 0 U f ↔ ContinuousOn f U := by
  simp only [fieldCk]

/-- Sanity: the first raw divided difference has denominator t0-t1. -/
example (f : K → F) (t : Fin 2 → K) :
    rawCurve f 1 t = (t 0 - t 1)⁻¹ • (f (t 0) - f (t 1)) := rfl

/-- Sanity: co-restriction agrees with the original map at each domain point. -/
example (S : Submodule K F) (U : Set E) (f : E → F)
    (hf : ∀ x ∈ U, f x ∈ S) (x : E) (hx : x ∈ U) :
    (subspaceCorestriction S U f hf x : F) = f x := by
  simp [subspaceCorestriction, hx]

/-- Sanity: a constant curve has a zeroth Schikhof extension. -/
example (b : F) : fieldSchikhof 0 (Set.univ : Set K) (fun _ => b) := by
  refine ⟨fun _ => b, continuousOn_const, ?_⟩
  intro t ht
  rfl

/-- Sanity: a one-point tuple has no distinctness exclusion. -/
example (t : Fin 1 → K) : t ∈ distinctTuples (Set.univ : Set K) 0 := by
  constructor
  · intro i
    trivial
  · intro i j hij
    apply Fin.ext
    omega

/-- Sanity: infinity means all finite orders, not an independent label. -/
example (U : Set E) (f : E → F) :
    fieldCr (K := K) ⊤ U f ↔ fieldSmooth (K := K) U f := by
  constructor
  · intro h n
    exact h n le_top
  · intro h n hn
    exact h n

/-- Sanity: smoothness includes continuity at order zero. -/
example (U : Set E) (f : E → F) (hf : fieldSmooth (K := K) U f) :
    ContinuousOn f U := by
  simpa only [fieldCk] using hf 0

/-- Sanity: the zero map has a genuine first quotient on the full domain. -/
example (U : Set E) : fieldCk (K := K) 1 U (fun _ : E => (0 : F)) := by
  simp only [fieldCk]
  refine ⟨continuousOn_const, (fun _ : E × E × K => (0 : F)),
    continuousOn_const, ?_⟩
  intro z hz
  simp

end TopologicalCalculusDefinitions

/-- Interleaving in Lemma 10.8, PDF p. 51; subsequences use strictly
increasing indices. -/
def alternatingSequence {Y : Type v} (a b : ℕ → Y) (n : ℕ) : Y :=
  if Even n then a (n / 2) else b (n / 2)

/-- Sanity: the interleaving begins with the first sequence. -/
example {Y : Type v} (a b : ℕ → Y) : alternatingSequence a b 0 = a 0 := by
  simp [alternatingSequence]

section TopologicalFieldResults

variable {K : Type} [Field K] [TopologicalSpace K]
variable [hKTop : IsTopologicalDivisionRing K] [hKT2 : T2Space K]
variable (hNonDiscrete : ¬ DiscreteTopology K)
variable {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
variable [hETop : IsTopologicalAddGroup E] [hESmul : ContinuousSMul K E] [hET2 : T2Space E]
variable {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F]
variable [hFTop : IsTopologicalAddGroup F] [hFSmul : ContinuousSMul K F] [hFT2 : T2Space F]
include hKTop hKT2 hNonDiscrete hETop hESmul hET2 hFTop hFSmul hFT2

end TopologicalFieldResults

/-- Lemma 10.3, PDF p. 49: compatible tuples form the actual inverse-limit
subspace of the product. No surjectivity of the bonding maps is required. -/
def projectiveLimitSubmodule
    {K : Type} [Field K] {I : Type u} [Preorder I]
    {F : I → Type u} [∀ i, AddCommGroup (F i)] [∀ i, Module K (F i)]
    (bond : ∀ i j : I, i ≤ j → F j →ₗ[K] F i) : Submodule K (∀ i, F i) where
  carrier := {a | ∀ i j h, bond i j h (a j) = a i}
  zero_mem' := by
    intro i j h
    exact map_zero (bond i j h)
  add_mem' := by
    intro a b ha hb i j h
    change bond i j h (a j + b j) = a i + b i
    rw [map_add, ha i j h, hb i j h]
  smul_mem' := by
    intro c a ha i j h
    change bond i j h (c • a j) = c • a i
    rw [map_smul, ha i j h]

/-- Sanity: the zero tuple is in the limit, even for an empty index type. -/
example {K : Type} [Field K] {I : Type u} [Preorder I]
    {F : I → Type u} [∀ i, AddCommGroup (F i)] [∀ i, Module K (F i)]
    (bond : ∀ i j : I, i ≤ j → F j →ₗ[K] F i) :
    (0 : ∀ i, F i) ∈ projectiveLimitSubmodule bond :=
  (projectiveLimitSubmodule bond).zero_mem

section CurveExtensionResults

variable {K : Type} [Field K] [TopologicalSpace K]
variable [hKTop : IsTopologicalDivisionRing K] [hKT2 : T2Space K]
variable (hNonDiscrete : ¬ DiscreteTopology K)
variable {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
variable [hETop : IsTopologicalAddGroup E] [hESmul : ContinuousSMul K E] [hET2 : T2Space E]
include hKTop hKT2 hNonDiscrete hETop hESmul hET2

end CurveExtensionResults

/-- The strong triangle inequality, with the norm inducing the field topology. -/
def IsUltrametricField (K : Type u) [NormedField K] : Prop :=
  ∀ a b : K, ‖a + b‖ ≤ max ‖a‖ ‖b‖

/-- Sanity: the ordinary real norm is not ultrametric. -/
example : ¬ IsUltrametricField ℝ := by
  intro h
  have hh := h 1 1
  norm_num at hh

/-- The field alternatives in Theorems 11.3 and 12.4. The real case is
transported by a norm-preserving field isomorphism, ensuring the usual topology. -/
def IsRealOrUltrametric (K : Type u) [NormedField K] : Prop :=
  (∃ e : K ≃+* ℝ, ∀ a : K, ‖a‖ = |e a|) ∨ IsUltrametricField K

/-- Sanity: R with its usual norm belongs to the real alternative. -/
example : IsRealOrUltrametric ℝ := by
  left
  exact ⟨RingEquiv.refl ℝ, fun a => Real.norm_eq_abs a⟩

end QAlgorithms.Papers.Independent.Renew46.P32


