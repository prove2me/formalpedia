-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:31.401968+00:00
-- url     : https://prove2.me/theorems/8745dfa1-69f8-4be5-8e77-5222764fd966
-- title:
--   Etale Coordinates
-- statement:
--   Definitions and structural lemmas for Etale Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleCoordinates.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
section
variable [Algebra (MvPolynomial ι k) S]
noncomputable def coord (i : ι) : S := algebraMap (MvPolynomial ι k) S (MvPolynomial.X i)
end
section
variable [Algebra (MvPolynomial ι k) S] [Algebra k S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
include ι
theorem exists_basisKaehler :
    ∃ b : Module.Basis ι S (KaehlerDifferential k S),
      ∀ i : ι, b i = KaehlerDifferential.D k S (coord k ι S i) := by
  have h : IsBaseChange S (KaehlerDifferential.map k k (MvPolynomial ι k) S) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale k (MvPolynomial ι k) S
  refine ⟨(Algebra.TensorProduct.basis S
    (KaehlerDifferential.mvPolynomialBasis k ι)).map h.equiv, fun i => ?_⟩
  simp only [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, IsBaseChange.equiv_tmul, one_smul,
    KaehlerDifferential.map_D]
  rfl
noncomputable def basisKaehler : Module.Basis ι S (KaehlerDifferential k S) :=
  (exists_basisKaehler k ι S).choose
@[simp] theorem basisKaehler_apply (i : ι) :
    basisKaehler k ι S i = KaehlerDifferential.D k S (coord k ι S i) :=
  (exists_basisKaehler k ι S).choose_spec i
noncomputable def partialDerivFun (i : ι) (s : S) : S :=
  (basisKaehler k ι S).repr (KaehlerDifferential.D k S s) i
theorem partialFun_map_add (i : ι) :
    ∀ x y : S, partialDerivFun k ι S i (x + y) = partialDerivFun k ι S i x + partialDerivFun k ι S i y := by
  intro x y
  show (basisKaehler k ι S).repr (KaehlerDifferential.D k S (x + y)) i
      = (basisKaehler k ι S).repr (KaehlerDifferential.D k S x) i
        + (basisKaehler k ι S).repr (KaehlerDifferential.D k S y) i
  rw [map_add, map_add, Finsupp.add_apply]
theorem partialFun_map_smul (i : ι) :
    ∀ (c : k) (x : S),
      partialDerivFun k ι S i (c • x) = (RingHom.id k) c • partialDerivFun k ι S i x := by
  intro c x
  have h1 : c • x = algebraMap k S c * x := Algebra.smul_def c x
  have h2 : KaehlerDifferential.D k S (c • x)
      = algebraMap k S c • KaehlerDifferential.D k S x := by
    rw [h1, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]
  show (basisKaehler k ι S).repr (KaehlerDifferential.D k S (c • x)) i
      = c • (basisKaehler k ι S).repr (KaehlerDifferential.D k S x) i
  rw [h2, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, ← Algebra.smul_def]
noncomputable def partialDerivLinear (i : ι) : S →ₗ[k] S where
  toFun := partialDerivFun k ι S i
  map_add' := partialFun_map_add k ι S i
  map_smul' := partialFun_map_smul k ι S i
theorem partialLinear_leibniz (i : ι) :
    ∀ a b : S, partialDerivLinear k ι S i (a * b)
      = a • partialDerivLinear k ι S i b + b • partialDerivLinear k ι S i a := by
  intro a b
  have h : KaehlerDifferential.D k S (a * b)
      = a • KaehlerDifferential.D k S b + b • KaehlerDifferential.D k S a :=
    (KaehlerDifferential.D k S).leibniz a b
  have h2 : (basisKaehler k ι S).repr (KaehlerDifferential.D k S (a * b)) i
      = a * (basisKaehler k ι S).repr (KaehlerDifferential.D k S b) i
        + b * (basisKaehler k ι S).repr (KaehlerDifferential.D k S a) i := by
    rw [h, map_add, Finsupp.add_apply, LinearEquiv.map_smul, LinearEquiv.map_smul,
      Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
  exact h2
noncomputable def partialDeriv (i : ι) : Derivation k S S :=
  Derivation.mk' (partialDerivLinear k ι S i) (partialLinear_leibniz k ι S i)
theorem partialDeriv_apply (i : ι) (s : S) :
    partialDeriv k ι S i s = (basisKaehler k ι S).repr (KaehlerDifferential.D k S s) i := rfl
@[simp] theorem partialDeriv_coord [DecidableEq ι] (i j : ι) :
    partialDeriv k ι S i (coord k ι S j) = if i = j then (1 : S) else 0 := by
  rw [partialDeriv_apply, ← basisKaehler_apply k ι S j, Module.Basis.repr_self,
    Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl
theorem partialDeriv_coord_self (i : ι) :
    partialDeriv k ι S i (coord k ι S i) = 1 := by
  rw [partialDeriv_apply, ← basisKaehler_apply k ι S i, Module.Basis.repr_self,
    Finsupp.single_eq_same]
theorem partialDeriv_coord_of_ne (i j : ι) (h : i ≠ j) :
    partialDeriv k ι S i (coord k ι S j) = 0 := by
  classical
  rw [partialDeriv_coord k ι S i j, if_neg h]
omit [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S] in
theorem sum_smul_derivation_apply (c : ι → S) (f : ι → Derivation k S S)
    (s : S) (t : Finset ι) :
    (∑ i ∈ t, c i • f i) s = ∑ i ∈ t, c i * f i s := by
  induction t using Finset.cons_induction_on
  · simp
  · rename_i a u hu ih
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    rfl
theorem span_range_partialDeriv [Finite ι] :
    Submodule.span S (Set.range (partialDeriv k ι S)) = (⊤ : Submodule S (Derivation k S S)) := by
  obtain ⟨hι⟩ := nonempty_fintype ι
  refine Submodule.eq_top_iff'.mpr fun D => ?_
  have key : D = ∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i := by
    ext s
    have h1 : ∑ i : ι, partialDeriv k ι S i s • KaehlerDifferential.D k S (coord k ι S i)
        = KaehlerDifferential.D k S s := by
      rw [← Module.Basis.sum_repr (basisKaehler k ι S) (KaehlerDifferential.D k S s)]
      exact Finset.sum_congr rfl fun i _ => by rw [basisKaehler_apply, partialDeriv_apply]
    have h2 : D.liftKaehlerDifferential
        (∑ i : ι, partialDeriv k ι S i s • KaehlerDifferential.D k S (coord k ι S i))
        = D.liftKaehlerDifferential (KaehlerDifferential.D k S s) := by rw [h1]
    simp only [map_sum, map_smul, Derivation.liftKaehlerDifferential_comp_D] at h2
    rw [sum_smul_derivation_apply, ← h2]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  rw [key]
  exact sum_mem fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
theorem exists_basisDerivation [Fintype ι] [DecidableEq ι] :
    ∃ b : Module.Basis ι S (Derivation k S S), ∀ i : ι, b i = partialDeriv k ι S i := by
  have hli : LinearIndependent S (partialDeriv k ι S) := by
    rw [linearIndependent_iff']
    intro s g hg j hj
    have h0 : (∑ i ∈ s, g i • partialDeriv k ι S i) (coord k ι S j) = 0 := by
      rw [hg]
      simp
    rw [sum_smul_derivation_apply k ι S g (partialDeriv k ι S)
      (coord k ι S j) s] at h0
    have key : ∑ i ∈ s, g i * partialDeriv k ι S i (coord k ι S j)
        = g j * partialDeriv k ι S j (coord k ι S j) := by
      refine Finset.sum_eq_single j ?_ ?_
      · intro i _ hij
        rw [partialDeriv_coord_of_ne k ι S i j hij, mul_zero]
      · intro hj'
        exact absurd hj hj'
    rw [key, partialDeriv_coord_self, mul_one] at h0
    exact h0
  have hsp : ⊤ ≤ Submodule.span S (Set.range (partialDeriv k ι S)) :=
    (span_range_partialDeriv k ι S).ge
  exact ⟨Module.Basis.mk hli hsp, fun i => Module.Basis.mk_apply hli hsp i⟩
noncomputable def basisDerivation [Fintype ι] [DecidableEq ι] :
    Module.Basis ι S (Derivation k S S) :=
  (exists_basisDerivation k ι S).choose
end
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution


