-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
-- name    : ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:48.589797+00:00
-- url     : https://prove2.me/theorems/4bb672b2-8621-43fb-a07b-f92ed154a8d7
-- title:
--   Comap Inclusion Is Local Hom
-- statement:
--   Definitions and structural lemmas for Comap Inclusion Is Local Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ComapInclusionIsLocalHom.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.MultiplicativeHeights
open scoped TensorProduct
def JetCountStatement : Prop :=
  ∀ (K : Type) [Field K] (D e : ℕ),
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin D) K e) = (e + D).choose D ∧
      Nat.card {α : Fin D →₀ ℕ // α.degree ≤ e} = (e + D).choose D
def JetRatioStatement : Prop :=
  ∀ n k D : ℕ, k + D ≤ n →
    (1 - (D : ℝ) * k / ((n - D + 1 : ℕ) : ℝ)) * ((n.choose D : ℕ) : ℝ) ≤ (((n - k).choose D : ℕ) : ℝ)
def RankStatement : Prop :=
  ∀ (K L V : Type) [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) (ι : Type) (v : ι → V),
    (∀ i, v i ∈ W) →
    Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[K] v i) = ⊤ →
    W = ⊤ ∧ Submodule.span K (Set.range v) = ⊤
noncomputable def torusSum {K : Type*} [NormedField K] {n : ℕ} (c : (Fin n → ℤ) → K)
    (τ : Fin n → K) : K :=
  ∑' χ, c χ * ∏ i, τ i ^ χ i
def ResidueFieldInfiniteOn {K : Type*} [NormedField K] (S : Set K) : Prop :=
  ∀ s : Finset K, ∃ x ∈ S, ‖x‖ ≤ 1 ∧ ∀ y ∈ s, 1 ≤ ‖x - y‖
def CauchyTorusStatement : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (K₀ : Subfield K),
    ResidueFieldInfiniteOn (K₀ : Set K) →
    ∀ (n : ℕ) (c : (Fin n → ℤ) → K),
      Filter.Tendsto (fun χ => ‖c χ‖) Filter.cofinite (nhds 0) →
      (∀ τ : Fin n → K, (∀ i, τ i ∈ K₀ ∧ ‖τ i‖ = 1) → ‖torusSum c τ‖ ≤ 1) →
      ∀ χ, ‖c χ‖ ≤ 1
def NormLengthStatement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B] [IsDomain B]
    [Algebra O B] [Module.Finite O B] [NoZeroSMulDivisors O B] (g : B),
    g ≠ 0 →
      IsDiscreteValuationRing.addVal O (Algebra.norm O g) =
        Module.length O (B ⧸ Ideal.span {g})
def NormOrdStatement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B] [IsDomain B]
    [IsDedekindDomain B] [Algebra O B] [Module.Finite O B] [NoZeroSMulDivisors O B] (g : B),
    g ≠ 0 →
      IsDiscreteValuationRing.addVal O (Algebra.norm O g) =
        ((∑ᶠ Q : {Q : Ideal B // Q.IsMaximal},
          Q.1.inertiaDeg O *
            Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {g})) :
          ℕ) : ℕ∞)
def comapInclusion {F₁ F₂ : Type*} [Field F₁] [Field F₂] (V : ValuationSubring F₂)
    (f : F₁ →+* F₂) : V.comap f →+* V :=
  f.restrict (V.comap f) V fun _ hx => hx
instance comapInclusion_isLocalHom {F₁ F₂ : Type*} [Field F₁] [Field F₂]
    (V : ValuationSubring F₂) (f : F₁ →+* F₂) : IsLocalHom (comapInclusion V f) := by
  constructor
  intro x hx
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hx
  have hu' : f (x : F₁) * (u : F₂) = 1 := congrArg Subtype.val hu
  have hx0 : (x : F₁) ≠ 0 := fun h => zero_ne_one (by rw [h, map_zero, zero_mul] at hu'; exact hu')
  have hinv : f ((x : F₁)⁻¹) = (u : F₂) := by rw [map_inv₀]; exact inv_eq_of_mul_eq_one_right hu'
  have hmem : (x : F₁)⁻¹ ∈ V.comap f := by rw [ValuationSubring.mem_comap, hinv]; exact u.2
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩
noncomputable abbrev residueAlgebra {F₁ F₂ : Type*} [Field F₁] [Field F₂]
    (V : ValuationSubring F₂) (f : F₁ →+* F₂) :
    Algebra (IsLocalRing.ResidueField (V.comap f)) (IsLocalRing.ResidueField V) :=
  (IsLocalRing.ResidueField.map (comapInclusion V f)).toAlgebra
def TRStatement : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] [Algebra F₁ F₂] (V : ValuationSubring F₂),
    letI := residueAlgebra V (algebraMap F₁ F₂)
    Algebra.trdeg (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (IsLocalRing.ResidueField V) ≤ Algebra.trdeg F₁ F₂
def DedekindRankStatement : Prop :=
  ∀ (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F]
    [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [Algebra O L] [IsScalarTower O F L],
    IsDedekindDomain (integralClosure O L) ∧ Module.Finite O (integralClosure O L) ∧
      Module.Free O (integralClosure O L) ∧
      Module.finrank O (integralClosure O L) = Module.finrank F L ∧
      {Q : Ideal (integralClosure O L) | Q.IsMaximal}.Finite ∧
      ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal},
          Q.1.ramificationIdx O * Q.1.inertiaDeg O = Module.finrank F L
abbrev SVars (D m : ℕ) : Type := Unit ⊕ (Fin (D + 1) × Fin m)
abbrev SField (Ω : Type) [Field Ω] (D m : ℕ) : Type :=
  FractionRing (MvPolynomial (SVars D m) Ω)
noncomputable def sImage {Ω : Type} [Field Ω] {D m : ℕ} (x : Fin m → Ω) :
    Fin (D + 1) × Fin (m + 1) → SField Ω D m :=
  fun p => algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m)
    (Fin.cases (motive := fun _ => MvPolynomial (SVars D m) Ω)
      (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (x k))
      (fun j => MvPolynomial.X (Sum.inr (p.1, j))) p.2)
def FieldOfSStatement : Prop :=
  ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] (D m : ℕ) (x : Fin m → Ω),
    (⊤ : IntermediateField K Ω).FG → Algebra.trdeg K Ω = D →
    (∃ J : Fin D → Fin m,
      LinearIndependent Ω fun a => KaehlerDifferential.D K Ω (x (J a))) →
    AlgebraicIndependent K (sImage (D := D) x) ∧
      FiniteDimensional (IntermediateField.adjoin K (Set.range (sImage (D := D) x)))
        (SField Ω D m)
def GaussExtStatement : Prop :=
  ∀ (Ω U : Type) [Field Ω] [Field U] [Algebra Ω U] (σ : Type) [Finite σ] (t : σ → U),
    AlgebraicIndependent Ω t → IntermediateField.adjoin Ω (Set.range t) = ⊤ →
    ∀ (V : ValuationSubring U) (ht : ∀ s, t s ∈ V),
      letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) →
      (∀ p : MvPolynomial σ Ω, V.valuation (MvPolynomial.aeval t p) =
          p.support.sup fun α => V.valuation (algebraMap Ω U (p.coeff α))) ∧
      (∀ ϖ : Ω, ϖ ≠ 0 → ϖ ∈ (V.comap (algebraMap Ω U)).nonunits →
          (∀ y ∈ (V.comap (algebraMap Ω U)).nonunits, y / ϖ ∈ V.comap (algebraMap Ω U)) →
          ∀ z ∈ V.nonunits, z / algebraMap Ω U ϖ ∈ V) ∧
      (∀ (V' : ValuationSubring U) (ht' : ∀ s, t s ∈ V'),
          V'.comap (algebraMap Ω U) = V.comap (algebraMap Ω U) →
          letI := residueAlgebra V' (algebraMap Ω U)
          AlgebraicIndependent (IsLocalRing.ResidueField (V'.comap (algebraMap Ω U)))
            (fun s => IsLocalRing.residue V' ⟨t s, ht' s⟩) →
          V' = V)
def ResidueTrdegStatement : Prop :=
  ∀ (K Ω U : Type) [Field K] [Field Ω] [Field U] [Algebra K Ω] [Algebra Ω U] (D : ℕ),
    Algebra.trdeg K Ω = D →
    ∀ (σ : Type) [Fintype σ] (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
      (τ : Type) [Fintype τ] (u : τ → V) (p : τ → MvPolynomial σ Ω)
      (hp : ∀ j α, (p j).coeff α ∈ V.comap (algebraMap Ω U)),
      Fintype.card τ = Fintype.card σ + D → (∀ j, MvPolynomial.aeval t (p j) = (u j : U)) →
      letI _iW := residueAlgebra V (algebraMap Ω U)
      letI _io := residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
      letI : Algebra (IsLocalRing.ResidueField
          ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (IsLocalRing.ResidueField V) :=
        ((algebraMap _ (IsLocalRing.ResidueField V)).comp
          (algebraMap _ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
      AlgebraicIndependent
          (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
          (fun j => IsLocalRing.residue V (u j)) →
      (∀ k₁ : IntermediateField
          (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
          (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))),
        (∀ j α, IsLocalRing.residue _ ⟨(p j).coeff α, hp j α⟩ ∈ k₁) →
        Algebra.trdeg
          (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) k₁ = D) ∧
      Algebra.trdeg
          (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
          (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) = D ∧
        AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
          (fun s => IsLocalRing.residue V ⟨t s, ht s⟩)
def LatticeCoordStatement : Prop :=
  (∀ (Ω : Type) [Field Ω] (ι : Type) [Finite ι] (W : ι → ValuationSubring Ω),
      (∀ i, IsDiscreteValuationRing (W i)) →
      IsPrincipalIdealRing (⨅ i, (W i).toSubring : Subring Ω) ∧
        IsFractionRing (⨅ i, (W i).toSubring : Subring Ω) Ω ∧
        {M : Ideal (⨅ i, (W i).toSubring : Subring Ω) | M.IsMaximal}.Finite ∧
        (∀ i, ∀ x ∈ W i, ∃ a s : (⨅ i, (W i).toSubring : Subring Ω),
          (W i).valuation (s : Ω) = 1 ∧ x * s = a) ∧
        (Nonempty ι → ∀ M : Ideal (⨅ i, (W i).toSubring : Subring Ω), M.IsMaximal →
          ∃ i, ∀ x, x ∈ M ↔ (W i).valuation (x : Ω) < 1)) ∧
  (∀ (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (N : ℕ) (v : Fin (N + 1) → R),
      Ideal.span (Set.range v) = ⊤ →
      ∃ A : Matrix (Fin (N + 1)) (Fin (N + 1)) R, IsUnit A ∧ ∀ j, A 0 j = v j) ∧
  (∀ (F : Type) [Field F] (A B : Subring F), A ≤ B →
      (∀ m : Ideal A, m.IsMaximal → ∀ b ∈ B, ∃ a s : A, s ∉ m ∧ b * (s : F) = a) → A = B)
def GradedFreeStatement : Prop :=
  (∀ (B : Type) [CommRing B] (D : ℕ) (S : Submonoid (MvPolynomial (Fin D) B)) (a : ℕ)
      (r : (Fin D →₀ ℕ) →₀ Localization S),
      (∀ α ∈ r.support, α.degree = a) →
      (r.sum fun α c => c * algebraMap (MvPolynomial (Fin D) B) (Localization S)
          (MvPolynomial.monomial α 1)) ∈
        (Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin D) B) (Localization S)
          (MvPolynomial.X i))) ^ (a + 1) →
      ∀ α, r α ∈ Ideal.span (Set.range fun i =>
          algebraMap (MvPolynomial (Fin D) B) (Localization S) (MvPolynomial.X i))) ∧
  (∀ (R : Type) [CommRing R] (J : Ideal R) (u : R) (k : ℕ),
      IsUnit (Ideal.Quotient.mk J u) → IsUnit (Ideal.Quotient.mk (J ^ (k + 1)) u))
end ReciprocityTheory.MultiplicativeHeights


