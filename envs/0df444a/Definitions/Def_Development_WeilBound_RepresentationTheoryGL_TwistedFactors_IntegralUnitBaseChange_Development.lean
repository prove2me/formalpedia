-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
-- name    : Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:08.710627+00:00
-- url     : https://prove2.me/theorems/ca0569ff-00bb-4ec3-8c5c-3bde1af0b8bf
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/Development.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Polynomial
open scoped ENNReal TensorProduct
namespace PositivityTheory.Rg.Tf.Loc
noncomputable section
abbrev intO (F : Type*) [Field F] [ValuativeRel F] : Subring F :=
  Valuation.integer (ValuativeRel.valuation F)
def IsUnitIntegral {F : Type*} [Field F] [ValuativeRel F] {n : ℕ} (γ : GL (Fin n) F) : Prop :=
  (∀ i, ((γ : Matrix (Fin n) (Fin n) F).charpoly.coeff i) ∈ intO F) ∧
    ValuativeRel.valuation F ((γ : Matrix (Fin n) (Fin n) F).charpoly.coeff 0) = 1
def latticeOf {F : Type*} [Field F] [ValuativeRel F] {n : ℕ} (g : GL (Fin n) F) : Set (Fin n → F) :=
  {v | ∃ w : Fin n → F, (∀ i, w i ∈ intO F) ∧ v = Matrix.mulVec (g : Matrix (Fin n) (Fin n) F) w}
def torusO (F : Type*) [Field F] [ValuativeRel F] {n : ℕ} : Set (GL (Fin n) F) :=
  {t | t ∈ unitGL (n := Fin n) F ∧ ∀ i j : Fin n, i ≠ j → (t : Matrix (Fin n) (Fin n) F) i j = 0}
def iwDouble (F : Type*) [Field F] [ValuativeRel F] {n : ℕ} (x : GL (Fin n) F) : Set (GL (Fin n) F) :=
  {g | ∃ a ∈ iwahori (m := n) F, ∃ b ∈ iwahori (m := n) F, g = a * x * b}
def iwFn (F : Type*) [Field F] [ValuativeRel F] {n : ℕ} (x : GL (Fin n) F) : GL (Fin n) F → ℝ≥0∞ :=
  Set.indicator (iwDouble F x) 1
def D0a : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    (∀ (τ : E ≃ₐ[k] E) (x : E), ValuativeRel.valuation E (τ x) = ValuativeRel.valuation E x) ∧
    (∀ a : k, algebraMap k E a ∈ intO E ↔ a ∈ intO k) ∧
    (∀ (n : ℕ) (g : GL (Fin n) k), incl g ∈ unitGL (n := Fin n) E ↔ g ∈ unitGL (n := Fin n) k) ∧
    (∀ (τ : E ≃ₐ[k] E) (n : ℕ) (g : GL (Fin n) E),
      sigmaGL τ g ∈ unitGL (n := Fin n) E ↔ g ∈ unitGL (n := Fin n) E) ∧
    Continuous (algebraMap k E) ∧
    ∀ n : ℕ, Continuous (fun g : GL (Fin n) k => (incl g : GL (Fin n) E))
def IntegralBasisUnramified : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    (∃ b : Module.Basis (Fin (Module.finrank k E)) k E, (∀ i, b i ∈ intO E) ∧
      ∀ x : E, x ∈ intO E ↔ ∀ i, b.repr x i ∈ intO k) ∧
    (∃ π : k, IsUniformiser π ∧ IsUniformiser (algebraMap k E π)) ∧
    ∀ j : ℕ, 0 < j → j < Module.finrank k E →
      ∃ x : E, x ∈ intO E ∧ ValuativeRel.valuation E ((σ ^ j) x - x) = 1
def TraceOneIntegralElement : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    (∃ a : E, a ∈ intO E ∧ ∑ j ∈ Finset.range (Module.finrank k E), (σ ^ j) a = 1) ∧
    ∃ x y : Fin (Module.finrank k E) → E, (∀ i, x i ∈ intO E ∧ y i ∈ intO E) ∧
      ∀ j < Module.finrank k E, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0
def T0 : Prop :=
  (∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ),
      LocallyCompactSpace (GL (Fin n) F) ∧ SecondCountableTopology (GL (Fin n) F) ∧
      IsOpen (unitGL (n := Fin n) F : Set (GL (Fin n) F)) ∧
      IsCompact (unitGL (n := Fin n) F : Set (GL (Fin n) F))) ∧
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (δ : GL (Fin n) E), IsClosed (twCent (sigmaGL σ) δ : Set (GL (Fin n) E))
def A1 : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), γ.charpoly.Separable →
    ∀ M : Matrix (Fin n) (Fin n) K, Commute M γ → ∃ p : K[X], M = aeval γ p
def A2 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (δ : GL (Fin n) E) (γ : GL (Fin n) k), normGL σ δ = incl γ →
      ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable →
      Commute (δ : Matrix (Fin n) (Fin n) E) (incl γ : GL (Fin n) E) ∧
        ∃ p : E[X], (δ : Matrix (Fin n) (Fin n) E) = aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p
def A3 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (γ : GL (Fin n) k), IsRegSemisimple γ →
      ∀ u : GL (Fin n) E,
        (∃ p : E[X], (u : Matrix (Fin n) (Fin n) E) = aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p) →
        normGL σ u = 1 →
        ∃ x : GL (Fin n) E,
          (∃ q : E[X], (x : Matrix (Fin n) (Fin n) E) = aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) q) ∧
          u = x⁻¹ * sigmaGL σ x
def N1 : Prop :=
  ∀ (κ κ' A : Type) [Field κ] [Finite κ] [CommRing κ'] [Algebra κ κ'] [Module.Finite κ κ']
    [CommRing A] [Algebra κ A] [Module.Finite κ A] [IsReduced A] (ℓ : ℕ) (τ : κ' ≃ₐ[κ] κ'),
    0 < ℓ → τ ^ ℓ = 1 → (∀ z : κ', τ z = z → z ∈ Set.range (algebraMap κ κ')) →
    (∃ x y : Fin ℓ → κ', ∀ j < ℓ, ∑ i, x i * (τ ^ j) (y i) = if j = 0 then 1 else 0) →
    ∀ a : Aˣ, ∃ s : (κ' ⊗[κ] A)ˣ,
      ∏ i ∈ Finset.range ℓ,
          Algebra.TensorProduct.map ((τ ^ i : κ' ≃ₐ[κ] κ').toAlgHom) (AlgHom.id κ A) (s : κ' ⊗[κ] A) =
        Algebra.TensorProduct.includeRight (a : A)
def N2 : Prop :=
  ∀ (O O' R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O']
    [CommRing R] [Algebra O R] [Module.Finite O R] (ℓ : ℕ) (τ : O' ≃ₐ[O] O'),
    0 < ℓ → τ ^ ℓ = 1 → (∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) →
    (∃ x y : Fin ℓ → O', ∀ j < ℓ, ∑ i, x i * (τ ^ j) (y i) = if j = 0 then 1 else 0) →
    (∀ s : O' ⊗[O] R, Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) s = s →
      s ∈ Set.range (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R)) ∧
    ∃ a : O', ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1 ∧
      ∀ m : ℕ, 1 ≤ m → ∀ r ∈ (⊥ : Ideal R).jacobson ^ m,
        (∏ j ∈ Finset.range ℓ,
            Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) (1 + a ⊗ₜ[O] r)) -
          Algebra.TensorProduct.includeRight (1 + r) ∈
        Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R)
          ((⊥ : Ideal R).jacobson ^ (m + 1))
def N3 : Prop :=
  ∀ (O O' R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O']
    [CommRing R] [Algebra O R] [Module.Finite O R] (ℓ : ℕ) (τ : O' ≃ₐ[O] O'),
    0 < ℓ → τ ^ ℓ = 1 → (∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) →
    (∃ x y : Fin ℓ → O', ∀ j < ℓ, ∑ i, x i * (τ ^ j) (y i) = if j = 0 then 1 else 0) →
    ∀ r : Rˣ, ∃ s : (O' ⊗[O] R)ˣ,
      ∏ j ∈ Finset.range ℓ,
          Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) (s : O' ⊗[O] R) =
        Algebra.TensorProduct.includeRight (r : R)
def N4 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (γ : GL (Fin n) k), IsUnitIntegral γ →
      ∃ c : GL (Fin n) E,
        (∃ p : E[X], (c : Matrix (Fin n) (Fin n) E) =
            aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p ∧ ∀ i, p.coeff i ∈ intO E) ∧
        (∃ q : E[X], ((c⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
            aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) q ∧ ∀ i, q.coeff i ∈ intO E) ∧
        normGL σ c = incl γ
def L1 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (g g' : GL (Fin n) F),
    latticeOf g = latticeOf g' ↔ g⁻¹ * g' ∈ unitGL (n := Fin n) F
def L2 : Prop :=
  (∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (γ : GL (Fin n) F),
      (∃ g : GL (Fin n) F, g⁻¹ * γ * g ∈ unitGL (n := Fin n) F) → IsUnitIntegral γ) ∧
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (δ g : GL (Fin n) E), twConj (sigmaGL σ) g δ ∈ unitGL (n := Fin n) E →
      g⁻¹ * normGL σ δ * g ∈ unitGL (n := Fin n) E
def L3 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (g : GL (Fin n) E), g⁻¹ * sigmaGL σ g ∈ unitGL (n := Fin n) E →
      ∃ y : GL (Fin n) k, (incl y)⁻¹ * g ∈ unitGL (n := Fin n) E
def L4 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (γ : GL (Fin n) k) (c : GL (Fin n) E), IsRegSemisimple γ →
      (∃ p : E[X], (c : Matrix (Fin n) (Fin n) E) =
          aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p ∧ ∀ i, p.coeff i ∈ intO E) →
      (∃ q : E[X], ((c⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
          aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) q ∧ ∀ i, q.coeff i ∈ intO E) →
      normGL σ c = incl γ →
      (∀ g : GL (Fin n) E, twConj (sigmaGL σ) g c ∈ unitGL (n := Fin n) E ↔
        (g⁻¹ * sigmaGL σ g ∈ unitGL (n := Fin n) E ∧ g⁻¹ * incl γ * g ∈ unitGL (n := Fin n) E)) ∧
      twCent (sigmaGL σ) c = (Subgroup.centralizer {γ}).map incl
def H2 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μG : Measure (GL (Fin n) F)) (H : Subgroup (GL (Fin n) F)) (μH : Measure H),
    μG.IsHaarMeasure → IsClosed (H : Set (GL (Fin n) F)) → (∀ a ∈ H, ∀ b ∈ H, a * b = b * a) →
    μH.IsHaarMeasure →
    ∀ (Fn : GL (Fin n) F → ℝ≥0∞), Measurable Fn → (∀ h ∈ H, ∀ g, Fn (h * g) = Fn g) →
    (∀ g, ∀ κ ∈ unitGL (n := Fin n) F, Fn (g * κ) = Fn g) →
    ∀ Rp : Set (GL (Fin n) F),
      (∀ g, ∃ r ∈ Rp, ∃ h ∈ H, ∃ κ ∈ unitGL (n := Fin n) F, g = h * r * κ) →
      (∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ unitGL (n := Fin n) F, r' = h * r * κ) → r = r') →
      quotLIntegral μG H μH Fn =
        ∑' r : Rp, Fn r * μG (unitGL (n := Fin n) F : Set (GL (Fin n) F)) /
          μH {h : H | (r : GL (Fin n) F)⁻¹ * (h : GL (Fin n) F) * r ∈ unitGL (n := Fin n) F}
def H4 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
      (δ : GL (Fin n) E) (γ : GL (Fin n) k) (h : GL (Fin n) E)
      (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ})),
      IsTwRegSemisimple σ δ → normGL σ δ = h * incl γ * h⁻¹ →
      Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
        Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ →
      ∀ (y : GL (Fin n) k) (z : GL (Fin n) E),
        Commute (z : Matrix (Fin n) (Fin n) E) (incl γ : GL (Fin n) E) →
        μδ {x | (h * z * incl y)⁻¹ * (x : GL (Fin n) E) * (h * z * incl y) ∈ unitGL (n := Fin n) E} =
          μγ {t | y⁻¹ * (t : GL (Fin n) k) * y ∈ unitGL (n := Fin n) k}
def I0 : Prop :=
  (∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ),
    (∃ U : Subgroup (GL (Fin n) F), (U : Set (GL (Fin n) F)) = iwahori (m := n) F) ∧
    IsOpen (iwahori (m := n) F) ∧ IsCompact (iwahori (m := n) F) ∧ torusO F ⊆ iwahori (m := n) F) ∧
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ n : ℕ, (∀ g : GL (Fin n) k, incl g ∈ iwahori (m := n) E ↔ g ∈ iwahori (m := n) k) ∧
      ∀ (τ : E ≃ₐ[k] E) (g : GL (Fin n) E), sigmaGL τ g ∈ iwahori (m := n) E ↔ g ∈ iwahori (m := n) E
def QuotientIntegralCompactOpen : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μG : Measure (GL (Fin n) F)) (H : Subgroup (GL (Fin n) F)) (μH : Measure H)
    (U : Subgroup (GL (Fin n) F)),
    IsOpen (U : Set (GL (Fin n) F)) → IsCompact (U : Set (GL (Fin n) F)) →
    μG.IsHaarMeasure → IsClosed (H : Set (GL (Fin n) F)) → (∀ a ∈ H, ∀ b ∈ H, a * b = b * a) →
    μH.IsHaarMeasure →
    ∀ (Fn : GL (Fin n) F → ℝ≥0∞), (∀ h ∈ H, ∀ g, Fn (h * g) = Fn g) →
    (∀ g, ∀ κ ∈ U, Fn (g * κ) = Fn g) →
    ∀ Rp : Set (GL (Fin n) F),
      (∀ g, ∃ r ∈ Rp, ∃ h ∈ H, ∃ κ ∈ U, g = h * r * κ) →
      (∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r') →
      quotLIntegral μG H μH Fn =
        ∑' r : Rp, Fn r * μG (U : Set (GL (Fin n) F)) /
          μH {h : H | (r : GL (Fin n) F)⁻¹ * (h : GL (Fin n) F) * r ∈ U}
def MeasureTransportOpenSet : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
      (SE : Set (GL (Fin n) E)) (Sk : Set (GL (Fin n) k)), IsOpen SE → (∀ g, incl g ∈ SE ↔ g ∈ Sk) →
      ∀ (δ : GL (Fin n) E) (γ : GL (Fin n) k) (h : GL (Fin n) E)
      (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ})),
      IsTwRegSemisimple σ δ → normGL σ δ = h * incl γ * h⁻¹ →
      Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
        Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ →
      ∀ (y : GL (Fin n) k) (z : GL (Fin n) E),
        Commute (z : Matrix (Fin n) (Fin n) E) (incl γ : GL (Fin n) E) →
        μδ {x | (h * z * incl y)⁻¹ * (x : GL (Fin n) E) * (h * z * incl y) ∈ SE} =
          μγ {t | y⁻¹ * (t : GL (Fin n) k) * y ∈ Sk}
def H3 : Prop :=
  ∀ (G : Type) [Group G] (θ : Monoid.End G) (g δ x : G),
    x ∈ twCent θ (twConj θ g δ) ↔ g * x * g⁻¹ ∈ twCent θ δ
def A4 : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (γ γ' : GL (Fin n) K),
    (γ : Matrix (Fin n) (Fin n) K).charpoly.Separable →
    (γ : Matrix (Fin n) (Fin n) K).charpoly = (γ' : Matrix (Fin n) (Fin n) K).charpoly →
    ∃ y : GL (Fin n) K, y⁻¹ * γ * y = γ'
def A5 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    (ϖ : Fˣ), ValuativeRel.valuation F (ϖ : F) < 1 → ∀ a : Fin n → ℤ, StrictlyDominant a →
    ∀ (g s s' : GL (Fin n) F), s ∈ torusO F → s' ∈ torusO F →
      g⁻¹ * (diagPow ϖ a * s) * g = diagPow ϖ a * s' →
      ∀ i j : Fin n, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0
def Z1 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
      (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)),
      μE.IsHaarMeasure → μk.IsHaarMeasure →
      μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 →
      μk (unitGL (n := Fin n) k : Set (GL (Fin n) k)) = 1 →
      (∀ (δ : GL (Fin n) E) (γ : GL (Fin n) k) (h : GL (Fin n) E)
          (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ})),
          IsTwRegSemisimple σ δ → normGL σ δ = h * incl γ * h⁻¹ →
          μδ.IsHaarMeasure → μγ.IsHaarMeasure →
          Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
            Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ →
          twOrbIntegral (sigmaGL σ) μE δ μδ (unitFn E) = orbIntegral μk γ μγ (unitFn k))
def Z2 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
      (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)),
      μE.IsHaarMeasure → μk.IsHaarMeasure →
      μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 →
      μk (unitGL (n := Fin n) k : Set (GL (Fin n) k)) = 1 →
      (∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})),
          IsRegSemisimple γ → (¬ ∃ δ : GL (Fin n) E, IsNormOf σ δ γ) →
          μγ.IsHaarMeasure → orbIntegral μk γ μγ (unitFn k) = 0)
def BCFLElem : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
      (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)),
      μE.IsHaarMeasure → μk.IsHaarMeasure →
      ∀ (ϖ : kˣ), IsUniformiser (ϖ : k) → ∀ a : Fin n → ℤ, StrictlyDominant a →
      ∀ (δ : GL (Fin n) E) (γ : GL (Fin n) k) (h : GL (Fin n) E)
        (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ})),
        IsTwRegSemisimple σ δ → normGL σ δ = h * incl γ * h⁻¹ →
      Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
        Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ →
        μδ.IsHaarMeasure → μγ.IsHaarMeasure →
        μk (iwahori (m := n) k) * twOrbIntegral (sigmaGL σ) μE δ μδ (iwFn E (incl (diagPow ϖ a))) =
          μE (iwahori (m := n) E) * orbIntegral μk γ μγ (iwFn k (diagPow ϖ (fun i => (Module.finrank k E : ℤ) * a i)))
def E1 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (ϖ : Fˣ), IsUniformiser (ϖ : F) → ∀ a : Fin n → ℤ, StrictlyDominant a →
    ∀ γ ∈ iwDouble F (diagPow ϖ a), ∃ m ∈ iwahori (m := n) F, ∃ t ∈ torusO F,
      m⁻¹ * γ * m = diagPow ϖ a * t
def TwistedContraction : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (ϖ : kˣ), IsUniformiser (ϖ : k) → ∀ a : Fin n → ℤ, StrictlyDominant a →
      ∀ δ ∈ iwDouble E (incl (diagPow ϖ a)), ∃ m ∈ iwahori (m := n) E, ∃ t ∈ torusO E,
        twConj (sigmaGL σ) m δ = incl (diagPow ϖ a) * t
def E2 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μG : Measure (GL (Fin n) F)), μG.IsHaarMeasure →
    ∀ (ϖ : Fˣ), IsUniformiser (ϖ : F) → ∀ a : Fin n → ℤ, StrictlyDominant a →
    ∀ (γ : GL (Fin n) F) (μγ : Measure (Subgroup.centralizer {γ})), μγ.IsHaarMeasure →
    ∀ (y s : GL (Fin n) F), s ∈ torusO F → y⁻¹ * γ * y = diagPow ϖ a * s →
      orbIntegral μG γ μγ (iwFn F (diagPow ϖ a)) =
        μG (iwahori (m := n) F) / μγ {c | y⁻¹ * (c : GL (Fin n) F) * y ∈ iwahori (m := n) F}
def E2VanishingOtherColumns : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      (μE : Measure (GL (Fin n) E)), μE.IsHaarMeasure →
      ∀ (ϖ : kˣ), IsUniformiser (ϖ : k) → ∀ a : Fin n → ℤ, StrictlyDominant a →
      ∀ (δ : GL (Fin n) E) (μδ : Measure (twCent (sigmaGL σ) δ)), μδ.IsHaarMeasure →
      ∀ (g t : GL (Fin n) E), t ∈ torusO E → twConj (sigmaGL σ) g δ = incl (diagPow ϖ a) * t →
        twOrbIntegral (sigmaGL σ) μE δ μδ (iwFn E (incl (diagPow ϖ a))) =
          μE (iwahori (m := n) E) / μδ {c | g⁻¹ * (c : GL (Fin n) E) * g ∈ iwahori (m := n) E}
def E3 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
      (ϖ : kˣ), IsUniformiser (ϖ : k) → ∀ a : Fin n → ℤ, StrictlyDominant a →
      ∀ (δ : GL (Fin n) E) (γ : GL (Fin n) k) (h : GL (Fin n) E)
        (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ})),
        IsTwRegSemisimple σ δ → normGL σ δ = h * incl γ * h⁻¹ →
      Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
        Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ →
        μδ.IsHaarMeasure → μγ.IsHaarMeasure →
        (∀ y s : GL (Fin n) k, s ∈ torusO k → y⁻¹ * γ * y = diagPow ϖ (fun i => (Module.finrank k E : ℤ) * a i) * s →
          ∃ g : GL (Fin n) E, twConj (sigmaGL σ) g δ ∈ iwDouble E (incl (diagPow ϖ a))) ∧
        (∀ g t : GL (Fin n) E, t ∈ torusO E → twConj (sigmaGL σ) g δ = incl (diagPow ϖ a) * t →
          ∃ y s : GL (Fin n) k, s ∈ torusO k ∧ y⁻¹ * γ * y = diagPow ϖ (fun i => (Module.finrank k E : ℤ) * a i) * s) ∧
        (∀ (g t : GL (Fin n) E) (y s : GL (Fin n) k), t ∈ torusO E → s ∈ torusO k →
          twConj (sigmaGL σ) g δ = incl (diagPow ϖ a) * t → y⁻¹ * γ * y = diagPow ϖ (fun i => (Module.finrank k E : ℤ) * a i) * s →
          μδ {c | g⁻¹ * (c : GL (Fin n) E) * g ∈ iwahori (m := n) E} =
            μγ {c | y⁻¹ * (c : GL (Fin n) k) * y ∈ iwahori (m := n) k})
end
end PositivityTheory.Rg.Tf.Loc


