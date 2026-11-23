-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
-- name    : Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:14.698823+00:00
-- url     : https://prove2.me/theorems/8b68a19e-82f0-4e71-b24b-543609eebbe9
-- title:
--   Order OKOne Inert
-- statement:
--   Definitions and structural lemmas for Order OKOne Inert, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/OrderOKOneInert.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_algebraMap_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix GlobalTheory.WeilM ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
namespace GlobalTheory.CompanionTheory.VacLoc
def intMat {E : Type} [CommRing E] (A : Subring E) (α β : Type) : AddSubgroup (Matrix α β E) where
  carrier := {x | ∀ i j, x i j ∈ A}
  zero_mem' := fun _ _ => zero_mem _
  add_mem' := fun hx hy i j => add_mem (hx i j) (hy i j)
  neg_mem' := fun hx i j => neg_mem (hx i j)
structure Inert (k : Type) [Field k] [ValuativeRel k] {E : Type} [CommRing E] [Algebra k E] (c : E →ₐ[k] E) (ξ : E) :
    Prop where
  quad : IsQuad c ξ
  two : valuation k (2 : k) = 1
  sq : ∃ δ : k, valuation k δ = 1 ∧ ξ * ξ = algebraMap k E δ ∧ ∀ y : k, valuation k y ≤ 1 → valuation k (y * y - δ) = 1
def Unram {E : Type} [CommRing E] (A : Subring E) (χ : Eˣ →* Circle) : Prop :=
  ∀ z : Eˣ, (z : E) ∈ A → ((z⁻¹ : Eˣ) : E) ∈ A → χ z = 1
def VacuumInert : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
    (E : Type) [CommRing E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (ξ : E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (JA : Matrix α α E) (JB : Matrix β β E) (ψ : AddChar k ℂ) (d : Darboux (symp c ξ JA JB) κ) (χA χB : Eˣ →* Circle)
    (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)) (φ : (κ → k) → ℂ),
    Inert k c ξ → GoodChar ψ 𝒪[k] 1 →
    OrderCondition c (ordQ 𝒪[k] ξ) (algebraMap k E (⅟2)) JA → OrderCondition c (ordQ 𝒪[k] ξ) (algebraMap k E (⅟2)) JB →
    Unram (ordQ 𝒪[k] ξ) χA → Unram (ordQ 𝒪[k] ξ) χB →
    IsUWeilPair c (sbClass k) ψ ξ JA JB d χA χB om →
    IsVac c ψ ξ (algebraMap k E (⅟2)) JA JB d (intMat (ordQ 𝒪[k] ξ) α β) φ →
    ∀ a ∈ KU c (ordQ 𝒪[k] ξ) JA, ∀ b ∈ KU c (ordQ 𝒪[k] ξ) JB, om (a, b) φ = φ
def MoveInert : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
    (E : Type) [CommRing E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (ξ : E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (JA : Matrix α α E) (JB : Matrix β β E) (ψ : AddChar k ℂ) (d : Darboux (symp c ξ JA JB) κ) (χ : Eˣ →* Circle)
    (om : UG c JB →* Module.End ℂ ((κ → k) → ℂ)) (μ : @Measure (κ → k) (borel _))
    (S : GlobalTheory.CompanionTheory.FinHeis.Sys (Matrix α β E) (SB (κ → k))) (φ : SB (κ → k)),
    Inert k c ξ → GoodChar ψ 𝒪[k] 1 → Even (Fintype.card α) →
    OrderCondition c (ordQ 𝒪[k] ξ) (algebraMap k E (⅟2)) JA → OrderCondition c (ordQ 𝒪[k] ξ) (algebraMap k E (⅟2)) JB →
    Unram (ordQ 𝒪[k] ξ) χ → ResEtaPow ⊥ χ (Fintype.card α) (R := k) →
    IsUWeilB c (sbClass k) ψ ξ JA JB d χ om → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → IsModel ψ d μ S →
    IsVac c ψ ξ (algebraMap k E (⅟2)) JA JB d (intMat (ordQ 𝒪[k] ξ) α β) φ →
    ∀ g : UG c JB,
      om g φ = (GlobalTheory.CompanionTheory.FinHeis.abelian₂ S (alH c ψ ξ (algebraMap k E (⅟2)) JA JB) (latB c g (intMat (ordQ 𝒪[k] ξ) α β))
        (intMat (ordQ 𝒪[k] ξ) α β) φ : SB (κ → k)) ∧
      ∃ m : ℕ, (intMat (ordQ 𝒪[k] ξ) α β).relIndex (latB c g (intMat (ordQ 𝒪[k] ξ) α β)) =
        (GlobalTheory.SplitWeil.resCard k ^ 2) ^ m
def MoveSplit : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
    (E : Type) [CommRing E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (ξ e : E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (JA : Matrix α α E) (JB : Matrix β β E) (ψ : AddChar k ℂ) (u : kˣ) (d : Darboux (symp c ξ JA JB) κ)
    (χ : Eˣ →* Circle) (om : UG c JB →* Module.End ℂ ((κ → k) → ℂ)) (μ : @Measure (κ → k) (borel _))
    (S : GlobalTheory.CompanionTheory.FinHeis.Sys (Matrix α β E) (SB (κ → k))) (φ : SB (κ → k)) (Γ : AddSubgroup (Matrix α β E)),
    IsQuad c ξ → e * e = e → GoodChar ψ 𝒪[k] u → IsHerm c JA → OrderCondition c (ordQ 𝒪[k] e) e JB →
    LatOK c ψ ξ JA JB (ordQ 𝒪[k] e) Γ → ResEtaPow ⊥ χ (Fintype.card α) (R := k) →
    IsUWeilB c (sbClass k) ψ ξ JA JB d χ om → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → IsModel ψ d μ S →
    IsVac c ψ ξ e JA JB d Γ φ →
    ∀ g : UG c JB,
      (∀ z : Eˣ, (z : E) = e * ((g : GL β E) : Matrix β β E).det + (1 - e) →
        om g φ = (χ z : ℂ) • (GlobalTheory.CompanionTheory.FinHeis.abelian₂ S (alH c ψ ξ e JA JB) (latB c g Γ) Γ φ : SB (κ → k))) ∧
      ∀ (ϖ : kˣ) (a : β → ℤ) (g₀ : UG c JB), (∃ p : 𝒪[k], Irreducible p ∧ (p : k) = ϖ) →
        (∃ k₁ ∈ KU c (ordQ 𝒪[k] e) JB, ∃ k₂ ∈ KU c (ordQ 𝒪[k] e) JB, g = k₁ * g₀ * k₂) →
        e • ((g₀ : GL β E) : Matrix β β E) = e • Matrix.diagonal (fun i => algebraMap k E ((ϖ ^ a i : kˣ) : k)) →
        Γ.relIndex (latB c g Γ) = GlobalTheory.SplitWeil.resCard k ^ (Fintype.card α * ∑ i, (a i).natAbs)
section Adelic
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def intA : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}
  zero_mem' := fun _ => zero_mem _
  one_mem' := fun _ => one_mem _
  add_mem' := fun hx hy v => add_mem (hx v) (hy v)
  neg_mem' := fun hx v => neg_mem (hx v)
  mul_mem' := fun hx hy v => mul_mem (hx v) (hy v)
abbrev EA : Type := FiniteAdeleRing (𝓞 F) F ⊗[F] E
def cA (c : E →ₐ[F] E) : EA F E →ₐ[FiniteAdeleRing (𝓞 F) F] EA F E :=
  Algebra.TensorProduct.map (AlgHom.id _ _) c
def intE : Subring (EA F E) :=
  Subring.closure ((fun x => x ⊗ₜ[F] (1 : E)) '' (intA F : Set (FiniteAdeleRing (𝓞 F) F)) ∪
    Set.range fun y : 𝓞 E => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (y : E))
end Adelic
def MoveAdelic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F)] [Invertible (2 : FiniteAdeleRing (𝓞 F) F)]
    [TopologicalSpace (EA F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (EA F E)]
    (c : E →ₐ[F] E) (ξ w₀ : EA F E) (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (JA : Matrix α α (EA F E)) (JB : Matrix β β (EA F E)) (ψ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)
    (u : (FiniteAdeleRing (𝓞 F) F)ˣ) (d : Darboux (symp (cA F E c) ξ JA JB) κ) (χ : (EA F E)ˣ →* Circle)
    (K : Subgroup (FiniteAdeleRing (𝓞 F) F)ˣ)
    (om : UG (cA F E c) JB →* Module.End ℂ ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ))
    (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (S : GlobalTheory.CompanionTheory.FinHeis.Sys (Matrix α β (EA F E)) (SB (κ → FiniteAdeleRing (𝓞 F) F)))
    (φ : SB (κ → FiniteAdeleRing (𝓞 F) F)) (Γ : AddSubgroup (Matrix α β (EA F E))),
    Algebra.Unramified (𝓞 F) (𝓞 E) → IsQuad (cA F E c) ξ → GoodChar ψ (intA F) u → IsHerm (cA F E c) JA →
    OrderCondition (cA F E c) (intE F E) w₀ JB → LatOK (cA F E c) ψ ξ JA JB (intE F E) Γ →
    ResEtaPow K χ (Fintype.card α) → IsUWeilB (cA F E c) (sbClass _) ψ ξ JA JB d χ om →
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → IsModel ψ d μ S → IsVac (cA F E c) ψ ξ w₀ JA JB d Γ φ →
    (∀ k ∈ KU (cA F E c) (intE F E) JB, ∀ z : (EA F E)ˣ, (z : EA F E) ∈ intE F E → ((z⁻¹ : (EA F E)ˣ) : EA F E) ∈ intE F E →
      ((k : GL β (EA F E)) : Matrix β β (EA F E)).det * cA F E c z = z → om k φ = (χ z : ℂ) • (φ : _ → ℂ)) ∧
    ∀ (g : UG (cA F E c) JB) (e : EA F E) (z : (EA F E)ˣ), e * e = e → e * cA F E c e = 0 →
      (1 - e - cA F E c e) • ((g : GL β (EA F E)) : Matrix β β (EA F E)) = (1 - e - cA F E c e) • (1 : Matrix β β (EA F E)) →
      (z : EA F E) = e * ((g : GL β (EA F E)) : Matrix β β (EA F E)).det + (1 - e) →
      om g φ = (χ z : ℂ) • (GlobalTheory.CompanionTheory.FinHeis.abelian₂ S (alH (cA F E c) ψ ξ w₀ JA JB) (latB (cA F E c) g Γ) Γ φ :
        SB (κ → FiniteAdeleRing (𝓞 F) F))
def IndexAdelic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [TopologicalSpace (EA F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (EA F E)]
    (c : E →ₐ[F] E) (ξ w₀ : EA F E) (α β : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (JA : Matrix α α (EA F E)) (JB : Matrix β β (EA F E)) (ψ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)
    (u : (FiniteAdeleRing (𝓞 F) F)ˣ) (Γ : AddSubgroup (Matrix α β (EA F E))),
    Algebra.Unramified (𝓞 F) (𝓞 E) → IsQuad (cA F E c) ξ → GoodChar ψ (intA F) u → IsHerm (cA F E c) JA →
    OrderCondition (cA F E c) (intE F E) w₀ JB → LatOK (cA F E c) ψ ξ JA JB (intE F E) Γ →
    ∀ (g g₀ : UG (cA F E c) JB) (e : EA F E) (t : β → (FiniteAdeleRing (𝓞 F) F)ˣ), e * e = e → e * cA F E c e = 0 →
      (∃ k₁ ∈ KU (cA F E c) (intE F E) JB, ∃ k₂ ∈ KU (cA F E c) (intE F E) JB, g = k₁ * g₀ * k₂) →
      (1 - e - cA F E c e) • ((g₀ : GL β (EA F E)) : Matrix β β (EA F E)) =
        (1 - e - cA F E c e) • (1 : Matrix β β (EA F E)) →
      e • ((g₀ : GL β (EA F E)) : Matrix β β (EA F E)) =
        e • Matrix.diagonal (fun i => algebraMap (FiniteAdeleRing (𝓞 F) F) (EA F E) (t i : FiniteAdeleRing (𝓞 F) F)) →
      (∀ i, (1 - e - cA F E c e) * algebraMap (FiniteAdeleRing (𝓞 F) F) (EA F E) (t i : FiniteAdeleRing (𝓞 F) F) =
        1 - e - cA F E c e) →
      Γ.relIndex (latB (cA F E c) g Γ) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 F), Ideal.absNorm v.asIdeal ^
          (Fintype.card α * ∑ i, (WithZero.log (Valued.v ((t i : FiniteAdeleRing (𝓞 F) F) v))).natAbs)
namespace Unr
def sqrtConj {k : Type} [Field k] (δ : k) : QuadraticAlgebra k δ 0 →ₐ[k] QuadraticAlgebra k δ 0 where
  toFun z := star z
  map_one' := star_one _
  map_mul' x y := star_mul' x y
  map_zero' := star_zero _
  map_add' := star_add
  commutes' r := by ext <;> simp
example {k : Type} [Field k] [ValuativeRel k] {E : Type} [CommRing E] [Algebra k E] {c : E →ₐ[k] E} {ξ : E}
    (h : Inert k c ξ) : ξ * ξ ≠ 1 := by
  obtain ⟨δ, -, h2, h3⟩ := h.sq
  intro e
  have e2 : δ = 1 := h.quad.algebraMap_injective (by rw [← h2, e, map_one])
  simpa [e2] using h3 1 (by simp)
example {E : Type} [CommRing E] (A : Subring E) : Unram A 1 ∧ (0 : Matrix Unit Unit E) ∈ intMat A Unit Unit :=
  ⟨fun _ _ _ => rfl, zero_mem _⟩
end Unr
end GlobalTheory.CompanionTheory.VacLoc


