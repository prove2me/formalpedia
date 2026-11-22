-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
-- name    : Formalism_GL3MeanSquares_OrbitPointsDistinct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:46.690828+00:00
-- url     : https://prove2.me/theorems/31dda516-4e4a-4887-b0f1-da8f70756f55
-- title:
--   Orbit Points Distinct
-- statement:
--   Definitions and structural lemmas for Orbit Points Distinct, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/OrbitPointsDistinct.lean

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal IsDedekindDomain
open scoped Pointwise TensorProduct
noncomputable section
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
def PartnerFormula : Prop :=
  ∀ (e : ℕ) (h t : HGrp e),
    cc e * ((c0, h) : GG e) * ((1, t) : GG e) = ((1, h * t) : GG e) ∧
    cc e * ((c0, h) : GG e) * (((sg e).1, t) : GG e) = (((sg e).1, h * t) : GG e) ∧
    cc e * ((((1 : ℤˣ), (-1 : ℤˣ)), h) : GG e) * ((1, t) : GG e) = (((sg e).1, h * t) : GG e) ∧
    cc e * ((((1 : ℤˣ), (-1 : ℤˣ)), h) : GG e) * (((sg e).1, t) : GG e) = ((1, h * t) : GG e)
def FrobArith : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
  ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (u : (ZMod (2 ^ (e + 2)))ˣ), (u : ZMod (2 ^ (e + 2))) = (p : ZMod (2 ^ (e + 2))) →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
    ((∀ x : 𝓞 (hostE ζ a b), σ • x - x ^ p ∈ P) ↔
      ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
        (((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p ∧
        (galE e ζ a b σ).2 = hcl e u)) ∧
    ((∀ x : 𝓞 (hostE ζ a b), σ⁻¹ • x - x ^ p ∈ P) ↔
      ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
        (((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p ∧
        (galE e ζ a b σ).2 = (hcl e u)⁻¹))
def OrbitsInt : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, (φ.1 = c0 ∨ φ.1 = ((1 : ℤˣ), (-1 : ℤˣ))) →
    ((φ⁻¹).1 = φ.1 ∧ (φ⁻¹).2 = (φ.2)⁻¹ ∧ orderOf (φ⁻¹).2 = orderOf φ.2 ∧
      orderOf φ⁻¹ = orderOf φ) ∧
    ∀ (τ : GG e) (i : ℤ),
      ((φ ^ i * τ ∈ Psi e ↔ τ ∈ Psi e) ↔ Even i) ∧
      (placeOf (φ ^ i * τ)).2 = φ.2 ^ i * τ.2 ∧
      (φ.1 = c0 → (placeOf (φ ^ i * τ)).1 = (placeOf τ).1) ∧
      (φ.1 = ((1 : ℤˣ), (-1 : ℤˣ)) →
        (placeOf (φ ^ i * τ)).1 = (if Even i then 1 else (sg e).1) * (placeOf τ).1)
def OrdLe (e l : ℕ) (J : ℝ) : Prop :=
  ∃ u : (ZMod (2 ^ (e + 2)))ˣ, (u : ZMod (2 ^ (e + 2))) = (l : ZMod (2 ^ (e + 2))) ∧
    (orderOf (hcl e u) : ℝ) ≤ J
def OrdersPow : Prop :=
  ∀ (e j l : ℕ), j ≤ e → l.Prime → l ≠ 2 →
  ∀ u : (ZMod (2 ^ (e + 2)))ˣ, (u : ZMod (2 ^ (e + 2))) = (l : ZMod (2 ^ (e + 2))) →
    (hcl e u ^ (2 ^ j) = 1 ↔
      ((l : ℤ) ≡ 1 [ZMOD ((2 ^ (e + 2) / 2 ^ j : ℕ) : ℤ)] ∨
        (l : ℤ) ≡ -1 [ZMOD ((2 ^ (e + 2) / 2 ^ j : ℕ) : ℤ)]))
def OrdersLower : Prop :=
  ∀ (e l : ℕ) (J : ℝ), l.Prime → l ≠ 2 → 1 ≤ J → OrdLe e l J →
    (2 ^ (e + 2) : ℝ) / J - 1 ≤ (l : ℝ)
def OrdersModulus : Prop :=
  ∀ (e : ℕ) (J : ℝ), 1 ≤ J → ∃ M : ℕ, 4 ≤ M ∧ M ∣ 2 ^ (e + 2) ∧ (2 ^ (e + 2) : ℝ) ≤ J * M ∧
    ∀ l : ℕ, l.Prime → l ≠ 2 →
      (OrdLe e l J ↔ ((l : ℤ) ≡ 1 [ZMOD (M : ℤ)] ∨ (l : ℤ) ≡ -1 [ZMOD (M : ℤ)]))
open Classical in

def OrdersSumSq : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (e Y : ℕ) (J : ℝ), 2 ≤ e → 1 ≤ J →
    (∑ l ∈ (Finset.range (Y + 1)).filter (fun l : ℕ => l.Prime ∧ l ≠ 2 ∧ OrdLe e l J),
      Real.log (l : ℝ) / (l : ℝ) ^ 2) ≤
      C * J ^ 2 * Real.log ((2 : ℝ) ^ e) / ((2 : ℝ) ^ e) ^ 2
open Classical in

def OrdersSumSqTsum : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (e : ℕ) (J : ℝ), 2 ≤ e → 1 ≤ J →
    Summable (fun l : ℕ => if l.Prime ∧ l ≠ 2 ∧ OrdLe e l J
      then Real.log (l : ℝ) / (l : ℝ) ^ 2 else 0) ∧
    (∑' l : ℕ, (if l.Prime ∧ l ≠ 2 ∧ OrdLe e l J
      then Real.log (l : ℝ) / (l : ℝ) ^ 2 else 0)) ≤
      C * J ^ 2 * Real.log ((2 : ℝ) ^ e) / ((2 : ℝ) ^ e) ^ 2
open Classical in

def OrdersSumLog : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (e : ℕ) (J Y : ℝ), 2 ≤ e → 1 ≤ J →
    (∑ l ∈ (Finset.range (⌊Y⌋₊ + 1)).filter (fun l : ℕ => l.Prime ∧ l ≠ 2 ∧ OrdLe e l J),
      Real.log (l : ℝ) / (l : ℝ)) ≤
      C * J * (Real.log ((2 : ℝ) ^ e * Y)) ^ 2 / (2 : ℝ) ^ e
def IsThick {e : ℕ} (ι : HGrp e ≃* Multiplicative (ZMod (2 ^ e))) (T : Finset ℕ)
    (u₀ : ZMod (2 ^ e)) (g : GG e) : Prop :=
  (placeOf g).1 = (sg e).1 ∧ InTranslate T u₀ (Multiplicative.toAdd (ι (placeOf g).2))
def ThickAlternate : Prop :=
  ∀ (e : ℕ) (ι : HGrp e ≃* Multiplicative (ZMod (2 ^ e))) (T : Finset ℕ) (u₀ : ZMod (2 ^ e))
    (φ τ : GG e), φ.1 = ((1 : ℤˣ), (-1 : ℤˣ)) → ∀ i : ℤ,
    ¬ (IsThick ι T u₀ (φ ^ i * τ) ∧ IsThick ι T u₀ (φ ^ (i + 1) * τ))
def ThickShortOrbit : Prop :=
  ∀ (e Lw : ℕ), 2 ≤ Lw → ∀ (ι : HGrp e ≃* Multiplicative (ZMod (2 ^ e))) (T : Finset ℕ),
    (∀ s ∈ T, 4 * Lw * s < 2 ^ e) →
  ∀ (u₀ : ZMod (2 ^ e)) (φ τ : GG e), φ.1 = c0 → φ.2 ≠ 1 → orderOf φ.2 ≤ 4 * Lw → ∀ i : ℤ,
    ¬ (IsThick ι T u₀ (φ ^ i * τ) ∧ IsThick ι T u₀ (φ ^ (i + 1) * τ))
def ThickCorollary : Prop :=
  ∀ (e Lw : ℕ), 3 ≤ Lw → ∀ (ι : HGrp e ≃* Multiplicative (ZMod (2 ^ e))) (T : Finset ℕ),
    (∀ s ∈ T, 4 * Lw * s < 2 ^ e) → NoRel T Lw →
  ∀ (u₀ : ZMod (2 ^ e)) (φ τ : GG e), φ ∉ Psi e → φ ≠ cc e → ∀ i : ℤ,
    ¬ (IsThick ι T u₀ (φ ^ i * τ) ∧ IsThick ι T u₀ (φ ^ (i + 1) * τ) ∧
      IsThick ι T u₀ (φ ^ (i + 2) * τ))
def OrbitPointsDistinct : Prop :=
  ∀ (n : ℕ) (t h : ZMod n), Set.InjOn (fun i : ℕ => t + i • h) (Set.Iio (addOrderOf h))
open Classical in

def BernMarginal : Prop :=
  ∀ (α : Type) [Fintype α] (δ : ℝ) (S A : Finset α), A ⊆ S →
    (∑ T : Finset α, if T ∩ S = A then bern δ T else 0) =
      δ ^ A.card * (1 - δ) ^ (S.card - A.card)
open Classical in

def RandomSubsetAvoidsBadProgressions : Prop :=
  ∀ (n : ℕ) [NeZero n] (ι : Type) [Fintype ι] (δ β R : ℝ) (ω : ι → ℝ) (hp : ι → ZMod n)
    (BAD : ZMod n → ZMod n → Finset (ZMod n) → Prop),
    0 ≤ δ → δ ≤ 1 → 16 ≤ δ * n → (∀ p, 0 ≤ ω p) →
    (∀ (h t : ZMod n) (T T' : Finset (ZMod n)),
      (∀ i : ℤ, (t + i • h ∈ T ↔ t + i • h ∈ T')) → (BAD h t T ↔ BAD h t T')) →
    (∀ h t : ZMod n, R ≤ (addOrderOf h : ℝ) →
      (∑ T : Finset (ZMod n), if t ∈ T ∧ BAD h t T then bern δ T else 0) /
        (∑ T : Finset (ZMod n), if t ∈ T then bern δ T else 0) ≤ β) →
    (∀ p, R ≤ (addOrderOf (hp p) : ℝ)) →
    ∃ T : Finset (ZMod n), δ * n / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * δ * n ∧
      (∑ p, ω p * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ)) ≤ 4 * β * δ * n * ∑ p, ω p
def StabJoint : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (k g : ℕ), g.Prime → 2 ^ (e + 2) * k < g - 1 →
  ∀ (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin k) (hostE ζ a b))), Finite Γ →
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G],
    (∀ N : Subgroup G, IsOpen (N : Set G) → N.Normal → ∃ m : ℕ, N.index = g ^ m) →
    ∀ j : Γ →* G, Function.Injective j → Γ = ⊥
def StabAdelic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (k : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    Formalism.UG.IsHerm (σ : E →+* E) J → IsUnit J.det → Formalism.UG.IsTotDef σ J →
  ∀ Λ : Submodule (𝓞 E) (Fin k → E), Module.Finite (𝓞 E) Λ →
    Submodule.span E (Λ : Set (Fin k → E)) = ⊤ →
  ∀ U : Subgroup (Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    U ≤ Formalism.UG.levelAfL σ J Λ →
  ∀ (w : HeightOneSpectrum (𝓞 F)) (g : ℕ), g.Prime → Module.finrank ℚ E * k < g - 1 →
  ∀ Uw : Subgroup (Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] w.adicCompletion F)),
    (∀ x ∈ U, Formalism.UG.bc (Formalism.UG.prV (E := E) w) x ∈ Uw) →
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G],
    (∀ N : Subgroup G, IsOpen (N : Set G) → N.Normal → ∃ m : ℕ, N.index = g ^ m) →
  ∀ j : Uw →* G, Function.Injective j →
    Formalism.UG.IsNeat
      ((Formalism.UG.ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf
        (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)))
      (U.subgroupOf (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)))
def CongruencePowers : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (g k : ℕ), (g : R) ∈ I →
  ∀ A : Matrix (Fin k) (Fin k) R, (∀ i j, (A - 1) i j ∈ I) →
  ∀ (m : ℕ) (i j : Fin k), (A ^ (g ^ m) - 1) i j ∈ I ^ (m + 1)
def FormsFree : Prop :=
  ∀ (G W : Type) [Group G] (Γ U : Subgroup G) [MulAction U W] (R : Set G),
    (∀ y : G, ∀ γ ∈ Γ, y⁻¹ * γ * y ∈ U → γ = 1) →
    (∀ g : G, ∃! r : G, r ∈ R ∧ ∃ γ ∈ Γ, ∃ u ∈ U, g = γ * r * u) →
    ∀ w : R → W, ∃! f : G → W,
      (∀ γ ∈ Γ, ∀ (u : U) (g : G), f (γ * g * (u : G)) = u⁻¹ • f g) ∧ ∀ r : R, f (r : G) = w r
def DiffStable : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
    σ • differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) =
      differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))
def PrincipalStable : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b c = cc e →
  ∀ 𝔭₂ 𝔭q : Ideal (𝓞 (KinE ζ a b)), 𝔭₂.IsPrime → 𝔭q.IsPrime →
    ((2 : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭₂ → ((q : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭q →
    ∃ 𝔟 : Ideal (𝓞 (hostE ζ a b)),
      differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟 * (c • 𝔟) ∧
      (∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime → P ∣ 𝔟 →
        P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭₂ ∨
        P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭q) ∧
      𝔟 ⊔ c • 𝔟 = ⊤ ∧
      (∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ ∈ Psi e → σ • 𝔟 = 𝔟) ∧
      ∀ 𝔟' : Ideal (𝓞 (hostE ζ a b)),
        differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟' * (c • 𝔟') →
        (∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime → P ∣ 𝔟' →
          P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭₂ ∨
          P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭q) →
        𝔟' = 𝔟
def DiffAbs : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    ∃ β : 𝓞 (hostE ζ a b), (β : hostE ζ a b) = bE ζ a b ∧
      differentIdeal ℤ (𝓞 (hostE ζ a b)) =
        differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) * span {β}
end Formalism.HermitianLattices.FiltrationBoundaryCriterion


