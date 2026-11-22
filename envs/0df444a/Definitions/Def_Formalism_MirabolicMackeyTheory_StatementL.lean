-- Prove2me | Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
-- name    : Formalism_MirabolicMackeyTheory_StatementL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:29.312292+00:00
-- url     : https://prove2.me/theorems/2b649c76-5817-467a-9b63-118e800710e8
-- title:
--   Statement L
-- statement:
--   Definitions and structural lemmas for Statement L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/StatementL.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
section Defs
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]
def lix (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) Z) : ℤ :=
  Formalism.HermitianLatticesTheory.lidx w.asIdeal A B
def sc [IsScalarTower (𝓞 K) K Z] (a : K) (A : Submodule (𝓞 K) Z) : Submodule (𝓞 K) Z :=
  A.map ((a • (LinearMap.id : Z →ₗ[K] Z)).restrictScalars (𝓞 K))
def cut [IsScalarTower (𝓞 K) K Z] (W : Submodule K Z) (A : Submodule (𝓞 K) Z) :
    Submodule (𝓞 K) Z :=
  A ⊓ W.restrictScalars (𝓞 K)
def IsLatIn (W : Submodule K Z) (A : Submodule (𝓞 K) Z) : Prop :=
  A.FG ∧ Submodule.span K (A : Set Z) = W
def eig {P : Type} [Group P] (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) :
    Submodule K Z :=
  ⨅ u : U, LinearMap.ker (ρ (u : P) - ((ψ (u : P) : 𝓞 K) : K) • (LinearMap.id : Z →ₗ[K] Z))
def IsMackey {P A : Type} [Group P] [Monoid A] (U : Subgroup P) (ψ : P → A) : Prop :=
  ψ 1 = 1 ∧ (∀ u ∈ U, ∀ u' ∈ U, ψ (u * u') = ψ u * ψ u') ∧
    ∀ h : P, h ∉ U → ∃ u ∈ U, h⁻¹ * u * h ∈ U ∧ ψ (h⁻¹ * u * h) ≠ ψ u
end Defs
def IdxMono : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (W : Submodule K Z) (A B B' : Submodule (𝓞 K) Z),
    IsLatIn W A → IsLatIn W B → IsLatIn W B' → B ≤ B' → lix w A B' ≤ lix w A B
def IdxScaleIn : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (W : Submodule K Z) (A B : Submodule (𝓞 K) Z),
    IsLatIn W A → IsLatIn W B → ∀ a : K, a ≠ 0 →
      IsLatIn W (sc a B) ∧ lix w A (sc a B) = lix w A B + (finrank K W : ℤ) * vw w a
def IdxCutLe : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (W W' : Submodule K Z) (A B : Submodule (𝓞 K) Z),
    IsLatIn W A → IsLatIn W B → B ≤ A → W' ≤ W →
      IsLatIn W' (cut W' A) ∧ 0 ≤ lix w (cut W' A) (cut W' B) ∧
        lix w (cut W' A) (cut W' B) ≤ lix w A B
def IdxTransport : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
    (w : HeightOneSpectrum (𝓞 K)) (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z), Function.Injective φ →
    ∀ A B : Submodule (𝓞 K) (Fin d → K),
      lix w (A.map (φ.restrictScalars (𝓞 K))) (B.map (φ.restrictScalars (𝓞 K))) = idx w A B
def LatInter : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (A B : Submodule (𝓞 K) Z), IsLatIn ⊤ A → IsLatIn ⊤ B → ∀ a : K, a ≠ 0 → IsLatIn ⊤ (A ⊓ sc a B)
def ThreeForms : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) Z),
    IsLatIn ⊤ A → IsLatIn ⊤ B → B ≤ A →
    ∀ (a : K) (E : ℕ) (r : ℝ), a ≠ 0 → vw w a = (E : ℤ) →
      ((∀ W : Submodule K Z, (lix w (cut W A) (cut W B) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r) ↔
        (lix w A (A ⊓ sc a⁻¹ B) : ℝ) ≤ r)
def ThreeFormsSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) Z),
    IsLatIn ⊤ A → IsLatIn ⊤ B → B ≤ A → ∀ (a : K), a ≠ 0 → 0 ≤ vw w a →
      lix w (sc a A ⊔ B) B = lix w A (A ⊓ sc a⁻¹ B)
def IdxFull : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (M Th ThK : Submodule (𝓞 K) Z),
    IsLatIn ⊤ M → IsLatIn ⊤ Th → IsLatIn ⊤ ThK → Th ≤ M →
    ∀ (σ : K), σ ≠ 0 → Th ≤ sc σ ThK →
    ∀ (E r : ℝ), (lix w M Th : ℝ) ≤ (finrank K Z : ℝ) * E + r →
      (lix w M ThK : ℝ) ≤ (finrank K Z : ℝ) * (E - (vw w σ : ℝ)) + r
def IdxPsiGood : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (Zψ V₀ : Submodule K Z) (M Th ThK Th0 : Submodule (𝓞 K) Z),
    IsLatIn ⊤ M → IsLatIn ⊤ Th → IsLatIn ⊤ ThK → Th ≤ M → Th0.FG →
    Th0 ≤ Zψ.restrictScalars (𝓞 K) →
    ∀ (σ : K), σ ≠ 0 → Th ≤ sc σ ThK →
    ∀ (u : ℕ), u ≠ 0 → sc (u : K) (cut Zψ ThK) ≤ Th0 →
    ∀ (a : K) (E : ℕ) (r : ℝ), a ≠ 0 → vw w a = (E : ℤ) →
    (lix w M (M ⊓ sc a⁻¹ Th) : ℝ) ≤ r →
    ∀ (δ : ℕ), 0 < δ →
    (δ : ℤ) * lix w (cut Zψ M) (cut Zψ (M ⊓ sc a⁻¹ Th)) ≤
      lix w M (M ⊓ sc a⁻¹ Th) + (finrank K Z : ℤ) * vw w (u : K) →
      IsLatIn (Zψ ⊓ V₀) (cut V₀ Th0) ∧
      (lix w (cut (Zψ ⊓ V₀) M) (cut V₀ Th0) : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w (u : K) : ℝ)) * (finrank K (Zψ ⊓ V₀ : Submodule K Z) : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w (u : K) : ℝ)) / (δ : ℝ)
def OrthOfMackey : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    (P : Type) [Group P] [Fintype P] (ρ : Representation K P Z) (U : Subgroup P) [Fintype U]
    (ψ : P → 𝓞 K), IsMackey U ψ →
    ∀ h : P, h ∉ U → ∀ z ∈ eig ρ U ψ,
      ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ h z) = 0
def LemmaGG : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K), IsMackey U ψ →
    ∀ (B B' : Submodule (𝓞 K) Z), IsLatIn ⊤ B → IsLatIn ⊤ B' → B' ≤ B →
    (∀ g : P, B.map ((ρ g).restrictScalars (𝓞 K)) ≤ B) →
    (∀ g : P, B'.map ((ρ g).restrictScalars (𝓞 K)) ≤ B') →
      (U.index : ℤ) * lix w (cut (eig ρ U ψ) B) (cut (eig ρ U ψ) B') ≤
        lix w B B' + (finrank K Z : ℤ) * vw w ((Nat.card U : ℕ) : K)
def MackeyProd : Prop :=
  ∀ (ι A : Type) [Fintype ι] [DecidableEq ι] [CommMonoid A] (P : ι → Type) [∀ v, Group (P v)]
    (U : ∀ v, Subgroup (P v)) (ψ : ∀ v, P v → A), (∀ v, IsMackey (U v) (ψ v)) →
      IsMackey (Subgroup.pi Set.univ U) (fun h : (∀ v, P v) => ∏ v, ψ v (h v))
def IsMirab {k : Type} [Field k] {n : ℕ} (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : Prop :=
  ∀ j, h (Fin.last n) j = if j = Fin.last n then 1 else 0
def IsUniU {k : Type} [Field k] {n : ℕ} (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : Prop :=
  (∀ i, u i i = 1) ∧ ∀ i j, j < i → u i j = 0
def supd {k : Type} [Field k] {n : ℕ} (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : k :=
  ∑ i : Fin n, u i.castSucc i.succ
def MirabolicMackey : Prop :=
  ∀ (k A : Type) [Field k] [Finite k] [CommMonoid A] (n : ℕ) (ψ : AddChar k A), ψ ≠ 1 →
    ∀ h : GL (Fin (n + 1)) k, IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) →
      ¬ IsUniU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) →
      ∃ u : GL (Fin (n + 1)) k, IsUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∧
        IsUniU ((h⁻¹ * u * h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∧
        ψ (supd ((h⁻¹ * u * h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ≠
          ψ (supd (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
def MirabolicIsMackey : Prop :=
  ∀ (k A : Type) [Field k] [Finite k] [CommMonoid A] (n : ℕ) (ψ : AddChar k A), ψ ≠ 1 →
    ∀ (P : Subgroup (GL (Fin (n + 1)) k)) (U : Subgroup P),
      (∀ h : GL (Fin (n + 1)) k, h ∈ P ↔ IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) →
      (∀ h : P, h ∈ U ↔ IsUniU ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) →
      IsMackey U (fun h : P => ψ (supd ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)))
def DataTrace : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
    (U : Type) [Group U] [Fintype U] (ρ : Representation K U Z) (ψ : U →* 𝓞 K)
    (X : Type) [Fintype X] [DecidableEq X] [MulAction U X], (∀ (u : U) (x : X), u • x = x → u = 1) →
    ∀ Θ : (X → 𝓞 K) →ₗ[𝓞 K] Z, (∀ (u : U) (φ : X → 𝓞 K), ρ u (Θ φ) = Θ (fun x => φ (u⁻¹ • x))) →
    ∀ z ∈ LinearMap.range Θ, (∀ u : U, ρ u z = ((ψ u : 𝓞 K) : K) • z) →
      ((Fintype.card U : ℕ) : K) • z ∈
        Submodule.span (𝓞 K) {y | ∃ x₀ : X, y = Θ (fun x => ∑ u : U, if x = u⁻¹ • x₀ then ψ u else 0)}
def LengthRamified : Prop :=
  ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
    [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Flat O O'] (e : ℕ),
    Ideal.map (algebraMap O O') (IsLocalRing.maximalIdeal O) = IsLocalRing.maximalIdeal O' ^ e →
    ∀ (M : Type) [AddCommGroup M] [Module O M], Module.length O M ≠ ⊤ →
      Module.length O' (TensorProduct O O' M) = (e : ℕ∞) * Module.length O M
def OnLocal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K), IsMackey U ψ →
    ∀ (V₀ : Submodule K Z) (e : Z →ₗ[K] Z), e ∘ₗ e = e → LinearMap.range e = V₀ →
    ∀ (M Th ThK Th0 X₃ X₄ : Submodule (𝓞 K) Z),
    IsLatIn ⊤ M → IsLatIn ⊤ Th → IsLatIn ⊤ ThK → Th ≤ M → Th0.FG →
    Th0 ≤ (eig ρ U ψ).restrictScalars (𝓞 K) →
    (∀ g : P, M.map ((ρ g).restrictScalars (𝓞 K)) ≤ M) →
    (∀ g : P, Th.map ((ρ g).restrictScalars (𝓞 K)) ≤ Th) →
    ∀ (σ : K), σ ≠ 0 → Th ≤ sc σ ThK →
    sc ((Nat.card U : ℕ) : K) (cut (eig ρ U ψ) ThK) ≤ Th0 →
    ∀ (a : K) (E : ℕ) (r : ℝ), a ≠ 0 → vw w a = (E : ℤ) →
    (∀ W : Submodule K Z, (lix w (cut W M) (cut W Th) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r) →
    IsLatIn (eig ρ U ψ ⊓ V₀) (Th0.map (e.restrictScalars (𝓞 K))) →
    IsLatIn (eig ρ U ψ ⊓ V₀) X₃ → IsLatIn (eig ρ U ψ ⊓ V₀) X₄ → X₃ ≤ X₄ →
    ∀ (ε : ℝ),
    (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ : ℝ) ≤
      (lix w (cut (eig ρ U ψ ⊓ V₀) M) (Th0.map (e.restrictScalars (𝓞 K))) : ℝ) + ε →
    ∀ (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z), Function.Injective φ →
    LinearMap.range φ = eig ρ U ψ ⊓ V₀ →
    ∀ (Mj Tj : Submodule (𝓞 K) (Fin d → K)),
    Mj.map (φ.restrictScalars (𝓞 K)) = cut (eig ρ U ψ ⊓ V₀) M →
    Tj.map (φ.restrictScalars (𝓞 K)) = X₄ →
      (idx w Mj Tj : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w ((Nat.card U : ℕ) : K) : ℝ)) * (d : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w ((Nat.card U : ℕ) : K) : ℝ)) / (U.index : ℝ) + ε
end Formalism.EigenvalueLevelCeiling


