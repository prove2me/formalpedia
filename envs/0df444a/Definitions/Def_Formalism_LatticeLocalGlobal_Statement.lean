-- Prove2me | Definitions.Def_Formalism_LatticeLocalGlobal_Statement
-- name    : Formalism_LatticeLocalGlobal_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:16.884807+00:00
-- url     : https://prove2.me/theorems/1fa8e2ef-c596-41b3-ad87-05ddcd88e140
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeLocalGlobal/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeLocalGlobalTheory
open IsDedekindDomain
def UniqueForm : Prop :=
  ∀ (k K E ι : Type) [Field k] [Field K] [Algebra k K] [AddCommGroup E] [Module K E]
    [Module k E] [IsScalarTower k K E] [FiniteDimensional K E]
    (ψ : ι → Module.Dual K E), (∀ v : E, (∀ i, ψ i v = 0) → v = 0) →
    ∀ W : Submodule k E, Module.finrank k W = Module.finrank K E →
      (∀ v ∈ W, ∀ i, ψ i v ∈ (algebraMap k K).range) →
      (W : Set E) = {v : E | ∀ i, ψ i v ∈ (algebraMap k K).range}
def UniqueFormTwo : Prop :=
  ∀ (k K E ι : Type) [Field k] [Field K] [Algebra k K] [AddCommGroup E] [Module K E]
    [Module k E] [IsScalarTower k K E] [FiniteDimensional K E]
    (ψ : ι → Module.Dual K E), (∀ v : E, (∀ i, ψ i v = 0) → v = 0) →
    ∀ W₁ W₂ : Submodule k E,
      Module.finrank k W₁ = Module.finrank K E → Module.finrank k W₂ = Module.finrank K E →
      (∀ v ∈ W₁, ∀ i, ψ i v ∈ (algebraMap k K).range) →
      (∀ v ∈ W₂, ∀ i, ψ i v ∈ (algebraMap k K).range) → W₁ = W₂
def OneRationalStructure : Prop :=
  ∀ (k K E ι T : Type) [Field k] [Field K] [Algebra k K] [AddCommGroup E] [Module K E]
    [Module k E] [IsScalarTower k K E] [FiniteDimensional K E]
    (Z : T → Type) [∀ μ, AddCommGroup (Z μ)] [∀ μ, Module K (Z μ)] [∀ μ, Module k (Z μ)]
    [∀ μ, IsScalarTower k K (Z μ)]
    (ψ : ι → Module.Dual K E), (∀ v : E, (∀ i, ψ i v = 0) → v = 0) →
    ∀ (io : ∀ μ, Z μ →ₗ[K] E) (FinalFormK : ∀ μ, Submodule k (Z μ)) (c : T → k)
      (vv : ∀ μ, ι → Z μ → K),
      (∀ μ, Function.Bijective (io μ)) →
      (∀ μ, Module.finrank k (FinalFormK μ) = Module.finrank K (Z μ)) →
      (∀ μ, c μ ≠ 0) →
      (∀ μ, ∀ F ∈ FinalFormK μ, ∀ i, vv μ i F ∈ (algebraMap k K).range) →
      (∀ μ, ∀ F ∈ FinalFormK μ, ∀ i, ψ i (io μ F) = (algebraMap k K (c μ))⁻¹ * vv μ i F) →
      ∀ μ μ', (FinalFormK μ).map ((io μ).restrictScalars k) = (FinalFormK μ').map ((io μ').restrictScalars k)
def IntegralOfLocalUnits : Prop :=
  ∀ (R L : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (x : L) (ζ y : HeightOneSpectrum R → L),
    (∀ w : HeightOneSpectrum R, w.valuation L (ζ w) = 1) → (∀ w : HeightOneSpectrum R, w.valuation L (y w) ≤ 1) →
    (∀ w : HeightOneSpectrum R, ζ w * x = y w) → x ∈ (algebraMap R L).range
def OneMapIntegral : Prop :=
  ∀ (R L V EE : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L]
    [AddCommGroup V] [Module L V] [Module R V] [IsScalarTower R L V]
    [AddCommGroup EE] [Module L EE] [Module R EE] [IsScalarTower R L EE]
    (N : Submodule R V) (RR : Submodule R EE) (B : V →ₗ[L] EE →ₗ[L] L)
    (ζ : HeightOneSpectrum R → L) (P : HeightOneSpectrum R → V → EE → L),
    (∀ w : HeightOneSpectrum R, w.valuation L (ζ w) = 1) →
    (∀ w : HeightOneSpectrum R, ∀ φ ∈ N, ∀ F ∈ RR, w.valuation L (P w φ F) ≤ 1) →
    (∀ (w : HeightOneSpectrum R) φ F, ζ w * B φ F = P w φ F) →
    ∃ β : N →ₗ[R] Module.Dual R RR,
      ∀ (φ : N) (F : RR), algebraMap R L (β φ F) = B (φ : V) (F : EE)
def locAt {R EE : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup EE] [Module R EE]
    (w : HeightOneSpectrum R) (M : Submodule R EE) : Set EE :=
  {x : EE | ∃ s : R, s ∉ w.asIdeal ∧ s • x ∈ M}
def LatticeLocalGlobal : Prop :=
  ∀ (R L EE : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L] [AddCommGroup EE] [Module L EE] [Module R EE] [IsScalarTower R L EE]
    (Λ₀ : Submodule R EE) (Λ : HeightOneSpectrum R → Submodule R EE)
    (S : Finset (HeightOneSpectrum R)),
    Λ₀.FG → Submodule.span L (Λ₀ : Set EE) = ⊤ →
    (∀ (w : HeightOneSpectrum R) (s : R), s ∉ w.asIdeal → ∀ x : EE, s • x ∈ Λ w → x ∈ Λ w) →
    (∀ w : HeightOneSpectrum R, w ∉ S → (Λ w : Set EE) = locAt w Λ₀) →
    (∀ w ∈ S, ∃ a : R, a ≠ 0 ∧ (∀ x ∈ locAt w Λ₀, a • x ∈ Λ w) ∧
      (∀ x ∈ Λ w, a • x ∈ locAt w Λ₀)) →
    (⨅ w, Λ w).FG ∧ Submodule.span L ((⨅ w, Λ w : Submodule R EE) : Set EE) = ⊤ ∧
      ∀ w, locAt w (⨅ w', Λ w') = (Λ w : Set EE)
def GaussSumUnit : Prop :=
  ∀ (R L : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (𝔽 : Type) [Field 𝔽] [Fintype 𝔽] (χ : MulChar 𝔽 L) (ψ : AddChar 𝔽 L),
    χ ≠ 1 → ψ.IsPrimitive →
    ∀ w : HeightOneSpectrum R, (Fintype.card 𝔽 : R) ∉ w.asIdeal →
      w.valuation L (gaussSum χ ψ) = 1
def UnitProduct : Prop :=
  ∀ (R L : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (w : HeightOneSpectrum R) (roots gs others : List L) (qs : List (R × ℤ)),
    (∀ z ∈ roots, ∃ n : ℕ, 0 < n ∧ z ^ n = 1) →
    (∀ g ∈ gs, ∃ (𝔽 : Type) (_ : Field 𝔽) (_ : Fintype 𝔽) (χ : MulChar 𝔽 L)
      (ψ : AddChar 𝔽 L), χ ≠ 1 ∧ ψ.IsPrimitive ∧ (Fintype.card 𝔽 : R) ∉ w.asIdeal ∧
        g = gaussSum χ ψ) →
    (∀ p ∈ qs, p.1 ∉ w.asIdeal) →
    (∀ c ∈ others, w.valuation L c = 1) →
    w.valuation L (roots.prod * gs.prod * (qs.map fun p => algebraMap R L p.1 ^ p.2).prod *
      others.prod) = 1
def gram {K M n : Type} [CommRing K] [StarRing K] [AddCommGroup M] [Module K M]
    (B : M →ₗ⋆[K] M →ₗ[K] K) (v : n → M) : Matrix n n K :=
  Matrix.of fun i j => B (v i) (v j)
def GramChange : Prop :=
  ∀ (K M n : Type) [CommRing K] [StarRing K] [AddCommGroup M] [Module K M] [Fintype n]
    [DecidableEq n] (B : M →ₗ⋆[K] M →ₗ[K] K) (v : n → M) (g : Matrix n n K),
    gram B (fun j => ∑ i, g i j • v i) = g.conjTranspose * gram B v * g ∧
    (gram B (fun j => ∑ i, g i j • v i)).det = star g.det * g.det * (gram B v).det
def DualGram : Prop :=
  ∀ (K M n : Type) [Field K] [StarRing K] [AddCommGroup M] [Module K M] [Fintype n]
    [DecidableEq n] (B : M →ₗ⋆[K] M →ₗ[K] K), (∀ x y, star (B x y) = B y x) →
    ∀ (v : Module.Basis n K M) (w : n → M),
      (∀ i j, B (w i) (v j) = if i = j then 1 else 0) →
      gram B w = (gram B v)⁻¹ ∧ (gram B w).det * (gram B v).det = 1
def PrincipalDatumIdentity : Prop :=
  ∀ (Γ J : Type) [CommGroup Γ] [Fintype J] (ww wwb ll : J → Γ) (e : J → ℤ)
    (c cb Nc sd ddEK A0 A0b ddE xi0 : Γ),
    (∀ j, ll j = ww j * wwb j) →
    ddEK = ∏ j, ll j ^ e j → A0 = ∏ j, ww j ^ (-e j) → A0b = ∏ j, wwb j ^ (-e j) →
    c * cb = Nc → ddE = ddEK * sd → xi0 = Nc⁻¹ * sd⁻¹ →
    xi0 * (c * A0) * (cb * A0b) * ddE = 1
end Formalism.LatticeLocalGlobalTheory


