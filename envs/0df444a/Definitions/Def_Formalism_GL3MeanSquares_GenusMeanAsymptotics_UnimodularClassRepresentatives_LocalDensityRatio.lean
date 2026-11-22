-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:19.264803+00:00
-- url     : https://prove2.me/theorems/e3b14ffb-fef5-46ac-bee4-4f2fe360befa
-- title:
--   Local Density Ratio
-- statement:
--   Definitions and structural lemmas for Local Density Ratio, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityRatio.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
def IsFixF (K F : Type) [Field K] [StarRing K] [Field F] [Algebra F K] : Prop :=
  ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)
def extP (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) :
    Ideal (𝓞 K) :=
  𝔭.map (algebraMap (𝓞 F) (𝓞 K))
def locF {K F W : Type} [Field K] [Field F] [Algebra F K] [AddCommGroup W] [Module (𝓞 K) W]
    (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) W) : Submodule (𝓞 K) W :=
  Formalism.HermitianLatticesTheory.locS (Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) L
def CongrP {K F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a b : K) :
    Prop :=
  ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z ∈ extP K 𝔭 ^ k,
    algebraMap (𝓞 K) K z = algebraMap F K (t : F) * (a - b)
def vF {F : Type} [Field F] (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F) : ℕ := sSup {e : ℕ | n ∈ 𝔭 ^ e}
def alphaStd (K : Type) {F : Type} [Field K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 m, (1 - etaF K F 𝔭 ^ j * (Ideal.absNorm 𝔭 : ℝ) ^ (-(j : ℤ)))
section Defs
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
def nkCount (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (n : 𝓞 F) : ℕ :=
  Nat.card {x : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) //
    ∃ y : ↥L, Submodule.Quotient.mk y = x ∧
      CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F))}
def akCount (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : ℕ :=
  Nat.card {X : Module.End (𝓞 K) (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) //
    ∀ x y x' y' : ↥L, Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))}
def alphaN (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F) : ℝ :=
  limUnder atTop fun k : ℕ =>
    (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1))
def alphaL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℝ :=
  limUnder atTop fun k : ℕ =>
    (akCount h L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2)
def discrIdeal (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : Ideal (𝓞 K) :=
  Ideal.span {z : 𝓞 K | ∃ x : Fin (finrank K V) → V, (∀ i, x i ∈ L) ∧
    algebraMap (𝓞 K) K z = (Matrix.of fun i j => h (x i) (x j)).det}
def vd (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℕ :=
  sSup {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e}
def normD (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : ℝ :=
  Real.sqrt (Ideal.absNorm (discrIdeal h L) : ℝ)
def lamP (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℝ :=
  alphaStd K 𝔭 (finrank K V) * (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h L 𝔭) / alphaL h L 𝔭
def lamG (F : Type) [Field F] [NumberField F] [Algebra F K] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) : ℝ :=
  ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, lamP h L 𝔭.1
def singS (F : Type) [Field F] [NumberField F] [Algebra F K] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) (n : 𝓞 F) : ℝ :=
  ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaN h L 𝔭.1 n /
    (1 - etaF K F 𝔭.1 ^ finrank K V * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))
def fibLoc {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} (S : VecSplit h h')
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (T : Submodule (𝓞 K) V') : ℕ :=
  Nat.card {Λ : Submodule (𝓞 K) V // locF 𝔭 Λ = Λ ∧
    (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = Λ) ∧ S.x₀ ∈ Λ ∧ S.cut Λ = locF 𝔭 T}
def IsIntegralAt {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    (𝔭 : Ideal (𝓞 F)) (h₀ : W →ₗ⋆[K] W →ₗ[K] K) (T : Submodule (𝓞 K) W) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, h₀ x y ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
def IsLocReps {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} (S : VecSplit h h')
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (s : Finset (Submodule (𝓞 K) V')) : Prop :=
  (∀ T ∈ s, locF 𝔭 T = T ∧ IsIntegralAt 𝔭 h' T ∧ fibLoc S L 𝔭 T ≠ 0) ∧
  ∀ T : Submodule (𝓞 K) V', locF 𝔭 T = T → IsIntegralAt 𝔭 h' T → fibLoc S L 𝔭 T ≠ 0 →
    ∃! T₀, T₀ ∈ s ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g T₀ = T
def psiP {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} (S : VecSplit h h')
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℝ := by
  classical
  exact if hs : ∃ s, IsLocReps S L 𝔭 s then
    ∑ T ∈ hs.choose, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 else 0
def orbCount (h : V →ₗ⋆[K] V →ₗ[K] K) (A B : Submodule (𝓞 K) V) : ℕ :=
  Nat.card {C : Submodule (𝓞 K) V // ∃ g ∈ Formalism.HermitianLatticesTheory.isom h,
    Formalism.HermitianLatticesTheory.gmap g A = A ∧ Formalism.HermitianLatticesTheory.gmap g B = C}
def ballCount (h : V →ₗ⋆[K] V →ₗ[K] K) (Λ : Submodule (𝓞 K) V) (T : ℝ) : ℕ :=
  Nat.card {x : V // x ∈ Λ ∧ ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ T}
end Defs
def boxSet (K F : Type) [Field K] [Field F] [Algebra F K] (T : ℝ) : Set (𝓞 F) :=
  {n | ∀ φ : K →+* ℂ, 0 < (φ (algebraMap F K (n : F))).re ∧ (φ (algebraMap F K (n : F))).re ≤ T}
def MassConst (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] (m : ℕ) (c : ℝ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V),
    h.IsSymm → IsTotPosDef h → finrank K V = m → Submodule.IsLattice K L →
    Formalism.HermitianLatticesTheory.IsIntegralLat h L → Formalism.HermitianLatticesTheory.mass h L = c * lamG F h L
def LIStat : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
      [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K)
      (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
      (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F),
      h.IsSymm → IsTotPosDef h → 𝔭.IsMaximal → n ≠ 0 → h S.x₀ S.x₀ = algebraMap F K (n : F) →
      Submodule.IsLattice K L → Formalism.HermitianLatticesTheory.IsIntegralLat h L →
      psiP S L 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * (vF 𝔭 n + vd h L 𝔭)) *
        alphaStd K 𝔭 (finrank K V - 1) * alphaN h L 𝔭 n / alphaL h L 𝔭
def LocalDensityRatio : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F →
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (A₀ B₀ : Submodule (𝓞 K) V)
      (𝔭 : Ideal (𝓞 F)),
      h.IsSymm → IsTotPosDef h → 𝔭.IsMaximal → Submodule.IsLattice K A₀ →
      Submodule.IsLattice K B₀ → Formalism.HermitianLatticesTheory.IsIntegralLat h A₀ → Formalism.HermitianLatticesTheory.IsIntegralLat h B₀ →
      alphaL h (locF 𝔭 A₀) 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) *
          orbCount h (locF 𝔭 B₀) (locF 𝔭 A₀) =
        alphaL h (locF 𝔭 B₀) 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 A₀) 𝔭) *
          orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀)
end Formalism.HermitianLattices.Ext.L3


