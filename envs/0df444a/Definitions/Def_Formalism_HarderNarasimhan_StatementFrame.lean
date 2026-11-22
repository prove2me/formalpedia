-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_StatementFrame
-- name    : Formalism_HarderNarasimhan_StatementFrame
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:18.778525+00:00
-- url     : https://prove2.me/theorems/05836992-76e9-461c-b657-6fd0aa0e56fe
-- title:
--   Statement Frame
-- statement:
--   Definitions and structural lemmas for Statement Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/StatementFrame.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_CorankShare_StatementFR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.CorankShareLayerCake.FR
noncomputable section
namespace Formalism.HN
def FrameHerm : Prop :=
  ∀ (K W κ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ) (c : I → ℝ)
    (s u HH e η : ℝ),
    (∀ w, IsUnit (X' w).det) → (∀ i w, IsUnit (X i w).det) → (∀ i, IsUnit (Y i).det) →
    IsUnit Y'.det →
    cc.FG → Submodule.span K (cc : Set W) = ⊤ →
    (∀ i, (N i).FG) → (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) →
    (∀ i, B i ≠ 0) → (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) →
    s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - htMap (b i) (X i) b' X' (B i)) →
    0 < u → (∀ i, muMaxDef (b i) (X i) (N i) - htMap (b i) (X i) b' X' (B i) ≤ s + u) →
    s - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    (∀ i, 0 < c i) →
    (∑ i, hs2 (frK (c i) (Matrix.toEuclideanLin
        (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 →
    (LinearMap.trace ℂ (EuclideanSpace ℂ κ)
        (frQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)) ∘ₗ
         frQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ κ)
        (frQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)))).re ^ 2 /
        (Fintype.card κ : ℝ) →
    0 ≤ η →
    s - Real.log (Fintype.card I : ℝ) - u * (1 + 4 * Real.log (1 + HH / u)) -
        (2 * η + 4 * Real.sqrt e) * HH ≤ muDef b' X' cc
def FrameHermSharp : Prop :=
  ∀ (K W κ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ) (c : I → ℝ)
    (s u HH e η : ℝ),
    (∀ w, IsUnit (X' w).det) → (∀ i w, IsUnit (X i w).det) → (∀ i, IsUnit (Y i).det) →
    IsUnit Y'.det →
    cc.FG → Submodule.span K (cc : Set W) = ⊤ →
    (∀ i, (N i).FG) → (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) →
    (∀ i, B i ≠ 0) → (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) →
    s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - htMap (b i) (X i) b' X' (B i)) →
    0 < u → (∀ i, muMaxDef (b i) (X i) (N i) - htMap (b i) (X i) b' X' (B i) ≤ s + u) →
    s - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    (∀ i, 0 < c i) →
    (∑ i, hs2 (frK (c i) (Matrix.toEuclideanLin
        (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 →
    (LinearMap.trace ℂ (EuclideanSpace ℂ κ)
        (frQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)) ∘ₗ
         frQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ κ)
        (frQ c (fun i => Matrix.toEuclideanLin
          (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i)))).re ^ 2 /
        (Fintype.card κ : ℝ) →
    0 ≤ η →
    s - 4 * u * Real.log (1 + HH / u) - (2 * η + 4 * Real.sqrt e) * HH ≤ muDef b' X' cc
end Formalism.HN


