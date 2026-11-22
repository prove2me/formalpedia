-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:56.107557+00:00
-- url     : https://prove2.me/theorems/3d68a666-78d2-4a9e-af24-46cf9cfe8355
-- title:
--   Mass Land St
-- statement:
--   Definitions and structural lemmas for Mass Land St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandSt.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
def TotPos {K : Type*} [Field K] (a : K) : Prop :=
  ∀ φ : K →+* ℂ, 0 < (φ a).re
def gram {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {n : ℕ}
    (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin n → V) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => h (e i) (e j)
def HermRepUnram : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ a b n : K, star a = a → star b = b → star n = n → TotPos a → TotPos b → TotPos n →
      ∃ s t : K, a * (s * star s) + b * (t * star t) = n
def OrthBasisPos : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
      h.IsSymm → IsTotPosDef h →
      ∃ e : Basis (Fin (finrank K V)) K V, (∀ i j, i ≠ j → h (e i) (e j) = 0) ∧
        ∀ i, star (h (e i) (e i)) = h (e i) (e i) ∧ TotPos (h (e i) (e i))
def LandherrDefUnram : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (n : ℕ) (V W : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
      [IsScalarTower (𝓞 K) K W] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : W →ₗ⋆[K] W →ₗ[K] K),
      h.IsSymm → h'.IsSymm → IsTotPosDef h → IsTotPosDef h' →
      ∀ (b : Basis (Fin n) K V) (b' : Basis (Fin n) K W) (k : K), k ≠ 0 →
        (gram h b).det = k * star k * (gram h' b').det →
        ∃ g : V ≃ₗ[K] W, ∀ x y, h' (g x) (g y) = h x y
end Formalism.HermitianLattices.Ext.L3


