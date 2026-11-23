-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:48.341705+00:00
-- url     : https://prove2.me/theorems/ee70a6d2-b0ee-4d46-bc4b-2db2629eb9a7
-- title:
--   Fourier Cube Volume
-- statement:
--   Definitions and structural lemmas for Fourier Cube Volume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCubeVolume.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section
section Gen
variable {ι : Type} [Fintype ι] {N : ℕ} (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ)
def Bv (t : Fin N → ℝ) : ι → Fin 2 → Fin 2 → ℂ := ∑ j, (t j : ℂ) • ω j
def ech (χ : ι → Fin 2 → Fin 2 → ℂ) (t : Fin N → ℝ) : ℂ :=
  cexp (-(4 * Real.pi * I) * (pr χ (Bv ω t) : ℂ))
end Gen
def cube (N : ℕ) : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1
section Mean
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E) (g : ℕ) (ω : Fin (4 * Fintype.card X.Ψ) → X.Ψ → Fin 2 → Fin 2 → ℂ)
  (G : Frame X.Ψ r → ℂ)
def Ich (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∫ t in cube (4 * Fintype.card X.Ψ), G (X.Zb u (Bv ω t) x) * ech ω χ t
variable {X u g ω G}
variable (hω : X.IsLZBasis g ω)
  (hadd : ∀ b b' x, X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x)
  (hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom)
end Mean
end
end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume


