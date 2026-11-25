-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:56:35.936321+00:00
-- url     : https://prove2.me/theorems/6ea87c4c-2818-490b-a64d-28ffb4790da4
-- title:
--   Formal Group On Copies
-- statement:
--   Definitions and structural lemmas for Formal Group On Copies, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupOnCopies.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace FormalGroupOnCopies
def OnCopies {k : Type} [CommRing k] {n d : ℕ} (S : Finset (Fin n)) (f : PS k n d) : Prop :=
  ∀ mm : Fin n × Fin d →₀ ℕ, coeff mm f ≠ 0 → ∀ i ∈ mm.support, i.1 ∈ S
end FormalGroupOnCopies
open FormalGroupOnCopies
def ColumnsStatement : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O),
    constantCoeff (B.hL k h w0) = 0 →
    ∀ (m n : ℕ) (S : Finset (Fin n)) (f₁ f₂ : PS k n d) (ι : Type) [Fintype ι]
      (cp : ι → Fin n) (u : ι → Fin d → k) (P₁ P₂ : MvPolynomial ι k),
      OnCopies S f₁ → OnCopies Sᶜ f₂ → (∀ l ∈ P₁.vars, cp l ∈ S) → (∀ l ∈ P₂.vars, cp l ∉ S) →
      nabValN B k h w0 m (f₁ * f₂) cp u (P₁ * P₂) =
        nabValN B k h w0 m f₁ cp u P₁ * nabValN B k h w0 m f₂ cp u P₂
end Formalism.MainNotions.ModuliIntegralCharts.H1


