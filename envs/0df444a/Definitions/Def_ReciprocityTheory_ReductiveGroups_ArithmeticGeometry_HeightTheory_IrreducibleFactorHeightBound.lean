-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorHeightBound
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorHeightBound
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-27T04:48:00.602546+00:00
-- url     : https://prove2.me/theorems/d0b5c232-42fa-4dfa-a3ba-55a63c0ed9b5
-- title:
--   Irreducible Factor Height Bound
-- statement:
--   Definitions and structural lemmas for Irreducible Factor Height Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/IrreducibleFactorHeightBound.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightKerScaledSubstitutionLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorStructure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightLeTorusHeightSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
abbrev UXVar (D N : ℕ) : Type := (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)
def xDeg {D N : ℕ} (s : UXVar D N →₀ ℕ) : ℕ := ∑ i, s (Sum.inr i)
def uDeg {D N : ℕ} (s : UXVar D N →₀ ℕ) : ℕ := ∑ p, s (Sum.inl p)
def XHom {R : Type*} [CommSemiring R] {D N : ℕ} (n : ℕ) (Q : MvPolynomial (UXVar D N) R) : Prop :=
  ∀ s ∈ Q.support, xDeg s = n
def UDegLE {R : Type*} [CommSemiring R] {D N : ℕ} (n : ℕ) (Q : MvPolynomial (UXVar D N) R) :
    Prop :=
  ∀ s ∈ Q.support, uDeg s ≤ n
noncomputable def hT {κ : Type} [Fintype κ] (f : MvPolynomial κ K) : ℝ :=
  ((∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w f)) +
      ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ f)) / (Module.finrank ℚ K : ℝ)
namespace Data
variable (d : Data K ι Ω WT A)
noncomputable def evc (c : ι) :
    MvPolynomial (UXVar d.D d.N) K →ₐ[K] MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (A c) :=
  MvPolynomial.aeval fun v =>
    match v with
    | Sum.inl p => MvPolynomial.X p
    | Sum.inr i => ∑ j, MvPolynomial.X (i, j) * MvPolynomial.C (d.w j c)
noncomputable def laW : ℝ := meanK fun sg => ⨆ j, Real.log (d.supN sg d.wL (d.w j))
noncomputable def upB : ℝ :=
  d.PP0' * d.wsize d.wL + max 0 d.laW + Real.log (d.N + 1 : ℕ) + 1
end Data
end ReciprocityTheory.ChartRestriction.G.T0


