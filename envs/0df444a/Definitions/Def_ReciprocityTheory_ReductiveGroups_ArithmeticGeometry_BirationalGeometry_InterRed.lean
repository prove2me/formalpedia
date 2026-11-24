-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:57.843425+00:00
-- url     : https://prove2.me/theorems/0457170c-9058-40fa-98e4-cee32cbca971
-- title:
--   Inter Red
-- statement:
--   Definitions and structural lemmas for Inter Red, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRed.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M
def ResDivPushStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι)
    (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set R.X) (BW : ∀ k, FinHolAtlas n (W k)),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W →
    (∀ k, HoloMap (BW k) R.A Subtype.val) →
    ∑ k, (m k : ℝ) * mInt (BW k)
        (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val)
        ((fun x => Real.log (B.h (R.lift x x))) ∘ Subtype.val) =
      ∑ᶠ (W') (_ : W' ∈ divSupp P s ∧ IsHorizontal W'),
        (multAt (P ⊔ Ideal.span {s}) W' : ℝ) * ptsIntegral W' (pot L) (fun z => Real.log (B.h z))
end ReciprocityTheory.ChartRestriction.G.Geo


