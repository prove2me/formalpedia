-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:11:01.0444+00:00
-- url     : https://prove2.me/theorems/feace617-18e8-48ab-80ff-fb62438860d1
-- title:
--   Loc Struct St
-- statement:
--   Definitions and structural lemmas for Loc Struct St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalIntegralPolynomials/LocStructSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.LocAlg
open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
def GenAt (K : Type) {Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ} (jc : Fin (N + 1))
    (x : Fin N → Ω) (V : ValuationSubring (OmS Ω D N)) : Prop :=
  ∃ ht : ∀ p, sImg jc x p ∈ V,
    letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra V (algebraMap Ω (OmS Ω D N))
    letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (V.comap (algebraMap Ω (OmS Ω D N))) (algebraMap K Ω)
    letI : Algebra (IsLocalRing.ResidueField
        ((V.comap (algebraMap Ω (OmS Ω D N))).comap (algebraMap K Ω))) (IsLocalRing.ResidueField V) :=
      ((algebraMap _ (IsLocalRing.ResidueField V)).comp
        (algebraMap _ (IsLocalRing.ResidueField (V.comap (algebraMap Ω (OmS Ω D N)))))).toAlgebra
    AlgebraicIndependent
      (IsLocalRing.ResidueField ((V.comap (algebraMap Ω (OmS Ω D N))).comap (algebraMap K Ω)))
      (fun p => IsLocalRing.residue V ⟨sImg jc x p, ht p⟩)
def PtSepSt : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D N : ℕ) (jc : Fin (N + 1)) (x : Fin N → Ω),
    Algebra.trdeg K Ω = D →
    ∀ V V' : ValuationSubring (OmS Ω D N), GenAt K jc x V → GenAt K jc x V' →
      V.comap (algebraMap Ω (OmS Ω D N)) = V'.comap (algebraMap Ω (OmS Ω D N)) → V = V'
def LocStructSt : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D N : ℕ) (jc : Fin (N + 1)) (x : Fin N → Ω),
    Algebra.trdeg K Ω = D →
    ∀ (Z : Type) [Fintype Z] (v : Z → Valuation (OmS Ω D N) (WithZero (Multiplicative ℤ))),
      (∀ ζ, GenAt K jc x (v ζ).valuationSubring) →
      (∀ ζ, ∃ a : OmS Ω D N,
        v ζ a = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      ∀ g : OmS Ω D N, (∀ ζ, v ζ g ≤ 1) →
      ∃ f d : MvPolynomial (TVar D N) Ω,
        (∀ ζ e, v ζ (algebraMap Ω (OmS Ω D N) (f.coeff e)) ≤ 1) ∧
        (∀ ζ e, v ζ (algebraMap Ω (OmS Ω D N) (d.coeff e)) ≤ 1) ∧
        (∀ ζ, v ζ (aeval (sImg jc x) d) = 1) ∧
        aeval (sImg jc x) f = aeval (sImg jc x) d * g
end Formalism.L2.Pj.LocAlg


