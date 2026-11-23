-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEnc
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEnc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:19.713023+00:00
-- url     : https://prove2.me/theorems/8bb934d7-9a20-4511-8b8a-f95546b97839
-- title:
--   CInd Enc
-- statement:
--   Definitions and structural lemmas for CInd Enc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndEnc.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
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
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def ltEquiv (Dw : Datum H) (n : ℕ) : LtN Dw n ≃ (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) × Fin n where
  toFun ℓ := (⟨ℓ.1, ℓ.2.1⟩, ℓ.2.2)
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
def encP {Dw : Datum H} {n : ℕ} {K : Type} [CommRing K] (P : MvPolynomial (LtN Dw n) K) :
    MvPolynomial ((Σ τ : E →+* ℂ, Fin (Dw.mult τ)) × Fin n) K :=
  MvPolynomial.rename (ltEquiv Dw n) P
def HarmLinkSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
    ∀ τ : E →+* ℂ, InPsi H τ → ∀ (i : Fin (Dw.mult τ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
      ∑ b : Fin n, MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ))), b)
        (MvPolynomial.pderiv (((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ))), b)
          (encP P)) = 0
def ColLinkSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ)
    (m : LtN Dw n →₀ ℕ) (b : Fin n),
    colOf m b = ReciprocityTheory.ChartRestriction.G.TB.colM (Finsupp.equivMapDomain (ltEquiv Dw n) m) b
def PsiCoverSt (H : Host E) : Prop :=
  ∀ τ : E →+* ℂ, InPsi H τ ∨ InPsi H (ComplexEmbedding.conjugate τ)
end Formalism.MainNotions.ModuliIntegralCharts.H1


