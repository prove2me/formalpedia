-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqSt
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:01.727181+00:00
-- url     : https://prove2.me/theorems/ec831913-3386-4f43-9aa4-5d872f8c96e0
-- title:
--   Exp Uniq St
-- statement:
--   Definitions and structural lemmas for Exp Uniq St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqSt.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPolynomial (X)
attribute [local instance] Over.cartesianMonoidalCategory
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {S : Type} [CommRing S]
def IsExpHomR (x0 : Sp S ⟶ Xo.X) (d : ℕ) (x : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G) : Prop :=
  (∀ m, homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ x (m + 1) = x m) ∧
  ∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d =>
      (X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2) : MvPolynomial (Fin 2 × Fin d) S)) ≫ x m =
    (homAt x0 (jetCopy d m (0 : Fin 2) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m) ≫ x m) *
      (homAt x0 (jetCopy d m (1 : Fin 2) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m) ≫ x m)
def SameTanR (x0 : Sp S ⟶ Xo.X) (d : ℕ) (x x' : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G) : Prop :=
  ∀ j : Fin d,
    homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1 =
      homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x' 1
end
def ExpUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (d : ℕ) (x x' : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G),
    IsExpHomR y.x d x → IsExpHomR y.x d x' → SameTanR y.x d x x' → x = x'
def ExpUniqRawSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (S : Type) [CommRing S] [Algebra ℚ S] (x0 : Sp S ⟶ Xo.X) (d : ℕ)
    (x x' : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G),
    IsExpHomR x0 d x → IsExpHomR x0 d x' → SameTanR x0 d x x' → x = x'
def ExpUniqLocSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (S : Type) [CommRing S] [IsLocalRing S] [Algebra ℚ S] (x0 : Sp S ⟶ Xo.X) (d : ℕ)
    (x x' : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G),
    IsExpHomR x0 d x → IsExpHomR x0 d x' → SameTanR x0 d x x' → x = x'
end Formalism.MainNotions.ModuliIntegralCharts.H1


