-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:07.666195+00:00
-- url     : https://prove2.me/theorems/54dd08db-39ee-4a93-b399-0b1958a14b1b
-- title:
--   Mul Gen Scale Right
-- statement:
--   Definitions and structural lemmas for Mul Gen Scale Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/MulGenScaleRight.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_sub

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MvPolynomial (X)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)
def tw (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (m : ℕ) : FrTy y d x m :=
  scaleGen _ _ (unitΓ (T m)) (e m)
abbrev sub (m : ℕ) {n' : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S)
    (T : (Jet S (Fin 2 × Fin d) m)ˣ) : (Jet S (Fin n' × Fin d) m)ˣ :=
  Units.map (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2).toMonoidHom T
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2


