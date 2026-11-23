-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:37.006816+00:00
-- url     : https://prove2.me/theorems/79e10f8b-762c-486d-bf38-01144d5293f5
-- title:
--   Germ DJet
-- statement:
--   Definitions and structural lemmas for Germ DJet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermDJet.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open AlgebraicGeometry CategoryTheory MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Alg
variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}
end Alg
section Subst
variable {R : Type} [CommRing R] {d : ℕ}
abbrev sL (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    Jet R (Fin 2 × Fin d) m →ₐ[R] Jet R (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (g j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) R) p.1 p.2
end Subst
section Over
variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
end Over
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD


