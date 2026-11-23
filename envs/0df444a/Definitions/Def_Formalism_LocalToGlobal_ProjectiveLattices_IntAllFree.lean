-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:16.48899+00:00
-- url     : https://prove2.me/theorems/2d28f8d4-8369-4874-87ec-571164157180
-- title:
--   Int All Free
-- statement:
--   Definitions and structural lemmas for Int All Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntAllFree.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.PjFree
open Formalism.L2.Pj
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
def IntAll : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → T.FinRes →
    ∀ y : (letI := io.toAlgebra; FrPt Xo c T.Fr),
      ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧
        letI := io.toAlgebra; letI := io'.toAlgebra
        ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ),
          (∀ a : T.V, φ (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) ∧ FrMap φ y z ∧ FrBor t z y'.1
end Formalism.L2.PjFree


