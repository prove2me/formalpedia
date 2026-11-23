-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:41.022804+00:00
-- url     : https://prove2.me/theorems/523fc90f-9012-436c-bf58-1234cf2e2638
-- title:
--   Crude Base
-- statement:
--   Definitions and structural lemmas for Crude Base, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeBase.lean

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
namespace Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {R : Type} [CommRing R] {d n : ℕ}
def Lin (b : Fin n) (v : Fin d → R) (f : PS R n d) : PS R n d :=
  ∑ j : Fin d, C (v j) * pderiv R (b, j) f
def LinMon {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R n d) :
    PS R n d :=
  (Finset.univ : Finset ι).toList.foldr (fun l g => (Lin (cp l) (u l))^[m l] g) f
def OrdGe (N : ℕ) (f : PS R n d) : Prop :=
  ∀ m : Fin n × Fin d →₀ ℕ, m.degree < N → coeff m f = 0
end Formalism.L2.Pj.Crude


