-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:57:17.278545+00:00
-- url     : https://prove2.me/theorems/5a488c0f-7e8c-491c-975c-39f0379fa99f
-- title:
--   Cusp Free
-- statement:
--   Definitions and structural lemmas for Cusp Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CuspFree.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
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
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
def cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  sec Xo c a n ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laU (U σ) a n)).comap (rdU (U σ))
def mulC (f g : Rul Xo c) : Rul Xo c := f * g
def CuspMul : Prop :=
  ∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), Dom a n → Dom a' n' → f ∈ cusp Xo c U a n →
    g ∈ cusp Xo c U a' n' → mulC Xo c f g ∈ cusp Xo c U (a + a') (n + n')
def CuspFD : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cusp Xo c U a n)
end Formalism.L2.PjFree


