-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_PtFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:54:17.647005+00:00
-- url     : https://prove2.me/theorems/c73b64fe-ed81-401e-aacc-2ac6bc3de47a
-- title:
--   Pt Free
-- statement:
--   Definitions and structural lemmas for Pt Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PtFree.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RulInst
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero

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
open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
section One
variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
structure IsVal (la : HeightOneSpectrum (𝓞 K)) (v : R → EReal) : Prop where
  zero : v 0 = ⊤
  ne_bot : ∀ r, v r ≠ ⊥
  add : ∀ r s, min (v r) (v s) ≤ v (r + s)
  smul : ∀ (a : K) r, a ≠ 0 → v (a • r) = (((vLa la a : ℤ) : ℝ) : EReal) + v r
  mul : ∀ r s, v (r * s) = v r + v s
structure IsNormOn (C : Submodule K R) (σ : K →+* ℂ) (N : R → ℝ) : Prop where
  nonneg : ∀ f ∈ C, 0 ≤ N f
  defin : ∀ f ∈ C, N f = 0 → f = 0
  smul : ∀ (a : K), ∀ f ∈ C, N (a • f) = ‖σ a‖ * N f
  add : ∀ f ∈ C, ∀ g ∈ C, N (f + g) ≤ N f + N g
end One
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop)
def algCls (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι) : Prop := y.IsAlg
def valSet (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) :=
  Set.range (vAtV : PtV Xo c cls Unit (fun _ _ _ _ => True) la → Rul Xo c → EReal)
variable {Xo c cls}
variable (Xo c cls)
def LiesTotal (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ la (T : CDVR) (ι : c.F →+* T.Fr) (e : ℕ), OverLa la T.V ι e → ∀ y : IntFr Xo c T ι, cls T ι y →
    ∃ η, lies la T ι y η
variable {Xo c cls}
end Formalism.L2.PjFree


