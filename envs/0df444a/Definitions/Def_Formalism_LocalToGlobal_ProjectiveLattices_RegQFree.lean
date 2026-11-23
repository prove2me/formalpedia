-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:53:36.456652+00:00
-- url     : https://prove2.me/theorems/bf79b4ca-f5c6-40e8-877a-a745faa6e8a5
-- title:
--   Reg QFree
-- statement:
--   Definitions and structural lemmas for Reg QFree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RegQFree.lean

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
def trivCls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop :=
  fun T ι _ => ∀ a : c.F, a ≠ 0 → ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = ι a
structure QPt where
  T : CDVR
  ι : c.F →+* T.Fr
  y : IntFr Xo c T ι
  triv : trivCls Xo c T ι y
def ordQ (q : QPt Xo c) (f : Rul Xo c) : EReal := nval q.T.V 1 (evI q.y f)
def RegularityR1Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n,
    (∃ la : HeightOneSpectrum (𝓞 c.F), ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) →
      ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q f
def RegularityR2Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ) (aE : (E →+* ℂ) × ℕ → ℕ) (nE k : ℕ) (ws : Fin k → Rul Xo c)
    (et : Rul Xo c) (c' : ℝ), 0 ≤ c' → (∀ i, ws i ∈ C aL nL) → et ∈ C aE nE →
    (∃ (la : HeightOneSpectrum (𝓞 c.F)) (nu : ℝ), ∀ v ∈ valSet Xo c (algCls Xo c) la,
      0 ≤ v et ∧ (∃ i, v (ws i) ≠ ⊤) ∧ (v et ≠ ⊤ → (⨅ i, v (ws i)) ≤ (nu : EReal) + (c' : EReal) * v et)) →
    ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q et ∧
      (ordQ Xo c q et ≠ ⊤ → (⨅ i, ordQ Xo c q (ws i)) ≤ (c' : EReal) * ordQ Xo c q et)
end Formalism.L2.PjFree


