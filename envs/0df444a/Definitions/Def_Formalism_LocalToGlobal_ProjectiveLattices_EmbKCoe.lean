-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:39:35.363958+00:00
-- url     : https://prove2.me/theorems/4a4dd30e-1c79-4c75-9af8-b25c747c498b
-- title:
--   Emb KCoe
-- statement:
--   Definitions and structural lemmas for Emb KCoe, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/EmbKCoe.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
abbrev Ix (Dw : Datum H) : Type := Option (Σ τ : E →+* ℂ, Fin (Dw.mult τ))
def ex (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Ix Dw → ℕ
  | none => n
  | some x => a (x.1, x.2)
def Dom (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop := (∀ τ, Antitone fun i => a (τ, i)) ∧ Even n
variable {l : Level H} (c : Coeff l)
instance : NumberField c.F where
  to_charZero := inferInstance
  to_finiteDimensional := c.fin
def embF (τ : E →+* ℂ) : E →+* c.F := τ.codRestrict c.F (c.conj τ)
def embK (τ : E →+* ℂ) : 𝓞 E →+* c.F := (embF c τ).comp (algebraMap (𝓞 E) E)
end Formalism.L2.Pj


