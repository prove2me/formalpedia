-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:16.253737+00:00
-- url     : https://prove2.me/theorems/e8513eeb-9032-4e19-81af-0f880111a85d
-- title:
--   Reg PFree
-- statement:
--   Definitions and structural lemmas for Reg PFree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RegPFree.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegLaw
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
def trivialClassCondition (T : CDVR) (io : c.F →+* T.Fr) (_y : IntFr Xo c T io) : Prop := True
theorem valSet_alg_subset (la : HeightOneSpectrum (𝓞 c.F)) :
    valSet Xo c (algCls Xo c) la ⊆ valSet Xo c (trivialClassCondition Xo c) la := by
  rintro _ ⟨y, rfl⟩
  exact ⟨PtV.widen (fun _ _ _ _ => trivial) y, rfl⟩
def trivSet : Set (Rul Xo c → EReal) :=
  {q | ∃ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io),
    (∀ a : c.F, a ≠ 0 → vV T.V (io a) = 0) ∧ q = fun f => nval T.V 1 (evI y f)}
def NoCommonZero {n : ℕ} (ws : Fin n → Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), ∃ i, evR Xo c (ws i) y ≠ 0
abbrev DomWt (E : Type) [Field E] : Type := {x : ((E →+* ℂ) × ℕ → ℕ) × ℕ // Dom x.1 x.2}
def regular₂ {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ReciprocityTheory.ChartRestriction.G.T0.RegLaw (Λ := HeightOneSpectrum (𝓞 c.F)) (Wt := DomWt E)
    (fun w => cusp Xo c U w.1.1 w.1.2)
    (fun la => valSet Xo c (algCls Xo c) la) (fun la => valSet Xo c (trivialClassCondition Xo c) la)
    (fun la v => ⟨v.1, valSet_alg_subset Xo c la v.2⟩) (fun _ v _ F => v.1 F.1)
    (trivSet Xo c) (fun q _ F => q.1 F.1) (fun ws => NoCommonZero Xo c fun i => (ws i).1) ∧
  ∀ a n, Dom a n → ∀ (m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ cusp Xo c U a n) → NoCommonZero Xo c ws →
    ∀ nu : HeightOneSpectrum (𝓞 c.F) → ℝ,
      (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)) →
        ∀ la, ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)
variable {Xo c}
end Formalism.L2.PjFree


