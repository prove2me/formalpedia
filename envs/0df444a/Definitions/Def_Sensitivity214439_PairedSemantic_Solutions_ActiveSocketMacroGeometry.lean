-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
-- name    : Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T20:22:52.090721+00:00
-- url     : https://prove2.me/theorems/022849ef-8f90-4c71-a70d-aaea1ac8427a
-- title:
--   Active-side conflict geometry and inactive tokens
-- statement:
--   For physical rows $v=(m,b)$ with a chosen active side $a(v)$, define a conflict between distinct rows when they share a macro or when a macro arc selects the active side at its destination. Independence means absence of all such conflicts. A directed conflict is a paired arc whose guard contains the destination's selected side.
--
--   The inactive token of $v$ is $(m,\neg a(v))$. An independent row set has injective macro projection and maps to an equally large compatible token clique. A marker cleanly dominates a row when its macro arc selects the inactive side; this becomes the marked-token condition. These bridges transfer finite token-clique caps to physical row populations.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/ActiveSocketMacroGeometry.lean lines 21–176; SHA256 745d14738e6e657e3f16e79a0836e3cda18124fa37719ea8d258c13fa013f29e; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroTokenSemantics
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentGuardCoverage
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentSocketGuards
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityActiveSocketGeometry
end SensitivityActiveSocketGeometry
namespace SensitivityCyclicTokens
end SensitivityCyclicTokens
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
Actual selected positive sockets induce the macro conflict graph used in the
population argument. An independent set contains at most one row per macro.
The complement of each selected socket is a coherent token. Every directed
conflict pays for a different actually active guard, including internal OR
checks. Clean domination gives exactly the literal perfect-marker condition.
-/

namespace SensitivityActiveSocketGeometry

noncomputable section
open scoped Classical Fin.CommRing
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge SensitivityCyclicTokens
set_option autoImplicit false

variable {M B I Color : Type} {L n : ℕ}

def Conflict (arc : M → M → Prop) (label : M → M → Bool)
    (active : M × B → Bool) (v w : M × B) : Prop :=
  v ≠ w ∧ (v.1 = w.1 ∨
    (arc v.1 w.1 ∧ label v.1 w.1 = active w) ∨
    (arc w.1 v.1 ∧ label w.1 v.1 = active v))

def Independent (arc : M → M → Prop) (label : M → M → Bool)
    (active : M × B → Bool) (vertices : Finset (M × B)) : Prop :=
  ∀ v ∈ vertices, ∀ w ∈ vertices, ¬ Conflict arc label active v w

theorem conflict_irrefl (arc : M → M → Prop) (label : M → M → Bool)
    (active : M × B → Bool) (v : M × B) : ¬ Conflict arc label active v v := by
  intro h
  exact h.1 rfl

theorem conflict_symm {arc : M → M → Prop} {label : M → M → Bool}
    {active : M × B → Bool} {v w : M × B}
    (h : Conflict arc label active v w) : Conflict arc label active w v := by
  refine ⟨Ne.symm h.1, ?_⟩
  rcases h.2 with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem Independent.macro_injective {arc : M → M → Prop} {label : M → M → Bool}
    {active : M × B → Bool} {vertices : Finset (M × B)}
    (hind : Independent arc label active vertices) :
    Set.InjOn Prod.fst (↑vertices : Set (M × B)) := by
  intro v hv w hw heq
  by_contra hne
  exact hind v hv w hw ⟨hne, Or.inl heq⟩

theorem Independent.label_avoids {arc : M → M → Prop} {label : M → M → Bool}
    {active : M × B → Bool} {vertices : Finset (M × B)}
    (hind : Independent arc label active vertices)
    {v w : M × B} (hv : v ∈ vertices) (hw : w ∈ vertices)
    (hne : v ≠ w) (harc : arc v.1 w.1) : label v.1 w.1 ≠ active w := by
  intro heq
  exact hind v hv w hw ⟨hne, Or.inr (Or.inl ⟨harc, heq⟩)⟩

def boolBit (b : Bool) : Fin 2 := if b then 1 else 0

def inactiveToken (active : Fin n × B → Bool) (v : Fin n × B) : Fin n × Fin 2 :=
  (v.1, boolBit (!(active v)))

theorem eq_not_of_ne {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

theorem fin_sub_value [NeZero n] (v w : Fin n) :
    (w - v).val = (w.val + n - v.val) % n := by
  rw [Fin.val_sub]
  congr 1
  have hv := v.isLt
  omega

theorem circulantArc_iff [NeZero n] (orient : ℕ) (v w : Fin n) :
    circulantArc orient v w ↔ orient.testBit (w - v).val = true := by
  rw [fin_sub_value]
  rfl

theorem circulantLabel_bit [NeZero n] (labels : ℕ) (v w : Fin n) :
    boolBit (circulantLabel labels v w) = labelBit labels (w - v) := by
  rw [labelBit, fin_sub_value]
  rfl

theorem independent_token_clique [NeZero n]
    (orient labels : ℕ) (active : Fin n × B → Bool)
    (hcovers : CoversPairs (@circulantArc n orient))
    (vertices : Finset (Fin n × B))
    (hind : Independent (circulantArc orient) (circulantLabel labels) active vertices) :
    TokenClique orient labels (vertices.image (inactiveToken active)) := by
  intro a ha b hb hne
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
  have hvw : v ≠ w := by intro h; exact hne (h ▸ rfl)
  have hm : v.1 ≠ w.1 := by
    intro h
    exact hvw (hind.macro_injective hv hw h)
  rcases hcovers v.1 w.1 hm with hfor | hback
  · left
    refine ⟨(circulantArc_iff orient v.1 w.1).mp hfor, ?_⟩
    have hlabel := eq_not_of_ne (hind.label_avoids hv hw hvw hfor)
    change boolBit (!(active w)) = labelBit labels (w.1 - v.1)
    rw [← hlabel]
    exact circulantLabel_bit labels v.1 w.1
  · right
    refine ⟨(circulantArc_iff orient w.1 v.1).mp hback, ?_⟩
    have hlabel := eq_not_of_ne (hind.label_avoids hw hv (Ne.symm hvw) hback)
    change boolBit (!(active v)) = labelBit labels (v.1 - w.1)
    rw [← hlabel]
    exact circulantLabel_bit labels w.1 v.1

theorem independent_token_card [NeZero n]
    (orient labels : ℕ) (active : Fin n × B → Bool)
    (vertices : Finset (Fin n × B))
    (hind : Independent (circulantArc orient) (circulantLabel labels) active vertices) :
    (vertices.image (inactiveToken active)).card = vertices.card := by
  apply Finset.card_image_iff.mpr
  intro v hv w hw heq
  exact hind.macro_injective hv hw (congrArg (fun t : Fin n × Fin 2 => t.1) heq)

def CleanlyDominates (arc : M → M → Prop) (label : M → M → Bool)
    (active : M × B → Bool) (marker : M) (v : M × B) : Prop :=
  arc marker v.1 ∧ label marker v.1 ≠ active v

theorem cleanlyDominates_marked [NeZero n]
    (orient labels : ℕ) (active : Fin n × B → Bool)
    (marker : Fin n) (v : Fin n × B)
    (h : CleanlyDominates (circulantArc orient) (circulantLabel labels)
      active marker v) : marked orient labels marker (inactiveToken active v) := by
  refine ⟨(circulantArc_iff orient marker v.1).mp h.1, ?_⟩
  change boolBit (!(active v)) = labelBit labels (v.1 - marker)
  rw [← eq_not_of_ne h.2]
  exact circulantLabel_bit labels marker v.1

theorem token_image_marked [NeZero n]
    (orient labels : ℕ) (active : Fin n × B → Bool)
    (marker : Fin n) (vertices : Finset (Fin n × B))
    (hdom : ∀ v ∈ vertices,
      CleanlyDominates (circulantArc orient) (circulantLabel labels) active marker v) :
    ∀ token ∈ vertices.image (inactiveToken active), marked orient labels marker token := by
  intro token htoken
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp htoken
  exact cleanlyDominates_marked orient labels active marker v (hdom v hv)

theorem independent_card_le [NeZero n]
    (orient labels cap : ℕ) (active : Fin n × B → Bool)
    (hcovers : CoversPairs (@circulantArc n orient))
    (hcap : ∀ tokens : Finset (Fin n × Fin 2),
      TokenClique orient labels tokens → tokens.card ≤ cap)
    (vertices : Finset (Fin n × B))
    (hind : Independent (circulantArc orient) (circulantLabel labels) active vertices) :
    vertices.card ≤ cap := by
  rw [← independent_token_card orient labels active vertices hind]
  exact hcap _ (independent_token_clique orient labels active hcovers vertices hind)



def DirectedConflict (macroArc : M → M → Prop) (label : M → M → Bool)
    (internalArc : B → B → Prop) (active : M × B → Bool) (v w : M × B) : Prop :=
  pairedArc macroArc internalArc v w ∧ (w, active w) ∈ pairedCheck label v w




















end
end SensitivityActiveSocketGeometry


