-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LatSizeCont
-- name    : Formalism_PeriodIntegrals_LatSizeCont
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:59.496374+00:00
-- url     : https://prove2.me/theorems/a7f49b59-7fe7-4f40-85c4-2d3b43a4bf14
-- title:
--   Lat Size Cont
-- statement:
--   Definitions and structural lemmas for Lat Size Cont, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LatSizeCont.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LatSizeCont
open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix
namespace Size
variable (I : Formalism.MainNotions.S.AutInst)
def latSet (x : I.GA) : Set (Fin I.n → I.E) :=
  {u | (I.fmat x.2⁻¹) *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) ∈ I.Lf}
def coordV (x : I.GA) (v : InfinitePlace I.F) (u : Fin I.n → I.E) : Fin I.n → ℂ :=
  (Formalism.MainNotions.S.uMat (x.1 v)⁻¹ * (I.P v)⁻¹) *ᵥ (fun i => I.φ v (u i))
def gramV (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) : Matrix (Fin j) (Fin j) ℂ :=
  fun a c => ∑ i, star (coordV I x v (b a) i) * coordV I x v (b c) i
structure Sub (x : I.GA) where
  j : ℕ
  j_pos : 1 ≤ j
  b : Fin j → Fin I.n → I.E
  b_ind : LinearIndependent I.E b
  B : Submodule (𝓞 I.E) (Fin I.n → I.E)
  B_lat : (B : Set (Fin I.n → I.E)) ⊆ latSet I x
  b_mem : ∀ a, b a ∈ B
  B_span : (B : Set (Fin I.n → I.E)) ⊆ Submodule.span I.E (Set.range b)
def ht {x : I.GA} (s : Sub I x) : ℝ :=
  (∏ v, (gramV I x v s.b).det.re) /
    (Nat.card (s.B ⧸ (Submodule.span (𝓞 I.E) (Set.range s.b)).comap s.B.subtype) : ℝ)
def size {x : I.GA} (s : Sub I x) : ℝ := ht I s ^ ((1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ)))
def tau1 (x : I.GA) : ℝ := min (1 / 2) (⨅ s : Sub I x, size I s)
end Size
def LatSizeCont : Prop :=
  ∀ I : Formalism.MainNotions.S.AutInst, 1 ≤ I.n →
    Continuous (Size.tau1 I) ∧ ∀ x : I.GA, 0 < Size.tau1 I x ∧ Size.tau1 I x ≤ 1 / 2
end PI.LatSizeCont


