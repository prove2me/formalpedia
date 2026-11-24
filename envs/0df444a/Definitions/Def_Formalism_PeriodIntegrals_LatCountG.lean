-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LatCountG
-- name    : Formalism_PeriodIntegrals_LatCountG
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:40:59.498432+00:00
-- url     : https://prove2.me/theorems/3907b4da-1de0-4714-a00b-5759006a1d34
-- title:
--   Lat Count G
-- statement:
--   Definitions and structural lemmas for Lat Count G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LatCountG.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrgCountableField
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_PeriodIntegrals_SymDist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LatCountG
open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix
section Size
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
section Lat
variable (I : Formalism.MainNotions.S.AutInst)
def LatCount : Prop :=
  ∀ x y : I.GA, 0 < tau1 I x → 0 < tau1 I y →
    ∀ r : InfinitePlace I.F → ℝ, (∀ v, 0 ≤ r v) → ∀ S : Finset I.GFset,
      (∀ γ ∈ S, (x⁻¹ * (γ : I.GA) * y).2 ∈ I.Kset ∧ ∀ v, PI.symD (I.ε v) ((x⁻¹ * (γ : I.GA) * y).1 v) ≤ r v) →
      (S.card : ℝ) ≤ (3 * Real.sqrt (I.n : ℝ) / (tau1 I x * tau1 I y)) ^ (2 * I.n ^ 2 * I.f) *
        Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v)
def Om (r : InfinitePlace I.F → ℝ) (K' : Set I.Gf) : Set I.GA :=
  {ω | (∀ v, PI.symD (I.ε v) (ω.1 v) ≤ r v) ∧ ω.2 ∈ K'}
def COm (r : InfinitePlace I.F → ℝ) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ)) ^ (2 * I.n ^ 2 * I.f) * Real.exp (4 * (I.n : ℝ) ^ 2 * ∑ v, r v)
def MultBound : Prop :=
  ∀ r : InfinitePlace I.F → ℝ, (∀ v, 0 ≤ r v) → ∀ K' : Subgroup I.Gf, (K' : Set I.Gf) ⊆ I.Kset →
    ∀ x : I.GA, 0 < tau1 I x →
      Formalism.L2.SG.FoldBound.mult (Formalism.MainNotions.LeviCoordinates.rr_GF I) (Om I r (K' : Set I.Gf)) x ≤
        ENNReal.ofReal (COm I r / tau1 I x ^ (4 * I.n ^ 2 * I.f))
end Lat
def LatCountAll : Prop := ∀ I : Formalism.MainNotions.S.AutInst, LatCount I
def MultFromLat : Prop := PI.SymDist → ∀ I : Formalism.MainNotions.S.AutInst, LatCount I → MultBound I
end PI.LatCountG
end


