-- Prove2me | Definitions.Def_KServer_race_fix2
-- name    : KServer_race_fix2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T20:46:39.498497+00:00
-- url     : https://prove2.me/theorems/9f13d071-a31b-4039-b8e6-c165c444738c
-- title:
--   Race assembly with split head lifts and exact chunk count
-- statement:
--   The race assembly of four chunk systems on a target space, with split lifts of the head phase for the two survivor branches, additionally recording that the produced chunk system has exactly the race chunk count (head count plus coins plus surviving side count plus closing count). The exact count, combined with the size ceiling, bounds the produced system's pathwise totals and the range terms in downstream variance estimates.
-- source:
--   Bansal-Cohen-Ravi style randomized k-server lower bound

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow
import Definitions.Def_KServer_park_shadow
import Definitions.Def_KServer_shadow2
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_hist
import Definitions.Def_KServer_absorb
import Definitions.Def_KServer_race_opt
import Definitions.Def_KServer_race_cost1
import Definitions.Def_KServer_race_cost2
import Definitions.Def_KServer_race_assemble
import Definitions.Def_KServer_race_fix

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section RaceSystem3

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

open Classical in
/-- **The race, with split head lifts and exact chunk count**: identical
to `race_system2` but additionally recording that the produced system has
exactly `mrace A BL BR CC κ` chunks, which is needed downstream to bound
range terms in variance estimates and pathwise totals. -/
theorem race_system3 (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (πA πL πR πTL πTR : Y → X) (ιAL ιAR ιL ιR ιTL ιTR : X → Y)
    (hπA : ∀ y z : Y, dist (πA y) (πA z) ≤ dist y z)
    (hπL : ∀ y z : Y, dist (πL y) (πL z) ≤ dist y z)
    (hπR : ∀ y z : Y, dist (πR y) (πR z) ≤ dist y z)
    (hπTL : ∀ y z : Y, dist (πTL y) (πTL z) ≤ dist y z)
    (hπTR : ∀ y z : Y, dist (πTR y) (πTR z) ≤ dist y z)
    (hGA : ∀ S : Set X, ∀ y ∈ GmA S, πA y ∈ S)
    (hGL : ∀ S : Set X, ∀ y ∈ GmL S, πL y ∈ S)
    (hGR : ∀ S : Set X, ∀ y ∈ GmR S, πR y ∈ S)
    (hGTL : ∀ S : Set X, ∀ y ∈ GmTL S, πTL y ∈ S)
    (hGTR : ∀ S : Set X, ∀ y ∈ GmTR S, πTR y ∈ S)
    (hGneA : ∀ S : Set X, S.Nonempty → (GmA S).Nonempty)
    (hGneL : ∀ S : Set X, S.Nonempty → (GmL S).Nonempty)
    (hGneR : ∀ S : Set X, S.Nonempty → (GmR S).Nonempty)
    (hGneTL : ∀ S : Set X, S.Nonempty → (GmTL S).Nonempty)
    (hGneTR : ∀ S : Set X, S.Nonempty → (GmTR S).Nonempty)
    (hιAL : ∀ x y : X, dist (ιAL x) (ιAL y) ≤ dist x y)
    (hιAR : ∀ x y : X, dist (ιAR x) (ιAR y) ≤ dist x y)
    (hιL : ∀ x y : X, dist (ιL x) (ιL y) ≤ dist x y)
    (hιR : ∀ x y : X, dist (ιR x) (ιR y) ≤ dist x y)
    (hιTL : ∀ x y : X, dist (ιTL x) (ιTL y) ≤ dist x y)
    (hιTR : ∀ x y : X, dist (ιTR x) (ιTR y) ≤ dist x y)
    (hGALsub : ∀ S : Set X, ιAL '' S ⊆ GmA S)
    (hGARsub : ∀ S : Set X, ιAR '' S ⊆ GmA S)
    (hGLsub : ∀ S : Set X, ιL '' S ⊆ GmL S)
    (hGRsub : ∀ S : Set X, ιR '' S ⊆ GmR S)
    (hGTLsub : ∀ S : Set X, ιTL '' S ⊆ GmTL S)
    (hGTRsub : ∀ S : Set X, ιTR '' S ⊆ GmTR S)
    (hJ0 : ιAL s = ιAR s)
    (hJ1L : ιAL t = ιL s) (hJ1R : ιAR t = ιR s)
    (hJ2L : ιL t = ιTL s) (hJ2R : ιR t = ιTR s)
    (hJ3L : ιTL t = stopPt) (hJ3R : ιTR t = stopPt)
    (hTLt : GmTL {t} = {stopPt}) (hTRt : GmTR {t} = {stopPt})
    (hchA : ∀ (ωa : A.Ω) (i : Fin A.m), A.chunk ωa i ≠ [])
    (hchL : ∀ (ωl : BL.Ω) (i : Fin BL.m), BL.chunk ωl i ≠ [])
    (hchR : ∀ (ωr : BR.Ω) (i : Fin BR.m), BR.chunk ωr i ≠ [])
    (hchC : ∀ (ωc : CC.Ω) (i : Fin CC.m), CC.chunk ωc i ≠ [])
    {sep J p' : ℝ}
    (hpe0 : 0 ≤ pe) (hpe : pe ≤ p') (hsep0 : 0 < sep)
    (hdiam : ∀ x₁ x₂ : X, dist x₁ x₂ ≤ J) (harith : J + pe ≤ sep)
    (hsepLR : ∀ SL SR : Set X, ∀ y ∈ GmL SL,
      ∀ z ∈ GmR SR, sep ≤ dist y z)
    (hdicho : ∀ z : Y,
      (z ∈ GmA ({t} : Set X) ∨ (∃ S, z ∈ GmL S) ∨ (∃ S, z ∈ GmR S)) →
      (∀ S' : Set X, ∀ p ∈ GmR S', sep ≤ dist z p)
      ∨ (∀ S' : Set X, ∀ p ∈ GmL S', sep ≤ dist z p))
    (h0A : ∀ a b : A.Ω, A.hist 0 a = A.hist 0 b)
    (h0L : ∀ a b : BL.Ω, BL.hist 0 a = BL.hist 0 b)
    (h0R : ∀ a b : BR.Ω, BR.hist 0 a = BR.hist 0 b)
    (hcB : 0 ≤ cB)
    (hd3 : 3 * dist s t ≤ dist (ιAL s) stopPt)
    {Trace Vrace : ℝ} {mLo' : ℕ} (hmLo : mLo' ≤ mrace A BL BR CC κ)
    (htot : Trace ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ∑ i : Fin (mrace A BL BR CC κ), rsize A BL BR CC κ ε ω (i : ℕ))
    (hvar : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ((∑ i : Fin (mrace A BL BR CC κ), rsize A BL BR CC κ ε ω (i : ℕ))
          - ∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω'
            * ∑ i : Fin (mrace A BL BR CC κ),
              rsize A BL BR CC κ ε ω' (i : ℕ)) ^ 2 ≤ Vrace) :
    ∃ C' : ChunkSystemB Y (ιAL s) stopPt 0 cB Trace p' mLo',
      C'.m = mrace A BL BR CC κ ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ Vrace) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) := by
  refine ⟨{
    Ω := RΩ A BL BR CC κ
    instFin := inferInstance
    instDec := inferInstance
    P := RP A BL BR CC κ ε
    m := mrace A BL BR CC κ
    hist := fun r ω => rhist2 A BL BR CC κ ω r
    chunk := fun ω i =>
      rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (i : ℕ)
    size := fun ω i => rsize A BL BR CC κ ε ω (i : ℕ)
    hP := RP_pos A BL BR CC κ ε hε
    hPsum := RP_sum A BL BR CC κ ε hε
    hm := hmLo
    hm0 := by
      have := A.hm0
      unfold mrace
      omega
    href := fun i j hij ω ω' h =>
      rhist2_refine A BL BR CC κ hκL hκR hij ω ω' h
    hadapt := fun i ω ω' h =>
      rchunk_adapt A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ hκL hκR
        ω ω' h
    hsmeas := fun i ω ω' h =>
      rsize_smeas A BL BR CC κ ε hκL hκR h0L h0R ω ω' h
    hne := fun ω i =>
      race_ne A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ
        hGneA hGneL hGneR hGneTL hGneTR ω (i : ℕ)
    hlast := fun ω =>
      race_last A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ hTLt hTRt ω
    hopt := fun ω => le_trans
      (race_opt2 A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ hκL hκR
        ιAL ιAR ιL ιR ιTL ιTR hιAL hιAR hιL hιR hιTL hιTR
        hGALsub hGARsub hGLsub hGRsub hGTLsub hGTRsub
        hJ0 hJ1L hJ1R hJ2L hJ2R hJ3L hJ3R ω) hd3
    hsize := fun ω i =>
      rsize_bounds A BL BR CC κ ε hε hcB ω (i : ℕ)
    hcost := fun i ω₀ E bail =>
      race_hcost A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ε hε hκL hκR
        πA πL πR πTL πTR hπA hπL hπR hπTL hπTR hGA hGL hGR hGTL hGTR
        hGneA hGneL hGneR hGneTL hGneTR hchA hchL hchR hchC
        hpe0 hpe hsep0 hdiam harith hsepLR hdicho h0L h0R ω₀ E bail
    htotal := htot }, rfl, ?_, ?_, ?_⟩
  · intro ω₁ ω₂
    show rhist2 A BL BR CC κ ω₁ 0 = rhist2 A BL BR CC κ ω₂ 0
    rw [rhist2_le_A A BL BR CC κ ω₁ (by omega),
      rhist2_le_A A BL BR CC κ ω₂ (by omega), h0A ω₁.1 ω₂.1]
  · exact hvar
  · intro ω i
    exact rchunk_ne_nil A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ
      hκL hκR hchA hchL hchR hchC ω i.isLt

end RaceSystem3

end Race

end KServer


