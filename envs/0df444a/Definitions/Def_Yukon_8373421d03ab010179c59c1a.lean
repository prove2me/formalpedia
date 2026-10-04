-- Prove2me | Definitions.Def_Yukon_8373421d03ab010179c59c1a
-- name    : Yukon_8373421d03ab010179c59c1a
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T17:48:54.093746+00:00
-- url     : https://prove2.me/theorems/1eea9b01-931f-4aa6-8a0d-38d21d4daf45
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RetainedWholeSpace6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RetainedWholeSpace6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RetainedWholeSpace6814.lean
--
--   yukon-proof-operation:certificate-split-af00f06375963834b1c2bcd5765d0e94fec010e6961e1e0dfe900a12ac4140ac
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNTRjZDU0YTQxMGIyOGVhMDkzNzA3ODlhOTE1M2VhMGM5MWMxNmVlODM0NTMzYTE2NDdmMzc0MmZjNGIzODUxMyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LWFmMDBmMDYzNzU5NjM4MzRiMWMyYmNkNTc2NWQwZTk0ZmVjMDEwZTY5NjFlMWUwZGZlOTAwYTEyYWM0MTQwYWMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl84MzczNDIxZDAzYWIwMTAxNzljNTljMWEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_fdec088c29e5451064f27f59















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-!
Fully proved extraction from the existing source alternative.
This file uses the compiled 68.13 interface (181265 agreements, 80879
errors). It does not claim that the numerical 68.14 retune is compiled.
No desired new counting inequality is assumed.
-/

namespace ProximityPrize.SubmissionLower.RetainedWholeSpace6814
open scoped Classical
open MvPolynomial RCN095 RCN130 RCN135 RCN146 RCN156 RCN174 RCN222
  RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open MovingFiberRegularData6811 MovingFiberInterpolation6811
  MovingFiberTotalAvoidance6811 MovingFiberProfile6811
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance  _root_.ProximityPrize.SubmissionLower.RetainedWholeSpace6814.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.RetainedWholeSpace6814.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {nodes : I ↪ K} {u0 u1 : I → K}

theorem universal_retention_of_large_packet
    (S : Data nodes u0 u1) (cfg : Params) (hc : cfg.WellFormed)
    (hI : Fintype.card I = 262144)
    (hL : cfg.L < wt residualTotalWeights S.F)
    (hGates : S.PairGates (cfg.B+cfg.s*(S.r-1))
      (cfg.U+cfg.s*(S.y-1)) (cfg.L+cfg.s*(S.t-1)))
    (hlarge : helperCap S cfg < S.seeds.card) :
    ∀ P : SecondJetSupport.Poly (K := K),
      Interpolant cfg.m cfg.B cfg.s cfg.U cfg.L cfg.k cfg.n0 nodes u0 u1 P →
      cfg.n0 ≤ (SecondJetCoefficients.asS P).natDegree ∧
      ∀ d ≤ cfg.k, S.F ∣ SecondJetClearedHelper.helper P S.F (cfg.s-d) d := by
  classical
  intro P hP
  rcases hc with ⟨hsB,hBU,hUL,hks,hsm,hkn,hBn,hschar⟩
  have hf : ∀ d ≤ cfg.s, (d.factorial : K) ≠ 0 := by
    intro d hd
    exact SecondJetOwnShape.factorial_ne d (hd.trans_lt hschar)
  have alt := helper_or_divisibility P S.F cfg.m cfg.B cfg.s cfg.U cfg.L
    cfg.k cfg.n0 S.r S.y S.t nodes u0 u1 hP S.irreducible hL hsB
    (by omega) (by omega) hks hsm
    (by have := S.rpos; omega) (by have := S.ry; have := S.rpos; omega)
    (by have := S.yt; have := S.ry; have := S.rpos; omega) S.weights hf
  rcases alt with ⟨Q,hrel,hw,hzero⟩ | hret
  · have hb : S.seeds.card ≤ helperCap S cfg := by
      apply S.proper_count_left hI Q
        (cfg.B+cfg.s*(S.r-1)) (cfg.U+cfg.s*(S.y-1)) (cfg.L+cfg.s*(S.t-1)) hrel
        (SecondJetPairBounds.degree_caps_of_weights Q _ _ _ hw) hGates
      intro gamma hgamma
      apply hzero (S.selected gamma) (S.degree gamma hgamma) gamma
        (Finset.univ.filter (fun i =>
          (S.selected gamma).eval (nodes i) = u0 i+gamma*u1 i))
        (S.agreement gamma hgamma) _ (S.solution gamma hgamma)
      intro i hi
      simpa only [mul_comm] using (Finset.mem_filter.mp hi).2
    exact False.elim ((Nat.not_lt_of_ge hb) hlarge)
  · exact hret










/-- Cross-multiplied curvature reduction for a parameter pencil. All symbols
are scalars here; in the application da,db are the code/contact derivatives
of a,b and ar,br are their slope partials. -/
theorem parameter_pencil_cross_identity
    {E : Type} [CommRing E] (a b ar br da db p q : E) :
    (a*br-b*ar)*(-da*q-db*p)-(b*da-a*db)*(ar*q+br*p) =
      (ar*db-br*da)*(a*q+b*p) := by
  ring













/-- Plane trapezoid cost in the nonnegative coordinates u=A-B, v=B.
This is the proper intersection of a tail factor with its flow derivative.
It is not a bound for arbitrary mixed-parameter factors. -/
def descendedPlaneCost (u v : ℕ) : ℕ :=
  2*u*v+v*v+6*u+24*v















/-- Looser rectangle count: it avoids needing a new mixed-volume endpoint. -/
def descendedRectCost (a b : ℕ) : ℕ := 2*a*b+6*a+24*b










end
end ProximityPrize.SubmissionLower.RetainedWholeSpace6814


