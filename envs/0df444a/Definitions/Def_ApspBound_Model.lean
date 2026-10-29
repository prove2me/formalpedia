-- Prove2me | Definitions.Def_ApspBound_Model
-- name    : ApspBound_Model
-- status  : Definition
-- author  : @darkhipo
-- created : 2026-10-29T02:17:12.673001+00:00
-- url     : https://prove2.me/theorems/4f7eb2c6-26ac-44ac-a0de-b3d0ca59563a
-- title:
--   APSP aligned-cache exponent refinement: cost model and analytic certificates
-- statement:
--   This definition packages the exact rational parameters and real-valued cost model for the aligned-cache refinement of the All-Pairs Shortest Paths (APSP) exponent below $2.9929479187094$. It fixes the tuned constants—the box density $c$, the switching threshold $\theta$, the base exponent $b$, the ring size $R = 10^{12}$, the frozen-block count $S$, and the derived $\eta = b/R$, $u = S\eta$, $v = (R-S)\eta$, $e = b+u$—together with the binary entropy $\mathrm{H}(x) = -x\log x - (1-x)\log(1-x)$ and the entropic cost parameters $T$ (box/cache formation), $G$ (box gain), $q_1$ (residual query exponent), $q_2 = q_1 + 2\theta$. It encodes the six cost categories of the written reduction (boxes, residual queries, stored queries, cache encodings, ordinary box encodings, matrix formation) at both scalar stages $x\in\{0,u\}$ and cyclic stages $z\in\{0,v\}$, and the resulting 47 affine cost inequalities. Kernel-certified rational arithmetic (`decide +kernel`) verifies each of the 47 expressions exceeds its target threshold (the stage saving $\delta = 3 - 2.9929479187094$) by at least a uniform slack $2\times 10^{-14}$ throughout the compact rational boxes enclosing $(T,G,q_1)$. A proved atanh-series enclosure establishes tight rational bounds for $\log 2$ and the entropies $\mathrm{H}(1/c)$, $\mathrm{H}((1-\theta)/c)$, $\mathrm{H}(\theta)$, which pin $(T,G,q_1)$ inside those boxes at the true real-logarithm parameters. This is the analytic feasibility model whose capstone is the theorem `ApspBound.apsp_feasibility`.
-- source:
--   Joshua Wharton (QFEX), APSP aligned-cache exponent refinement (2026). Finite affine certificate adapted from shreshth-s/thin-matrix-results, commit 8a21eaae81599913dba562727e03a9b48c36a5b9. Packaged and independently verified by the BigO strike, 2026-10-28.

/-
Copyright (c) 2026 Joshua Wharton, QFEX.
Author: Joshua Wharton <joshua@qfex.com>
Packaged for prove2.me by the BigO strike (2026-10-28).
Adapted from the finite affine certificate in shreshth-s/thin-matrix-results,
commit 8a21eaae81599913dba562727e03a9b48c36a5b9.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-
Copyright (c) 2026 Joshua Wharton, QFEX.
Author: Joshua Wharton <joshua@qfex.com>

Exact parameters and real-valued cost formulas for the published APSP
numerical refinement. The parameters are rational; entropy uses Real.log.
-/

namespace ApspBound.Analytic

noncomputable def c : ℝ := 10665500244065729 / 1000000000000000
noncomputable def theta : ℝ := 6529782369872631 / 100000000000000000
noncomputable def b : ℝ := 46046352103722105 / 1000000000000000000
def R : ℕ := 1000000000000
def S : ℕ := 768979037380
noncomputable def delta : ℝ := 70520812906 / 10000000000000
noncomputable def uniformSlack : ℝ := 2 / 100000000000000
noncomputable def exponent : ℝ := 29929479187094 / 10000000000000
noncomputable def previousExponent : ℝ := 299294792 / 100000000
noncomputable def eta : ℝ := b / (R : ℝ)
noncomputable def u : ℝ := (S : ℝ) * eta
noncomputable def v : ℝ := ((R - S : ℕ) : ℝ) * eta
noncomputable def e : ℝ := b + u

noncomputable def entropy (x : ℝ) : ℝ :=
  -x * Real.log x - (1 - x) * Real.log (1 - x)

noncomputable def CK : ℝ := c * entropy (1 / c) / Real.log 4
noncomputable def T : ℝ := c - 1 + CK
noncomputable def G : ℝ :=
  (c * entropy (1 / c) - c * entropy ((1 - theta) / c) - theta * Real.log 4) /
    Real.log 2
noncomputable def q1 : ℝ := entropy theta / Real.log 2
noncomputable def q2 : ℝ := q1 + 2 * theta
noncomputable def E : ℝ := T + q1
noncomputable def Ebox : ℝ := T - G

/-- Savings below cubic time, in the six cost categories of the written reduction. -/
noncomputable def scalarSaving (x : ℝ) (i : Fin 6) : ℝ :=
  match i.val with
  | 0 => b - x + (b + x) * G - eta
  | 1 => b - (b + x) * q1 - eta
  | 2 => b - (b + x) * q2 - eta
  | 3 => 1 + b - x / 2 - (b + x) * E - eta
  | 4 => 1 + b - x / 2 - (b + x) * Ebox - eta
  | _ => 1 - 3 * x / 2 - eta

noncomputable def cyclicSaving (z : ℝ) (i : Fin 6) : ℝ :=
  match i.val with
  | 0 => b - u - z + e * G - eta
  | 1 => b - z - e * q1 - eta
  | 2 => b - e * q2 - eta
  | 3 => 1 + b - u / 2 - z - e * E - eta
  | 4 => 1 + b - u / 2 - z - e * Ebox - eta
  | _ => 1 - 3 * u / 2 - z - eta

noncomputable def scalarGeometry (x : ℝ) : ℝ := 1 + x / 2 - (b + x) * T
noncomputable def cyclicGeometry : ℝ := 1 + u / 2 - e * T

end ApspBound.Analytic

/-
Copyright (c) 2026 Joshua Wharton, QFEX.
Author: Joshua Wharton <joshua@qfex.com>

Adapted from the finite affine certificate in shreshth-s/thin-matrix-results,
commit 8a21eaae81599913dba562727e03a9b48c36a5b9, for the new exact witness.
The original algorithm and proof framework remain attributable to that work
and its cited predecessors; this file certifies the parameter refinement.
-/

/-!
# Limited exact arithmetic certificate for the aligned witness

This file proves exact witness identities and independently evaluates the 47
cost inequalities over compact rational boxes for T, G, q1. The relations
q2=q1+2*theta, Esource=T+q1, Ebox=T-G are encoded in the affine formulas.

ANALYTIC SCOPE: this file does not define real logarithms or entropy. It does
not prove that these boxes enclose the real expressions in the research note.
The boxes were outward rounded from the Python rational interval computation;
their relationship to real logarithms is proved separately in
`Certificate.lean` and is not an assumption hidden in this file.
No theorem here establishes the embedding/cache lemmas or an APSP algorithm.

Uses kernel reduction (decide +kernel) and proof-producing grind; no unproved placeholders,
native_decide, custom axiom, or external package.
-/
namespace ApspBound.Numerical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def c : Rat := 10665500244065729 / 1000000000000000
def theta : Rat := 6529782369872631 / 100000000000000000
def b : Rat := 46046352103722105 / 1000000000000000000
def delta : Rat := 70520812906 / 10000000000000
def uniformSlack : Rat := 2 / 100000000000000
def exponent : Rat := 29929479187094 / 10000000000000
def previousExponent : Rat := 299294792 / 100000000
def R : Nat := 1000000000000
def S : Nat := 768979037380
def eta : Rat := b / (R : Rat)
def u : Rat := (S : Rat) * eta
def v : Rat := ((R - S : Nat) : Rat) * eta
def e : Rat := b + u

theorem witnessIdentities :
    u + v = b ∧ (R : Rat) * eta = b ∧ (S : Rat) * eta = u ∧
    e = b + u ∧ 3 - delta = exponent ∧ exponent < previousExponent ∧
    0 < S ∧ S < R := by
  decide +kernel

-- The real-log/entropy interpretation of these compact boxes is NOT proved here.
def tLo : Rat := 12059361352073940511273 / 1000000000000000000000
def tHi : Rat := 12059361352073940511274 / 1000000000000000000000
def gLo : Rat := 86576374110896937279 / 1000000000000000000000
def gHi : Rat := 86576374110896937280 / 1000000000000000000000
def qLo : Rat := 348125802190376753494 / 1000000000000000000000
def qHi : Rat := 348125802190376753495 / 1000000000000000000000

theorem boxesOrdered : tLo ≤ tHi ∧ gLo ≤ gHi ∧ qLo ≤ qHi := by
  decide +kernel

structure Affine where
  constant : Rat
  tCoeff : Rat
  gCoeff : Rat
  qCoeff : Rat

def eval (a : Affine) (T G q1 : Rat) : Rat :=
  a.constant + a.tCoeff*T + a.gCoeff*G + a.qCoeff*q1

def signedLower (coefficient lo hi : Rat) : Rat :=
  if 0 ≤ coefficient then coefficient*lo else coefficient*hi

def lower (a : Affine) : Rat :=
  a.constant + signedLower a.tCoeff tLo tHi +
    signedLower a.gCoeff gLo gHi + signedLower a.qCoeff qLo qHi

theorem signedLower_le (coefficient lo hi x : Rat)
    (hlo : lo ≤ x) (hhi : x ≤ hi) :
    signedLower coefficient lo hi ≤ coefficient*x := by
  unfold signedLower
  split
  next h => exact Rat.mul_le_mul_of_nonneg_left hlo h
  next h =>
    have hn : 0 ≤ -coefficient := by grind
    have hm := Rat.mul_le_mul_of_nonneg_left hhi hn
    have hh := Rat.neg_le_neg hm
    simpa only [Rat.neg_mul, Rat.neg_neg] using hh

theorem lower_le_eval (a : Affine) (T G q1 : Rat)
    (hT : tLo ≤ T ∧ T ≤ tHi) (hG : gLo ≤ G ∧ G ≤ gHi)
    (hq : qLo ≤ q1 ∧ q1 ≤ qHi) : lower a ≤ eval a T G q1 := by
  have ht := signedLower_le a.tCoeff tLo tHi T hT.1 hT.2
  have hg := signedLower_le a.gCoeff gLo gHi G hG.1 hG.2
  have hq' := signedLower_le a.qCoeff qLo qHi q1 hq.1 hq.2
  unfold lower eval
  grind

structure Check where
  label : String
  target : Rat
  expression : Affine

def regimes : List Check := [
  ⟨"ordinary tail regime", 0, ⟨c-5, 0, 0, 0⟩⟩,
  ⟨"positive switching threshold", 0, ⟨theta, 0, 0, 0⟩⟩,
  ⟨"unweighted cache cutoff increasing", 0, ⟨1/2-theta, 0, 0, 0⟩⟩,
  ⟨"stored cutoff increasing", 0, ⟨4/5-theta, 0, 0, 0⟩⟩,
  ⟨"ordinary private-cap tail geometric", 0, ⟨1-4/(c-1), 0, 0, 0⟩⟩,
  ⟨"box private-cap tail geometric", 0, ⟨1-4*(1-theta)/(c-1+theta), 0, 0, 0⟩⟩,
  ⟨"positive box gain", 0, ⟨0, 0, 1, 0⟩⟩,
  ⟨"box gain below one", 0, ⟨1, 0, -1, 0⟩⟩,
  ⟨"positive residual query exponent", 0, ⟨0, 0, 0, 1⟩⟩,
  ⟨"positive stored query exponent", 0, ⟨2*theta, 0, 0, 1⟩⟩,
  ⟨"positive source encoder slope", 0, ⟨1/2, 1, 0, 1⟩⟩,
  ⟨"positive box encoder slope", 0, ⟨1/2, 1, -1, 0⟩⟩,
  ⟨"positive original geometry slope", 0, ⟨-1/2, 1, 0, 0⟩⟩,
  ⟨"positive frozen-factor count", 0, ⟨(S : Rat), 0, 0, 0⟩⟩,
  ⟨"at least two cyclic factors", 1, ⟨((R-S : Nat) : Rat), 0, 0, 0⟩⟩,
  ⟨"positive final ring exponent", 0, ⟨v, 0, 0, 0⟩⟩,
  ⟨"positive candidate exponent", 0, ⟨eta, 0, 0, 0⟩⟩,
  ⟨"middle blocks fit", 0, ⟨1-b, 0, 0, 0⟩⟩,
  ⟨"incidence bookkeeping after enumeration", delta, ⟨b-eta, 0, 0, 0⟩⟩
]

/-- Phase I costs after substituting q2 and both E's; ep=b+x. -/
def scalarPhase (x : Rat) (endpoint : String) : List Check :=
  let ep := b+x
  [⟨"phase I "++endpoint++": boxes", delta, ⟨b-x-eta, 0, ep, 0⟩⟩,
   ⟨"phase I "++endpoint++": residual queries", delta, ⟨b-eta, 0, 0, -ep⟩⟩,
   ⟨"phase I "++endpoint++": stored queries", delta, ⟨b-eta-ep*(2*theta), 0, 0, -ep⟩⟩,
   ⟨"phase I "++endpoint++": cache encodings", delta, ⟨1+b-x/2-eta, -ep, 0, -ep⟩⟩,
   ⟨"phase I "++endpoint++": ordinary box encodings", delta, ⟨1+b-x/2-eta, -ep, ep, 0⟩⟩,
   ⟨"phase I "++endpoint++": matrix formation", delta, ⟨1-3*x/2-eta, 0, 0, 0⟩⟩,
   ⟨"phase I "++endpoint++": original tile geometry", 0, ⟨1+x/2, -ep, 0, 0⟩⟩]

/-- Cyclic preprocessing/residual costs pay z; stored lookup costs do not. -/
def cyclicPhase (z : Rat) (endpoint : String) : List Check :=
  [⟨"phase II "++endpoint++": boxes", delta, ⟨b-u-z-eta, 0, e, 0⟩⟩,
   ⟨"phase II "++endpoint++": residual queries", delta, ⟨b-z-eta, 0, 0, -e⟩⟩,
   ⟨"phase II "++endpoint++": stored queries", delta, ⟨b-eta-e*(2*theta), 0, 0, -e⟩⟩,
   ⟨"phase II "++endpoint++": cache encodings", delta, ⟨1+b-u/2-z-eta, -e, 0, -e⟩⟩,
   ⟨"phase II "++endpoint++": ordinary box encodings", delta, ⟨1+b-u/2-z-eta, -e, e, 0⟩⟩,
   ⟨"phase II "++endpoint++": matrix formation", delta, ⟨1-3*u/2-z-eta, 0, 0, 0⟩⟩,
   ⟨"phase II "++endpoint++": original tile geometry", 0, ⟨1+u/2, -e, 0, 0⟩⟩]

/-- Unexpanded phase-I expressions, in the same order as the Python verifier.
This second representation makes the substitutions and affine expansion auditable.
-/
def scalarCosts (x T G q1 : Rat) : List Rat :=
  let ep := b+x
  let q2 := q1+2*theta
  let Esource := T+q1
  let Ebox := T-G
  [b-x+ep*G-eta,
   b-ep*q1-eta,
   b-ep*q2-eta,
   1+b-x/2-ep*Esource-eta,
   1+b-x/2-ep*Ebox-eta,
   1-3*x/2-eta,
   1+x/2-ep*T]

/-- Unexpanded cyclic-phase expressions. The cyclic exponent z is charged
in both encoders and in residual queries; it is absent from stored lookups.
-/
def cyclicCosts (z T G q1 : Rat) : List Rat :=
  let q2 := q1+2*theta
  let Esource := T+q1
  let Ebox := T-G
  [b-u-z+e*G-eta,
   b-z-e*q1-eta,
   b-e*q2-eta,
   1+b-u/2-z-e*Esource-eta,
   1+b-u/2-z-e*Ebox-eta,
   1-3*u/2-z-eta,
   1+u/2-e*T]

theorem scalarPhaseEval (x T G q1 : Rat) (endpoint : String) :
    (scalarPhase x endpoint).map (fun check => eval check.expression T G q1) =
      scalarCosts x T G q1 := by
  simp only [scalarPhase, scalarCosts, eval, List.map_cons, List.map_nil, List.cons.injEq]
  grind

theorem cyclicPhaseEval (z T G q1 : Rat) (endpoint : String) :
    (cyclicPhase z endpoint).map (fun check => eval check.expression T G q1) =
      cyclicCosts z T G q1 := by
  simp only [cyclicPhase, cyclicCosts, eval, List.map_cons, List.map_nil, List.cons.injEq]
  grind

def checks : List Check :=
  regimes ++ scalarPhase 0 "initial" ++ scalarPhase u "freeze" ++
    cyclicPhase 0 "start" ++ cyclicPhase v "final"

theorem checkCount : checks.length = 47 := by decide +kernel

/-- Kernel recomputation from witness constants and three parameter boxes.
No Python-generated per-cost lower endpoints are imported. -/
theorem numericalMargins :
    checks.all (fun check => decide (check.target < lower check.expression)) = true := by
  decide +kernel

/-- A common strictly positive reserve in every one of the 47 inequalities. -/
theorem numericalMarginsWithSlack :
    checks.all (fun check => decide (check.target + uniformSlack < lower check.expression)) = true := by
  decide +kernel

theorem uniformSlackPositive : 0 < uniformSlack := by decide +kernel

/-- Conditional interval-to-cost theorem. Only three rational enclosure pairs
are assumed. This theorem does not assert a real-log enclosure. -/
theorem allCostsOfEnclosures (T G q1 : Rat)
    (hT : tLo ≤ T ∧ T ≤ tHi) (hG : gLo ≤ G ∧ G ≤ gHi)
    (hq : qLo ≤ q1 ∧ q1 ≤ qHi) :
    ∀ check ∈ checks, check.target < eval check.expression T G q1 := by
  intro check hmember
  have hb : decide (check.target < lower check.expression) = true :=
    (List.all_eq_true.mp numericalMargins) check hmember
  have hm : check.target < lower check.expression := of_decide_eq_true hb
  have hl := lower_le_eval check.expression T G q1 hT hG hq
  grind

end ApspBound.Numerical

/-
Copyright (c) 2026 Joshua Wharton, QFEX.
Author: Joshua Wharton <joshua@qfex.com>

Analytic numerical certificate for the conditional APSP exponent refinement.
The range-reduction identity and proof arrangement follow the open upstream
ThinMatrix.RealCertificate module from shreshth-s/thin-matrix-results, with new rational
parameters and 40-term enclosures. The analytical remainder bound itself is
proved in Mathlib.Analysis.SpecialFunctions.Log.Deriv.

Each numerical bound is proved inside Lean from the real logarithm. The Python
generator only selects rational endpoints; it is not in the proof's trust base.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

namespace ApspBound.Analytic
open scoped BigOperators
noncomputable section

/-- The applications below use 40 terms of this proved positive atanh-series enclosure.
The omitted nonnegative tail is bounded by a rational geometric majorant. -/
theorem atanhLogBounds (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1))
        ≤ Real.log ((1 + z) / (1 - z)) ∧
    Real.log ((1 + z) / (1 - z)) ≤
      2 * ((∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
        z ^ (2 * n + 1) / (1 - z ^ 2)) := by
  have hlo := Real.sum_range_le_log_div hz0 hz1 n
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 n
  constructor <;> linarith

theorem logTwoFine :
    (693147180559945309417232121458 / 10^30 : ℝ) < Real.log (2 : ℝ) ∧
    Real.log (2 : ℝ) < (693147180559945309417232121459 / 10^30 : ℝ) := by
  have h := atanhLogBounds (1 / 3 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logC16 :
    (405574466206381144535140895700 / 10^30 : ℝ) < Real.log (16000000000000000 / 10665500244065729 : ℝ) ∧
    Real.log (16000000000000000 / 10665500244065729 : ℝ) < (405574466206381144535140895701 / 10^30 : ℝ) := by
  have h := atanhLogBounds (5334499755934271 / 26665500244065729 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logCComp2 :
    (594695794157380769260934210624 / 10^30 : ℝ) < Real.log (19331000488131458 / 10665500244065729 : ℝ) ∧
    Real.log (19331000488131458 / 10665500244065729 : ℝ) < (594695794157380769260934210625 / 10^30 : ℝ) := by
  have h := atanhLogBounds (8665500244065729 / 29996500732197187 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logD16 :
    (338047137752077978432345089172 / 10^30 : ℝ) < Real.log (373880870520509476 / 266637506101643225 : ℝ) ∧
    Real.log (373880870520509476 / 266637506101643225 : ℝ) < (338047137752077978432345089173 / 10^30 : ℝ) := by
  have h := atanhLogBounds (107243364418866251 / 640518376622152701 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logDComp2 :
    (601428838713867539932064942021 / 10^30 : ℝ) < Real.log (973079806776445531 / 533275012203286450 : ℝ) ∧
    Real.log (973079806776445531 / 533275012203286450 : ℝ) < (601428838713867539932064942022 / 10^30 : ℝ) := by
  have h := atanhLogBounds (439804794573159081 / 1506354818979731981 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logTheta16 :
    (43792151246919381980159120037 / 10^30 : ℝ) < Real.log (6529782369872631 / 6250000000000000 : ℝ) ∧
    Real.log (6529782369872631 / 6250000000000000 : ℝ) < (43792151246919381980159120038 / 10^30 : ℝ) := by
  have h := atanhLogBounds (279782369872631 / 12779782369872631 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem logThetaComp2 :
    (625619852105642143314436314929 / 10^30 : ℝ) < Real.log (93470217630127369 / 50000000000000000 : ℝ) ∧
    Real.log (93470217630127369 / 50000000000000000 : ℝ) < (625619852105642143314436314930 / 10^30 : ℝ) := by
  have h := atanhLogBounds (43470217630127369 / 143470217630127369 : ℝ) (by norm_num) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- The public logarithm enclosure used in the rational cost ledger. -/
theorem logTwo :
    (693147180559945309417232 / 10^24 : ℝ) < Real.log 2 ∧
    Real.log 2 < (693147180559945309417233 / 10^24 : ℝ) := by
  have h := logTwoFine
  norm_num at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- Range-reduction identity used to place both entropy logarithms in [1,2]
for the chosen parameters. -/
theorem entropyScaled (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    entropy p = (1+3*p)*Real.log 2 - p*Real.log (16*p)
      - (1-p)*Real.log (2*(1-p)) := by
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num
  have hmul := Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (ne_of_gt hp)
  have hcomp := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (ne_of_gt (sub_pos.mpr hp1))
  have ha : Real.log p = Real.log (16*p) - 4*Real.log 2 := by
    rw [h16] at hmul
    linarith
  have hb : Real.log (1-p) = Real.log (2*(1-p)) - Real.log 2 := by
    linarith
  rw [entropy, ha, hb]
  ring

theorem entropyC :
    (311152414738582918394308 / 10^24 : ℝ) < entropy (1/c) ∧
    entropy (1/c) < (311152414738582918394309 / 10^24 : ℝ) := by
  have hs := entropyScaled (1/c) (by norm_num [c, theta]) (by norm_num [c, theta])
  have h0 := logTwoFine
  have h1 := logC16
  have h2 := logCComp2
  norm_num [c, theta] at hs ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

theorem entropyD :
    (297038479999443775766554 / 10^24 : ℝ) < entropy ((1-theta)/c) ∧
    entropy ((1-theta)/c) < (297038479999443775766555 / 10^24 : ℝ) := by
  have hs := entropyScaled ((1-theta)/c) (by norm_num [c, theta]) (by norm_num [c, theta])
  have h0 := logTwoFine
  have h1 := logD16
  have h2 := logDComp2
  norm_num [c, theta] at hs ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

theorem entropyTheta :
    (241302418268428879845954 / 10^24 : ℝ) < entropy (theta) ∧
    entropy (theta) < (241302418268428879845955 / 10^24 : ℝ) := by
  have hs := entropyScaled (theta) (by norm_num [c, theta]) (by norm_num [c, theta])
  have h0 := logTwoFine
  have h1 := logTheta16
  have h2 := logThetaComp2
  norm_num [c, theta] at hs ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

/-- The four real-logarithm enclosures, with no enclosure hypotheses. -/
theorem analyticEnclosures :
    ((693147180559945309417232 / 10^24 : ℝ) < Real.log 2 ∧
      Real.log 2 < (693147180559945309417233 / 10^24 : ℝ)) ∧
    ((311152414738582918394308 / 10^24 : ℝ) < entropy (1/c) ∧
      entropy (1/c) < (311152414738582918394309 / 10^24 : ℝ)) ∧
    ((297038479999443775766554 / 10^24 : ℝ) < entropy ((1-theta)/c) ∧
      entropy ((1-theta)/c) < (297038479999443775766555 / 10^24 : ℝ)) ∧
    ((241302418268428879845954 / 10^24 : ℝ) < entropy theta ∧
      entropy theta < (241302418268428879845955 / 10^24 : ℝ)) :=
  ⟨logTwo, entropyC, entropyD, entropyTheta⟩


end
end ApspBound.Analytic

namespace ApspBound.Analytic
noncomputable def evalReal (a : Numerical.Affine) : ℝ :=
  (a.constant : ℝ) + (a.tCoeff : ℝ) * T + (a.gCoeff : ℝ) * G + (a.qCoeff : ℝ) * q1
end ApspBound.Analytic


