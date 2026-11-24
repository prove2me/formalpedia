-- Prove2me | Definitions.Def_Curvature_AdaptivePredictor
-- name    : Curvature_AdaptivePredictor
-- status  : Definition
-- author  : @ssakaue
-- created : 2026-11-24T07:17:05.659977+00:00
-- url     : https://prove2.me/theorems/6d9805ab-025a-4459-8562-d3446045de10
-- title:
--   Algorithm 5: mixing base learners with rescaled inputs
-- statement:
--   This file defines Algorithm 5 of the paper, which mixes the predictions of base learners with different fixed parameters, and the domain data from which its base learners are built. A base learner for a domain $\mathcal K$ is a fixed-parameter learner with a cost $c_{\mathcal B}\ge0$. For a bound $G>0$, a parameter $\varepsilon\in(0,1]$ and inputs $g_1,g_2,\ldots$, its prediction $w_t\in\mathcal K$ depends only on $g_1,\ldots,g_{t-1}$, and $2\sum_{t=1}^Tr_t-\varepsilon\sum_{t=1}^T|r_t|\le Gc_{\mathcal B}/\varepsilon$ holds with $r_t\coloneqq\langle g_t,w_t-u\rangle$ for every $u\in\mathcal K$, every horizon $T$ and every input sequence with $\lVert g_t\rVert_2\le G$.
--
--   For a nonempty compact convex domain $\mathcal K$, the formalization allows two kinds of **domain initialization**. The first is an admissible description $\mathcal D$ of $\mathcal K$ with $C_{\mathcal D}(\mathcal K)\le2048\,\omega_{\psi_1}(\mathcal K)$; it yields Algorithm 4 with the dyadic initialization as a base learner with cost $192\,C_{\mathcal D}(\mathcal K)$. The second is a representation $\mathcal K=w_\circ+A\{v:\lVert v\rVert_p\le1\}$ with $A^\top A=\operatorname{diag}(a_1^2,\ldots,a_N^2)$, $a\in(0,\infty)^N$ and $p\ge2$, together with a choice of fixed initial diagonal; it yields Algorithm 4 with the fixed initialization as a base learner with cost $164\,\omega_{\psi_1}(\mathcal K)$.
--
--   Algorithm 5 receives a bound $G>0$ on the input norms and a bound $W>0$ on $\omega_{\psi_1}(\mathcal K)$. It runs base learner $i=0,1,2,\ldots$ with the parameter $\varepsilon_i\coloneqq2^{-i}/8$ and the bound $2G$ from round $2^i$ on, so the base learners $i\le\lfloor\log_2t\rfloor$ are active in round $t$.
--
--   To combine their predictions in round $t$, Algorithm 5 uses the vector $L$ of cumulative corrected losses through round $t-1$, with a final zero representing the base learners that have yet to start. The paper computes the exact weights $p_t$ by recursively applying exponential weights with learning rates $\varepsilon_k/(128M)$ at the splits indexed by $k$, where $M\coloneqq2GW/\log 2$ (Eq. (158)). The Lean definition allows any rule that maps $t$ and $L$ to nonnegative weights $\widehat p_t$ on $0,\ldots,\lfloor\log_2 t\rfloor+1$ summing to one, with positive total weight on the active base learners. Whenever $|L_i|\le 2M(t-1)$ for all $i$ and $L_{\lfloor\log_2 t\rfloor+1}=0$, the rule must satisfy $\lVert\widehat p_t-p_t\rVert_1\le (t+1)^{-2}$.
--
--   Algorithm 5 normalizes $\widehat p_t$ over the active base learners to obtain the mixing proportions $\pi_{t,i}$. If $w_t^{(i)}$ is the prediction of base learner $i$, Algorithm 5 plays $w_t=\sum_{i=0}^{\lfloor\log_2 t\rfloor}\pi_{t,i}w_t^{(i)}$ and then observes $g_t$ (Eq. (160)). It computes $a_{t,i}\coloneqq\langle g_t,w_t-w_t^{(i)}\rangle$ and sends base learner $i$ the input $\frac{1-\varepsilon_i/2}{1+\varepsilon_i/2}g_t$ if $a_{t,i}>0$, $\frac{1+\varepsilon_i/2}{1-\varepsilon_i/2}g_t$ if $a_{t,i}<0$, and $g_t$ otherwise. It adds $-\bigl(a_{t,i}-\frac{\varepsilon_i}{2}|a_{t,i}|\bigr)$ to the cumulative corrected loss of base learner $i$.
--
--   The file also defines $N_T(u)\coloneqq\sum_{t=1}^T\max\{\langle g_t,u-w_t\rangle,0\}$ for the predictions $w_t$ of Algorithm 5 and the constant of Theorem 1. These definitions follow Section 4 and Appendices C.1 and C.4.
-- source:
--   arXiv:2611.27572v1, Algorithm 5, p. 46; Appendices C.1–C.4, pp. 44–50; Algorithm 4, p. 42. https://arxiv.org/html/2611.27572v1#algorithm5

import Definitions.Def_Curvature_DomainGeometry
import Definitions.Def_Curvature_DyadicRun
import Definitions.Def_Curvature_FixedAxes
import Definitions.Def_Curvature_WidthAndSignGame
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}

def adaptiveRate (i : ℕ) : ℝ := 1 / (8 * (2 : ℝ)^i)

def adaptiveStart (i : ℕ) : ℕ := 2^i - 1

def adaptiveLoss (θ r : ℝ) : ℝ := r - θ * |r|

def adaptiveNegative (T : ℕ) (r : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, max 0 (-r t)


end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}

def adaptiveScale (θ a : ℝ) : ℝ :=
  if 0 < a then (1 - θ) / (1 + θ) else
  if a < 0 then (1 + θ) / (1 - θ) else 1


end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

def adaptiveEta (M : ℝ) (i : ℕ) : ℝ := adaptiveRate i / (128*M)

def binaryMean (q x y : ℝ) : ℝ := q*x + (1-q)*y

def binaryMix (η q x y : ℝ) : ℝ :=
  -Real.log (binaryMean q (Real.exp (-η*x)) (Real.exp (-η*y))) / η

def binaryLeftWeight (η x y : ℝ) : ℝ :=
  Real.exp (-η*x) / (Real.exp (-η*x) + Real.exp (-η*y))


def adaptivePotential (M : ℝ) (L : ℕ → ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => L k
  | n+1 => binaryMix (adaptiveEta M k) (1/2) (L k) (adaptivePotential M L (k+1) n)

def adaptiveExactMean (M : ℝ) (L v : ℕ → ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => v k
  | n+1 => binaryMean (binaryLeftWeight (adaptiveEta M k) (L k)
      (adaptivePotential M L (k+1) n)) (v k) (adaptiveExactMean M L v (k+1) n)


def adaptiveProbability (M : ℝ) (L : ℕ → ℝ) (k n j : ℕ) : ℝ :=
  adaptiveExactMean M L (fun i => if i=j then 1 else 0) k n


end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature


def adaptiveUpdate (i : ℕ) (r : ℝ) : ℝ := -adaptiveLoss (adaptiveRate i/2) r


end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)}

def adaptiveAwake (t : ℕ) : ℕ := Nat.log 2 (t+1)


structure AdaptiveRunState (d : ℕ) where
  loss : ℕ → ℝ
  feedback : ℕ → ℕ → Vec d

def adaptiveMixTolerance (t : ℕ) : ℝ := 1 / ((t : ℝ)+2)^2

/-- The weights used on a round are chosen from the cumulative losses so far. -/
structure AdaptiveWeightRule (M : ℝ) where
  prob : (ℕ → ℝ) → ℕ → ℕ → ℝ
  nonnegative : ∀ L t i, 0 ≤ prob L t i
  total : ∀ L t, (∑ i ∈ Finset.Icc 0 (0+(adaptiveAwake t+1)), prob L t i) = 1
  awake_positive : ∀ L t, 0 < ∑ i ∈ Finset.range (adaptiveAwake t+1), prob L t i
  approximation : ∀ L (t : ℕ), (∀ i, |L i| ≤ 2*M*(t : ℝ)) → L (adaptiveAwake t+1) = 0 →
    (∑ i ∈ Finset.Icc 0 (0+(adaptiveAwake t+1)),
      |adaptiveProbability M L 0 (adaptiveAwake t+1) i - prob L t i|) ≤ adaptiveMixTolerance t


def adaptiveAwakeMass {M : ℝ} (P : AdaptiveWeightRule M) (L : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (adaptiveAwake t+1), P.prob L t i

def adaptiveWeight {M : ℝ} (P : AdaptiveWeightRule M) (L : ℕ → ℝ) (t i : ℕ) : ℝ :=
  P.prob L t i / adaptiveAwakeMass P L t

theorem adaptiveWeight_nonneg {M : ℝ} (P : AdaptiveWeightRule M) (L : ℕ → ℝ) (t i : ℕ) :
    0 ≤ adaptiveWeight P L t i := div_nonneg (P.nonnegative L t i) (P.awake_positive L t).le

theorem adaptiveWeight_sum {M : ℝ} (P : AdaptiveWeightRule M) (L : ℕ → ℝ) (t : ℕ) :
    (∑ i ∈ Finset.range (adaptiveAwake t+1), adaptiveWeight P L t i) = 1 := by
  simp only [adaptiveWeight, ← Finset.sum_div]
  change adaptiveAwakeMass P L t / adaptiveAwakeMass P L t = 1
  exact div_self (P.awake_positive L t).ne'

/-- A fixed-parameter learner and its signed regret bound, valid for all input streams. -/
structure AdaptiveBase (K : Set (Vec d)) where
  cost : ℝ
  cost_nonneg : 0 ≤ cost
  play : ℝ → ℝ → (ℕ → Vec d) → ℕ → K
  play_prefix : ∀ G ε g g' t, (∀ i < t, g i = g' i) → play G ε g t = play G ε g' t
  playedRegret : ∀ {G ε : ℝ}, 0 < G → 0 < ε → ε ≤ 1 →
    ∀ (g : ℕ → Vec d), (∀ t, norm₂ (g t) ≤ G) → ∀ (u : K) (T : ℕ),
      let r := fun t => excess (g t) (play G ε g t).val u.val
      2*(∑ t ∈ Finset.range T, r t) - ε*(∑ t ∈ Finset.range T, |r t|) ≤ G * cost / ε

namespace AdaptiveBase
variable (B : AdaptiveBase K) (hcv : Convex ℝ K) {M : ℝ} (P : AdaptiveWeightRule M)

def adaptiveBasePlay (G : ℝ) (s : AdaptiveRunState d) (t i : ℕ) : K :=
  B.play (2*G) (adaptiveRate i)
    (fun j => s.feedback i (j + adaptiveStart i)) (t - adaptiveStart i)

def adaptiveRoundPlay (G : ℝ) (s : AdaptiveRunState d) (t : ℕ) : K :=
  ⟨∑ i ∈ Finset.range (adaptiveAwake t+1),
      adaptiveWeight P s.loss t i • (B.adaptiveBasePlay G s t i).val,
    hcv.sum_mem (fun i _ => adaptiveWeight_nonneg P s.loss t i) (adaptiveWeight_sum P s.loss t)
      (fun i _ => (B.adaptiveBasePlay G s t i).2)⟩

def adaptiveDifference (G : ℝ) (s : AdaptiveRunState d) (t : ℕ) (g : Vec d) (i : ℕ) : ℝ :=
  if i ≤ adaptiveAwake t then
    excess g (B.adaptiveRoundPlay hcv P G s t).val
      (B.adaptiveBasePlay G s t i).val
  else 0


def adaptiveStep (G : ℝ) (s : AdaptiveRunState d) (t : ℕ) (g : Vec d) : AdaptiveRunState d :=
  let a := B.adaptiveDifference hcv P G s t g
  { loss := fun i => s.loss i + adaptiveUpdate i (a i)
    feedback := fun i j => if i ≤ adaptiveAwake t ∧ j=t then
      adaptiveScale (adaptiveRate i/2) (a i) • g else s.feedback i j }

def adaptiveStateAfter (G : ℝ) (g : ℕ → Vec d) : ℕ → AdaptiveRunState d
  | 0 => ⟨0, 0⟩
  | t+1 => B.adaptiveStep hcv P G (adaptiveStateAfter G g t) t (g t)

def adaptivePlay (G : ℝ) (g : ℕ → Vec d) (t : ℕ) : K :=
  B.adaptiveRoundPlay hcv P G (B.adaptiveStateAfter hcv P G g t) t


section Run
variable (G : ℝ) (g : ℕ → Vec d)

local notation "s" => B.adaptiveStateAfter hcv P G g
local notation "a" => B.adaptiveDifference hcv P G
local notation "w" => B.adaptiveRoundPlay hcv P G
local notation "b" => B.adaptiveBasePlay G


end Run
end AdaptiveBase
end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {N d : ℕ} [NeZero N]

/-- Choices of the supplied fixed-matrix representation, including the three canonical computations. -/
inductive FixedAxisInitialization (a : Vec N) (q : ℝ) where
  | exactAxes
  | ball (R : ℝ) (constant : a = fun _ => R)
  | ellipsoid (exponent : q = 2)
  | box (exponent : q = 1)

def FixedAxisInitialization.diagonal {a : Vec N} {q : ℝ} (mode : FixedAxisInitialization a q)
    (ε : ℝ) (i : Fin N) : ℝ :=
  match mode with
  | .exactAxes => fixedAxisDiagonal a q ε i
  | .ball R _ => roundedBallDiagonal N q R ε
  | .ellipsoid _ => roundedEllipsoidDiagonal a ε
  | .box _ => (10/ε)*a i

theorem FixedAxisInitialization.diagonal_bounds {a : Vec N} {q : ℝ} (mode : FixedAxisInitialization a q)
    (ha : ∀ i, 0 < a i) (hq : 1 ≤ q) (hq' : q ≤ 2) {ε : ℝ} (hε : 0 < ε) (i : Fin N) :
    let D := mode.diagonal ε i
    fixedAxisDiagonal a q ε i ≤ D ∧ D ≤ 3*fixedAxisDiagonal a q ε i := by
  have hpos : 0 < fixedAxisDiagonal a q ε i := mul_pos
    (div_pos (mul_pos (by norm_num) (fixedAxisScale_pos ha q)) hε)
    (Real.rpow_pos_of_pos (fixedAxisWeight_pos ha q i) _)
  cases mode with
  | exactAxes => exact ⟨le_rfl, by dsimp [diagonal]; linarith only [hpos]⟩
  | ball R hc =>
    subst a
    exact roundedBallDiagonal_bounds hq hq' (ha i) hε i
  | ellipsoid hq =>
    subst q
    exact roundedEllipsoidDiagonal_bounds ha hε i
  | box hq =>
    subst q
    dsimp [diagonal]
    rw [fixedBoxDiagonal ha]
    constructor <;> nlinarith [mul_pos (by positivity : 0 < 10/ε) (ha i)]

variable {K : Set (Vec d)}

def fixedDomainState (hne : K.Nonempty) (hc : IsCompact K) (hK : Convex ℝ K)
    (center : Vec d) (A : Matrix (Fin d) (Fin N) ℝ)
    {a : Vec N} {q : ℝ} (mode : FixedAxisInitialization a q) (G ε : ℝ) (g : ℕ → Vec d) :=
  let H := Matrix.diagonal (mode.diagonal ε)
  let cov :=  A.transpose*A
  fixedRun H ε (fixedThreshold (fixedAdditionScale cov H ε)) (fun i z =>
    A.transpose.mulVec (normalizedDomainInput hne hc hK center A G g i z))

def fixedDomainPlay (hne : K.Nonempty) (hc : IsCompact K) (hK : Convex ℝ K)
    (center : Vec d) (A : Matrix (Fin d) (Fin N) ℝ) {a : Vec N} {q : ℝ}
    (mode : FixedAxisInitialization a q) (G ε : ℝ) (g : ℕ → Vec d) (t : ℕ) : K :=
  domainProjection hne hc hK (center + A.mulVec (fixedDomainState hne hc hK center A mode G ε g t).z)

theorem fixedDomainPlay_prefix (hne : K.Nonempty) (hc : IsCompact K) (hK : Convex ℝ K)
    (center : Vec d) (A : Matrix (Fin d) (Fin N) ℝ) {a : Vec N} {q : ℝ}
    (mode : FixedAxisInitialization a q) (G ε : ℝ) (g g' : ℕ → Vec d) (t : ℕ)
    (heq : ∀ i < t, g i = g' i) :
    fixedDomainPlay hne hc hK center A mode G ε g t = fixedDomainPlay hne hc hK center A mode G ε g' t := by
  suffices fixedDomainState hne hc hK center A mode G ε g t =
      fixedDomainState hne hc hK center A mode G ε g' t by simp [fixedDomainPlay, this]
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs := ih fun i hi => heq i (Nat.lt_succ_of_lt hi)
    let H := Matrix.diagonal (mode.diagonal ε)
    let update (s : BallState N) (input : Vec d) :=
      let x := center+A.mulVec s.z
      let w := (domainProjection hne hc hK x).val
      generalStep ε (fixedThreshold (fixedAdditionScale (A.transpose*A) H ε) t) (t+1)
        s (A.transpose.mulVec (G⁻¹ • correctDomainInput x w input))
    change update (fixedDomainState hne hc hK center A mode G ε g t) (g t) =
      update (fixedDomainState hne hc hK center A mode G ε g' t) (g' t)
    rw [hs, heq t (Nat.lt_succ_self t)]

theorem fixedAxesPlayedWidth (hne : K.Nonempty) (hc : IsCompact K) (hK : Convex ℝ K)
    (center : Vec d) (A : Matrix (Fin d) (Fin N) ℝ)
    {a : Vec N} (ha : ∀ i, 0 < a i) {q : ℝ} (hq : 1 ≤ q) (hq' : q ≤ 2)
    (hgA : A.transpose*A = Matrix.diagonal (fun i => a i^2))
    (hbody : K = (fun v => center + A.mulVec v) '' {v | fixedUnitCoeffs q v})
    (mode : FixedAxisInitialization a q) {G ε : ℝ} (hG : 0 < G) (hε : 0 < ε) (hε' : ε ≤ 1)
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ G) (u : K) (T : ℕ) :
    let r := fun t => excess (g t) (fixedDomainPlay hne hc hK center A mode G ε g t).val u.val
    2 * (∑ i ∈ Finset.range T, r i) - ε*(∑ i ∈ Finset.range T, |r i|) ≤
      (164*G/ε)*coordinateWidth K := by
  have hw : fixedAxisScale a q/4 ≤ coordinateWidth K := fixedAxisWidth_lower hc center A ha hgA hq
    (fun v hv => hbody ▸ Set.mem_image_of_mem _ hv)
  obtain ⟨v, hv, huv⟩ := (show u.val ∈ (fun v => center+A.mulVec v) '' {v | fixedUnitCoeffs q v}
    from hbody ▸ u.prop)
  change center + A.mulVec v = u.val at huv
  let ambient := normalizedDomainInput hne hc hK center A G g
  let feed := fun t z => A.transpose.mulVec (ambient t z)
  let H := Matrix.diagonal (mode.diagonal ε)
  let s := fixedDomainState hne hc hK center A mode G ε g
  let rin := fun t => excess (feed t (s t).z) (s t).z v
  let r := fun t => excess (g t) (fixedDomainPlay hne hc hK center A mode G ε g t).val u.val
  have hfeed : ∀ t z, (Matrix.diagonal (fun i => a i^2) -
      Matrix.vecMulVec (feed t z) (feed t z)).PosSemidef := by
    intro t z
    rw [← hgA]
    exact gram_sub_rankOne_posSemidef A _ (normalizedDomainInput_norm hne hc hK center A hG g hg t z)
  have hD := mode.diagonal_bounds ha hq hq' hε
  have hb := fixedRoundedAxisBound ha hq hq' hε hε' (fun i => (hD i).1) (fun i => (hD i).2)
    feed (fun t => hfeed t _) v hv T
  rw [← hgA] at hb
  change 2*(∑ i ∈ Finset.range T, rin i)-ε*(∑ i ∈ Finset.range T, |rin i|) +
    dotProduct (v-(s T).z) (H.mulVec (v-(s T).z)) ≤ _ at hb
  have hH : H.PosDef := Matrix.PosDef.diagonal fun i => lt_of_lt_of_le
    (mul_pos (div_pos (mul_pos (by norm_num) (fixedAxisScale_pos ha q)) hε)
      (Real.rpow_pos_of_pos (fixedAxisWeight_pos ha q i) _)) (hD i).1
  have hdist : 0 ≤ dotProduct (v-(s T).z) (H.mulVec (v-(s T).z)) := by
    simpa using hH.posSemidef.dotProduct_mulVec_nonneg (v-(s T).z)
  have hi := (le_add_of_nonneg_right hdist).trans hb
  have ht := signedRegret_domainProjection_le_internal hne hc hK center A (fun t => (s t).z)
    v (huv ▸ u.prop) g hG hg hε.le (hε'.trans (by norm_num)) T
  dsimp only at ht
  rw [huv] at ht
  change (∑ t ∈ Finset.range T, (2*r t-ε*|r t|)) ≤ G*(∑ t ∈ Finset.range T, (2*rin t-ε*|rin t|)) at ht
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at ht
  apply ht.trans
  calc
    _ ≤ G*(41*fixedAxisScale a q/ε) := mul_le_mul_of_nonneg_left hi hG.le
    _ = (164*G/ε)*(fixedAxisScale a q/4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)

end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)}

private theorem adaptiveWidth_nonneg (hne : K.Nonempty) (hc : IsCompact K) :
    0 ≤ coordinateWidth K := by
  obtain ⟨x,hx⟩ := hne
  have hh := (norm₂_nonneg (x-x)).trans (coordinateWidth_pair hc ⟨x,hx⟩ ⟨x,hx⟩)
  have hnum := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp hh
  linarith only [hnum]

def AdmissibleDescription.adaptiveBase (D : AdmissibleDescription K)
    (hne : K.Nonempty) (hc : IsCompact K) (hcv : Convex ℝ K) : AdaptiveBase K where
  cost := 192*D.representationCost
  cost_nonneg := mul_nonneg (by norm_num)
    ((adaptiveWidth_nonneg hne hc).trans (width_le_representationCost D hne hc))
  play := D.play hne hc hcv
  play_prefix := D.play_prefix hne hc hcv
  playedRegret hG hε hε' g hg u T :=
    (D.playedRegret hne hc hcv hG hε hε' g hg u T).trans_eq (by ring)


def AdaptiveBase.fixedAxes {N : ℕ} [NeZero N] (hne : K.Nonempty) (hc : IsCompact K)
    (hcv : Convex ℝ K) (center : Vec d) (A : Matrix (Fin d) (Fin N) ℝ)
    {a : Vec N} (ha : ∀ i, 0 < a i) {q : ℝ} (hq : 1 ≤ q) (hq' : q ≤ 2)
    (hgA : A.transpose*A = Matrix.diagonal (fun i => a i^2))
    (hbody : K = (fun v => center+A.mulVec v) '' {v | fixedUnitCoeffs q v})
    (mode : FixedAxisInitialization a q) : AdaptiveBase K where
  cost := 164*coordinateWidth K
  cost_nonneg := mul_nonneg (by norm_num) (adaptiveWidth_nonneg hne hc)
  play := fixedDomainPlay hne hc hcv center A mode
  play_prefix := fixedDomainPlay_prefix hne hc hcv center A mode
  playedRegret hG hε hε' g hg u T :=
    (fixedAxesPlayedWidth hne hc hcv center A ha hq hq' hgA hbody mode hG hε hε' g hg u T).trans_eq
      (by ring)

def adaptiveBaseWidthFactor : ℝ := 393216

def adaptiveWidthScale (G W : ℝ) : ℝ := 2*G*W / Real.log 2

def adaptiveWidthConstant : ℝ := 24 * (adaptiveBaseWidthFactor + 514/Real.log 2)


end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature
variable {d : ℕ} {K : Set (Vec d)}

/-- The geometric data supplied once to the fixed-parameter update. -/
inductive DomainInitialization (K : Set (Vec d)) where
  | dyadic (D : AdmissibleDescription K) (hcost : D.representationCost ≤ 2048*coordinateWidth K)
  | fixed {N : ℕ} [NeZero N] (center : Vec d) (A : Matrix (Fin d) (Fin N) ℝ)
      {a : Vec N} (ha : ∀ i, 0 < a i) {q : ℝ} (hq : 1 ≤ q) (hq' : q ≤ 2)
      (hgram : A.transpose*A = Matrix.diagonal (fun i => a i^2))
      (hbody : K = (fun v => center + A.mulVec v) '' {v | fixedUnitCoeffs q v})
      (mode : FixedAxisInitialization a q)

namespace DomainInitialization


def adaptiveBase (I : DomainInitialization K) (hne : K.Nonempty) (hc : IsCompact K)
    (hcv : Convex ℝ K) : AdaptiveBase K :=
  match I with
  | .dyadic D _ => D.adaptiveBase hne hc hcv
  | @DomainInitialization.fixed _ _ N inst center A _ ha _ hq hq' hgram hbody mode =>
    @AdaptiveBase.fixedAxes d K N inst hne hc hcv center A _ ha _ hq hq' hgram hbody mode


end DomainInitialization


end Curvature

end
end


