-- Prove2me | Definitions.Def_MinimaxInterventions1429_Separable_Algorithm
-- name    : MinimaxInterventions1429_Separable_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:13.339772+00:00
-- url     : https://prove2.me/theorems/6d3f98c0-ca65-4fab-8a45-6a3dcd39748f
-- title:
--   Section 3.2 deterministic contrast, anchor and alignment algorithm
-- statement:
--   Fix dimensions $m,k\ge2$, tolerance $\alpha\ge0$, and integer precision $T\ge1$. The reconstruction is an explicit finite bit-query program that receives no hidden table. It first searches every contrast $(g,h)$ with $h\ne1$ in row-column order and sets the reference-column estimate to zero. Its contrast-only output is
--
--   $$\widehat L^{\mathrm{contrast}}_{gh}=\tfrac12+\widehat\omega_{gh}
--   -\tfrac12\bigl(\max_j\widehat\omega_{gj}+\min_j\widehat\omega_{gj}\bigr).$$
--
--   For alignment it computes the estimated contrast diameter and fails when it is at most $8z$, where $z=\alpha+2(2\alpha+2^{-T})$. Otherwise it chooses the first maximizing column, then its first maximizing and first minimizing rows as anchors. It joins the anchors, attaches every other row to its farther anchor in the max-coordinate distance, and breaks equal-distance ties towards the root anchor.
--
--   For each child-parent pair, it chooses the first column whose absolute estimated contrast difference exceeds $4z$, orders the two rows to make the difference positive, runs the saturated level search for $T$ calls, and negates the estimate if the pair was reversed. The other anchor is processed first, followed by the other rows in increasing order. The root level is zero; child levels are computed by addition to their parent level. The output is $\widehat a_g+\widehat\omega_{gh}$ together with the root index, or a failure symbol.
--
--   For totality, absent eligible columns cause failure even on invalid bit strings. Theorem 3.5 asserts eligibility and tree depth and diameter as conclusions about the constructed plan. Neither these properties nor a successful estimate is stored in its data. Every choice is a public function of the transcript. This is the same contrast prefix used in both the main reconstruction and Proposition 3.7.
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Section 3.2, printed p.11 (PDF p.13); Section 3.3, Proposition 3.7, printed p.13 (PDF p.15)

import Definitions.Def_MinimaxInterventions1429_Separable_BitPrograms
set_option autoImplicit false

noncomputable section

namespace MinimaxInterventions1429.Separable

/-- First extremizer in the source order; a total public function on finite nonempty arrays. -/
def firstMax {n : ℕ} [NeZero n] (f : Fin n → ℝ) : Fin n :=
  (List.finRange n).foldl (fun a b => if f a < f b then b else a) 0

def firstMin {n : ℕ} [NeZero n] (f : Fin n → ℝ) : Fin n := firstMax (fun i => -f i)

def rowDistance {m k : ℕ} (w : Table m k) (g r : Fin m) : ℝ :=
  ⨆ h, |w g h - w r h|

def estimatedDiameter {m k : ℕ} (w : Table m k) : ℝ :=
  ⨆ h, (⨆ g, w g h) - (⨅ g, w g h)

structure AnchorPlan (m : ℕ) where
  root : Fin m
  other : Fin m
  parent : Fin m → Fin m

def planAnchors {m k : ℕ} [NeZero m] [NeZero k]
    (α : ℝ) (T : ℕ) (w : Table m k) : Option (AnchorPlan m) := by
  classical
  let z := effectiveTolerance α (2 * α + eta T)
  if estimatedDiameter w ≤ 8 * z then exact none
  else
    let h := firstMax (fun j => (⨆ g, w g j) - (⨅ g, w g j))
    let g₀ := firstMax (fun g => w g h)
    let r₀ := firstMin (fun g => w g h)
    exact some ⟨g₀, r₀, fun g =>
      if g = g₀ then g₀ else if g = r₀ then g₀
      else if rowDistance w g g₀ ≥ rowDistance w g r₀ then g₀ else r₀⟩

def contrastPairs (m k : ℕ) [NeZero k] : List (Fin m × Fin k) :=
  ((List.finRange m).flatMap (fun g => (List.finRange k).map (fun h => (g, h)))).filter
    (fun gh => gh.2 != 0)

def estimateContrasts {m k : ℕ} [NeZero k] (α : ℝ) (T : ℕ) :
    List (Fin m × Fin k) → Table m k → BitProgram m k (Table m k)
  | [], w => .done w
  | (g, h) :: rest, w => (contrastSearch α T g h).bind (fun x =>
    estimateContrasts α T rest (fun r j => if r = g ∧ j = h then x else w r j))

def contrastPhase (m k : ℕ) [NeZero k] (α : ℝ) (T : ℕ) : BitProgram m k (Table m k) :=
  estimateContrasts α T (contrastPairs m k) 0

def eligibleColumn {m k : ℕ} [NeZero k] (w : Table m k)
    (z : ℝ) (g r : Fin m) : Option (Fin k) :=
  (List.finRange k).find? (fun h => decide (4 * z < |w g h - w r h|))

/-- Breadth-first order: the other anchor and then the remaining rows in source order. -/
def alignmentOrder {m : ℕ} (plan : AnchorPlan m) : List (Fin m) :=
  plan.other :: (List.finRange m).filter (fun g => g != plan.root && g != plan.other)

def estimateLevels {m k : ℕ} [NeZero k] (α : ℝ) (T : ℕ)
    (w : Table m k) (plan : AnchorPlan m) :
    List (Fin m) → (Fin m → ℝ) → BitProgram m k (Option (Fin m × Table m k))
  | [], a => .done (some (plan.root, fun g h => a g + w g h))
  | g :: rest, a =>
    let r := plan.parent g
    let κ := 2 * α + eta T
    match eligibleColumn w (effectiveTolerance α κ) g r with
    | none => .done none
    | some h =>
      if w g h > w r h then
        (levelSearch α κ T w g r h).bind (fun x =>
          estimateLevels α T w plan rest (Function.update a g (a r + x)))
      else
        (levelSearch α κ T w r g h).bind (fun x =>
          estimateLevels α T w plan rest (Function.update a g (a r - x)))

/-- The Section 3.2 algorithm, defined without the hidden payoff table. -/
def reconstruction (m k : ℕ) [NeZero m] [NeZero k] (α : ℝ) (T : ℕ) :
    BitProgram m k (Option (Fin m × Table m k)) :=
  (contrastPhase m k α T).bind (fun w =>
    match planAnchors α T w with
    | none => .done none
    | some plan => estimateLevels α T w plan (alignmentOrder plan) 0)

def contrastEstimate (m k : ℕ) [NeZero k] (α : ℝ) (T : ℕ) : BitProgram m k (Table m k) :=
  (contrastPhase m k α T).bind (fun w => .done (centeredProfile w))

end MinimaxInterventions1429.Separable


