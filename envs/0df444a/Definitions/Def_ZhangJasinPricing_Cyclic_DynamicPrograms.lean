-- Prove2me | Definitions.Def_ZhangJasinPricing_Cyclic_DynamicPrograms
-- name    : ZhangJasinPricing_Cyclic_DynamicPrograms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T06:58:13.299995+00:00
-- url     : https://prove2.me/theorems/6c809274-2edd-4cb1-afd3-33be46e378e0
-- title:
--   The decreasing and threshold dynamic programs with maximizing witnesses
-- statement:
--   Each dynamic program takes an arbitrary real reward table. The length-one entry at terminal price i is ([i],rᵢ). For longer lengths, the decreasing program considers appending i to the previous i-state with reward rᵢ, or appending i to a previous state j<i with the prescribed drop reward. The threshold program instead considers every split k+(t−k) with both parts ending in i, together with the same strict-drop branch. Every stage retains every maximizing word and its total value. A finite recursion fuel equal to requested length suffices for every smaller subproblem. Empty alternatives contribute no candidate, including when rewards are negative.
--
--   The final search compares these stage optima divided by their lengths, over all lengths from one to the supplied bound. OLD uses K+M−1 and OLT uses 2K+M−2. A measurable tie rule selects a maximizing candidate from any nonempty finite list, using only candidate values and encoded past observable prices, sales, and revenue. All such rules are quantified over in the learning results.
--
--   The duplicate j=i alternative printed in (2) is represented by its separate r_i branch, following the explanation on p. 10; the drop parameters are defined only for j<i.
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, §§3–6, p. 9 (PDF p. 9)

import Definitions.Def_ZhangJasinPricing_Cyclic_Policies
open MeasureTheory
open scoped Classical
noncomputable section

namespace ZhangJasinPricing.Cyclic
abbrev Plan := Word × ℝ
/-- Retain all maximizing witnesses, including all ties; no default-zero competitor. -/
def maximizers (xs : List Plan) : List Plan :=
  xs.filter (fun x => decide (∀ y ∈ xs, y.2 ≤ x.2))

/-- Recurrence (2) / (5), returning optimal words together with their total value.
The fuel bounds the requested length; recursive subproblems use smaller lengths. -/
def dp (mode : Mode) (K : ℕ) (r : Parameter → ℝ) : ℕ → ℕ → ℕ → List Plan
  | 0, _, _ => []
  | fuel+1, t, i =>
    if t = 1 then [([i], r (i,i,0))]
    else if t = 0 then []
    else
      let drops := (List.range i).flatMap (fun j =>
        (dp mode K r fuel (t-1) j).map (fun x =>
          (x.1 ++ [i], x.2 + r (j,i,min (t-1) K))))
      let same := match mode with
        | .decreasing => (dp mode K r fuel (t-1) i).map (fun x =>
            (x.1 ++ [i], x.2 + r (i,i,0)))
        | .threshold => (List.range (t-1)).flatMap (fun k =>
            (dp mode K r fuel (k+1) i).flatMap (fun x =>
              (dp mode K r fuel (t-(k+1)) i).map (fun y => (x.1 ++ y.1, x.2+y.2))))
      maximizers (same ++ drops)

def searchBound (mode : Mode) (M K : ℕ) : ℕ :=
  match mode with | .decreasing => K+M-1 | .threshold => 2*K+M-2

/-- All stage maximizers, normalized for the final length selection. -/
def dpOptions (mode : Mode) (M K b : ℕ) (r : Parameter → ℝ) : List Plan :=
  (List.range b).flatMap (fun n => (List.range M).flatMap (fun i =>
    (dp mode K r (n+1) (n+1) i).map (fun x => (x.1,x.2/(n+1 : ℕ)))))

/-- A tie rule sees only a numerical encoding of past prices, sales and revenues
and candidate values. It must choose a maximum for every nonempty candidate list.
Measurability is imposed on each finite-dimensional candidate-count slice. -/
structure TieRule where
  choose : ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℕ
  in_range : ∀ (n : ℕ) (h v : ℕ → ℝ), 0 < n → choose n h v < n
  maximum : ∀ (n : ℕ) (h v : ℕ → ℝ), 0 < n → ∀ j, j < n → v j ≤ v (choose n h v)
  measurable : ∀ n, Measurable (fun x : (ℕ → ℝ) × (ℕ → ℝ) => choose n x.1 x.2)

def selectPlan (tie : TieRule) (h : ℕ → ℝ) (xs : List Plan) : Plan :=
  xs[tie.choose xs.length h (fun j => (xs[j]?.getD ([],0)).2)]?.getD ([],0)
end ZhangJasinPricing.Cyclic


