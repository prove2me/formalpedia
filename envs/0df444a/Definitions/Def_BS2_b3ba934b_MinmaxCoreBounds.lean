-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxCoreBounds
-- name    : BS2_b3ba934b_MinmaxCoreBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:26:52.931183+00:00
-- url     : https://prove2.me/theorems/8ba4772e-8f6b-4438-82e2-966fa0b7ada6
-- title:
--   Sensitivity separation: MinmaxCoreBounds (complete source module)
-- statement:
--   Complete Lean source module `MinmaxCoreBounds` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxCoreBounds.lean; original SHA-256 77d3d32befc4447195cc0469d2458936f80d224567187b0630cb46a727757bba; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Reuse verified A/M/P entries in the min/max conditional formula. -/
import Definitions.Def_BS2_b3ba934b_MinmaxExpressions

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundMinmaxNumeric
open ThreeBoundNumeric ThreeBoundFullProfile

def pCore (n pcross : ℕ) (v : Profile n) (j k l : Entry) (first : ℕ) : ℕ :=
  if j.same k then 0 else
    if j.tolerance=0 ∧ l.tolerance=0 ∧ j.plain ∧ k.plain ∧ l.plain then
      let tj := j.lowerAt 0
      let tk := k.lowerAt 0
      let tl := l.lowerAt 0
      let cross := pcross*(aExpr n j.guard tl).eval v
      let m0 := (minusExpr n l.guard tj tk).eval v
      let m1 := (minusExpr n l.guard k.guard j.guard).eval v
      let basic := 2*(bExpr n l.guard tj).eval v+cross+max ((plusExpr n tj tk tl).eval v) m1
      let target := if tj<tk then cross+max (max (2*m0) (m0+(bExpr n l.guard tk).eval v))
        ((unionExpr n l.guard tj tk tl).eval v+(bExpr n l.guard tl).eval v) else 0
      let guard := if k.guard<j.guard then cross+max (2*(bExpr n l.guard tk).eval v)
        (2*(bExpr n l.guard tl).eval v+m1) else 0
      min (min first basic) (max target guard)
    else first

def dCore (n degree : ℕ) (v : Profile n) (i j k l : Entry) (first : ℕ) : ℕ :=
  if j.same k then 0 else
    if j.tolerance=0 ∧ l.tolerance=0 ∧ l.plain ∧ k.upperAt 0≤l.lowerAt 0 then
      let ti := i.lowerAt 0
      let ui := i.upperAt 0
      let tj := j.lowerAt 0
      let uj := j.upperAt 0
      let tk := k.lowerAt 0
      let uk := k.upperAt 0
      let tl := l.lowerAt 0
      let a := (aExpr n l.guard i.guard).eval v
      min first (max ((pairMExpr n degree ti ui i.guard 0 tj uj j.guard tk uk k.guard).eval v)
        (max (if tj<tk then (bExpr n ui tl).eval v+degree*a+(unionExpr n ti tj tk tl).eval v else 0)
          (if k.guard<j.guard then (bExpr n ti tl).eval v+(bExpr n ui tl).eval v+(degree-1)*a+
            (unionExpr n l.guard k.guard j.guard i.guard).eval v else 0)))
    else first

theorem pCore_mono (n pcross : ℕ) (v : Profile n) (j k l : Entry) :
    Monotone (pCore n pcross v j k l) := by
  intro a b hab
  unfold pCore
  split_ifs <;> first | exact le_rfl | exact hab |
    exact min_le_min (min_le_min hab le_rfl) le_rfl

theorem dCore_mono (n degree : ℕ) (v : Profile n) (i j k l : Entry) :
    Monotone (dCore n degree v i j k l) := by
  intro a b hab
  unfold dCore
  split_ifs <;> first | exact le_rfl | exact hab | exact min_le_min hab le_rfl

theorem rawP_core (n pcross : ℕ) (v : Profile n) (rawA : Entry → Entry → Expr n)
    (j k l : Entry) :
    (rawPExpr n pcross rawA j k l).eval v=pCore n pcross v j k l ((rawA k l).eval v) := by
  simp only [rawPExpr,pCore]
  split_ifs <;> simp [Expr.eval,apply_ite]

theorem rawD_core (n degree pcross : ℕ) (v : Profile n) (rawA : Entry → Entry → Expr n)
    (i j k l : Entry) : (rawDExpr n degree pcross rawA i j k l).eval v=
      dCore n degree v i j k l ((rawMExpr n degree i j k).eval v+(rawPExpr n pcross rawA j k l).eval v) := by
  simp only [rawDExpr,dCore]
  split_ifs <;> simp [Expr.eval,apply_ite]

theorem rawP_bound_from_A (n pcross : ℕ) (v : Profile n) (rawA : Entry → Entry → Expr n)
    (j k l : Entry) (av pv : ℕ) (ha : (rawA k l).eval v≤av)
    (hp : pCore n pcross v j k l av≤pv) : (rawPExpr n pcross rawA j k l).eval v≤pv := by
  rw [rawP_core]
  exact (pCore_mono n pcross v j k l ha).trans hp

theorem rawD_bound_from_MP (n degree pcross : ℕ) (v : Profile n) (rawA : Entry → Entry → Expr n)
    (i j k l : Entry) (mv pv dv : ℕ)
    (hm : (rawMExpr n degree i j k).eval v≤ mv)
    (hp : (rawPExpr n pcross rawA j k l).eval v≤pv)
    (hd : dCore n degree v i j k l (mv+pv)≤dv) :
    (rawDExpr n degree pcross rawA i j k l).eval v≤dv := by
  rw [rawD_core]
  exact (dCore_mono n degree v i j k l (Nat.add_le_add hm hp)).trans hd

end ThreeBoundMinmaxNumeric

#print axioms ThreeBoundMinmaxNumeric.rawD_bound_from_MP


