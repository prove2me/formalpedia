-- Prove2me | Definitions.Def_BS2_b3ba934b_ProfileIntervals
-- name    : BS2_b3ba934b_ProfileIntervals
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:22:59.254553+00:00
-- url     : https://prove2.me/theorems/73bd7b44-8088-4ef7-85e4-2c8d6405247a
-- title:
--   Sensitivity separation: ProfileIntervals (complete source module)
-- statement:
--   Complete Lean source module `ProfileIntervals` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ProfileIntervals.lean; original SHA-256 d459359ece9a5eb9b94eebb512c181956cf125c4577048018b0a8a4b66a1a2e9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Semantic interpretation of interval maxima in the transfer formula. -/
import Definitions.Def_BS2_b3ba934b_NumericExpressions

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile

theorem bool_boundary (f : ℕ → Bool) (j k : ℕ) (hjk : j < k)
    (hj : f j = true) (hk : f k = false) :
    ∃ m, j ≤ m ∧ m < k ∧ f m = true ∧ f (m+1) = false := by
  induction k with
  | zero => omega
  | succ k ih =>
      cases hm : f k with
      | true => exact ⟨k,by omega,by omega,hm,hk⟩
      | false =>
          have hjk' : j < k := by
            by_contra h
            have : j = k := by omega
            subst j
            simp [hm] at hj
          obtain ⟨m,hmj,hmk,hmt,hmf⟩ := ih hjk' hm
          exact ⟨m,hmj,by omega,hmt,hmf⟩

theorem fin_bool_boundary {n : ℕ} (f : Fin n → Bool) (j k : Fin n)
    (hjk : j < k) (hj : f j = true) (hk : f k = false) :
    ∃ m : Fin n, j ≤ m ∧ m < k ∧ f m = true ∧ f (next m) = false := by
  let ff : ℕ → Bool := fun a => if h : a < n then f ⟨a,h⟩ else false
  have hj' : ff j.val = true := by simpa [ff] using hj
  have hk' : ff k.val = false := by simpa [ff] using hk
  obtain ⟨m,hmj,hmk,hmt,hmf⟩ := bool_boundary ff j.val k.val hjk hj' hk'
  have hmn : m < n := hmk.trans k.isLt
  have hmn' : m+1 < n := lt_of_le_of_lt hmk k.isLt
  refine ⟨⟨m,hmn⟩,hmj,hmk,?_,?_⟩
  · simpa [ff,hmn] using hmt
  · simpa [ff,hmn',next] using hmf

variable {n : ℕ} {I : Type} [Fintype I]

theorem aExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j : Fin n) (hij : i ≤ j) :
    ABound F i j ((aExpr n i.val j.val).eval v) := by
  simpa only [aExpr, dif_pos i.isLt, dif_pos j.isLt, Expr.eval] using hv (.a i j) hij

theorem bExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j : Fin n) (hij : i ≤ j) :
    BBound F i j ((bExpr n i.val j.val).eval v) := by
  simpa only [bExpr, dif_pos i.isLt, dif_pos j.isLt, Expr.eval] using hv (.b i j) hij

theorem minusExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j k : Fin n) (hij : i ≤ j) (hjk : j < k) :
    MBound F i j k ((minusExpr n i.val j.val k.val).eval v) := by
  intro x hj hk
  obtain ⟨m,hmj,hmk,hmt,hmf⟩ := fin_bool_boundary (fun t => F t x) j k hjk hj hk
  have hmn : m.val+1 < n := lt_of_le_of_lt hmk k.isLt
  have hm := hv (.m i m) (hij.trans hmj) hmn x hmt hmf
  apply hm.trans
  simp only [minusExpr, if_pos (show i.val ≤ j.val ∧ j.val < k.val from ⟨hij,hjk⟩),
    Expr.eval_maximum, List.map_map]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  refine ⟨m.val,mem_interval.mpr ⟨hmj,hmk⟩,?_⟩
  simp only [Function.comp_apply,mExpr,dif_pos i.isLt,dif_pos m.isLt,Expr.eval]

theorem plusExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j k : Fin n) (hij : i < j) (hjk : j ≤ k) :
    PBound F i j k ((plusExpr n i.val j.val k.val).eval v) := by
  intro x hi hj
  obtain ⟨m,hmi,hmj,hmt,hmf⟩ := fin_bool_boundary (fun t => F t x) i j hij hi hj
  have hm := hv (.p m k) (hmj.trans_le hjk) x hmt hmf
  apply hm.trans
  simp only [plusExpr, if_pos (show i.val < j.val ∧ j.val ≤ k.val from ⟨hij,hjk⟩),
    Expr.eval_maximum, List.map_map]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  refine ⟨m.val,mem_interval.mpr ⟨hmi,hmj⟩,?_⟩
  simp only [Function.comp_apply,pExpr,dif_pos m.isLt,dif_pos k.isLt,Expr.eval]

theorem unionExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j k l : Fin n)
    (hij : i ≤ j) (hjk : j < k) (hkl : k ≤ l) :
    DBound F i j k l ((unionExpr n i.val j.val k.val l.val).eval v) := by
  intro x hj hk
  obtain ⟨m,hmj,hmk,hmt,hmf⟩ := fin_bool_boundary (fun t => F t x) j k hjk hj hk
  have hm := hv (.d i m l) (hij.trans hmj) (hmk.trans_le hkl) x hmt hmf
  apply hm.trans
  simp only [unionExpr, if_pos
    (show i.val ≤ j.val ∧ j.val < k.val ∧ k.val ≤ l.val from ⟨hij,hjk,hkl⟩),
    Expr.eval_maximum, List.map_map]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  refine ⟨m.val,mem_interval.mpr ⟨hmj,hmk⟩,?_⟩
  simp only [Function.comp_apply,dExpr,dif_pos i.isLt,dif_pos m.isLt,dif_pos l.isLt,Expr.eval]

end ThreeBoundNumeric

#print axioms ThreeBoundNumeric.minusExpr_bound
#print axioms ThreeBoundNumeric.plusExpr_bound
#print axioms ThreeBoundNumeric.unionExpr_bound


