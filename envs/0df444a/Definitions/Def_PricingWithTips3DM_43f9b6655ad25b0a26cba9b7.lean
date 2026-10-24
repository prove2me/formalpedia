-- Prove2me | Definitions.Def_PricingWithTips3DM_43f9b6655ad25b0a26cba9b7
-- name    : PricingWithTips3DM_43f9b6655ad25b0a26cba9b7
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:19:40.789192+00:00
-- url     : https://prove2.me/theorems/4942190c-64c3-4f8e-b02c-d00eb12d3221
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Logic.Sat3.BoundedOcc
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Definitions.Def_PricingWithTips3DM_559a735c0442b6eef1922892
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# 3SAT with clauses of length 2 or 3 and at most 3 occurrences per variable

The bounded-occurrence version of 3SAT: clauses have length exactly two or
three, and every variable occurs at most three times (counting every literal
position). A restriction of SAT in the sense of `Problem.restrict`, filed
under 3SAT, whose restriction it refines.

Length-2 clauses must be allowed for the restriction to be honest: by
Tovey's theorem, with all clauses of length exactly three the bounded
occurrences make the formula *always* satisfiable.

Hardness proofs (in `BoundedOcc/`): from SAT and from 3SAT
(`FromSat.lean`; relabel occurrences and chain them with implication
cycles; certified in `FromSat/Code.lean` and `FromSat/Adequacy.lean`).
-/

namespace Hardness

variable {V : Type*}



/-- Number of occurrences of variable `v` in `φ`: every position in every
clause counts, so a variable used twice in one clause occurs twice. -/
def CNF.varOccs [DecidableEq V] (φ : CNF V) (v : V) : ℕ :=
  (φ.map fun c ↦ c.countP fun l ↦ decide (l.var = v)).sum

/-- `varOccs` distributes over concatenation of formulas. -/
theorem CNF.varOccs_append [DecidableEq V] (φ₁ φ₂ : CNF V) (v : V) :
    CNF.varOccs (φ₁ ++ φ₂) v = CNF.varOccs φ₁ v + CNF.varOccs φ₂ v := by
  unfold CNF.varOccs
  rw [List.map_append, List.sum_append]

/-- `varOccs` of a `flatMap` is the sum of the `varOccs` of the pieces. -/
theorem CNF.varOccs_flatMap [DecidableEq V] {ι : Type*} (t : List ι)
    (F : ι → CNF V) (v : V) :
    CNF.varOccs (t.flatMap F) v = (t.map fun a ↦ CNF.varOccs (F a) v).sum := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih]
    exact CNF.varOccs_append ..

/-- Occurrence counts of a relabeled formula, as counts on the original: the
relabeled formula counts a label `w` wherever the original carries a variable
that `f` sends to `w`. -/
theorem CNF.varOccs_relabel_eq_countP [DecidableEq W] (f : V → W) (φ : CNF V)
    (w : W) :
    (φ.relabel f).varOccs w
      = (φ.map fun c ↦ c.countP fun l ↦ decide (f l.var = w)).sum := by
  unfold CNF.varOccs CNF.relabel
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun c _ ↦ ?_)
  rw [Function.comp_apply, List.countP_map]
  rfl

/-- A variable that does not occur is counted zero times. -/
theorem CNF.varOccs_eq_zero_of_notMem [DecidableEq V] {φ : CNF V} {v : V}
    (hv : v ∉ φ.vars) : φ.varOccs v = 0 := by
  refine List.sum_eq_zero fun n hn ↦ ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
  exact List.countP_eq_zero.mpr fun l hl h ↦
    hv (of_decide_eq_true h ▸ CNF.mem_vars hc hl)

/-- A label carried by no occurring variable is counted zero times in the
relabeled formula. -/
theorem CNF.varOccs_relabel_eq_zero [DecidableEq W] {f : V → W} {φ : CNF V}
    {w : W} (hw : ∀ v ∈ φ.vars, f v ≠ w) : (φ.relabel f).varOccs w = 0 := by
  rw [CNF.varOccs_relabel_eq_countP]
  refine List.sum_eq_zero fun n hn ↦ ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
  exact List.countP_eq_zero.mpr fun l hl h ↦
    hw l.var (CNF.mem_vars hc hl) (of_decide_eq_true h)

/-- At the label of an occurring variable, the relabeled count is that
variable's own count — provided `f` separates the occurring variables. -/
theorem CNF.varOccs_relabel_of_mem [DecidableEq V] [DecidableEq W] {f : V → W}
    {φ : CNF V} (hf : Set.InjOn f φ.vars) {v : V} (hv : v ∈ φ.vars) :
    (φ.relabel f).varOccs (f v) = φ.varOccs v := by
  rw [CNF.varOccs_relabel_eq_countP]
  unfold CNF.varOccs
  refine congrArg List.sum (List.map_congr_left fun c hc ↦ ?_)
  refine List.countP_congr fun l hl ↦ ?_
  have hlv : l.var ∈ φ.vars := CNF.mem_vars hc hl
  simp only [decide_eq_true_eq]
  exact ⟨fun h ↦ hf hlv hv h, fun h ↦ congrArg f h⟩

/-- **Relabeling preserves and reflects every occurrence bound**, provided the
map separates the occurring variables. Reflection needs the two lemmas above
together: a label carried by no occurring variable is counted zero times, and
a variable that does not occur is itself counted zero times, so neither side
can hide an excess from the other.

This is the form a representation theorem needs; the corollary
`CNF.varOccs_relabel_le` is the one gadget certificates use, transporting an
occurrence bound across the realization of tagged fresh names as numbers. -/
theorem CNF.forall_varOccs_relabel_le [DecidableEq V] [DecidableEq W] {f : V → W}
    {φ : CNF V} (hf : Set.InjOn f φ.vars) (m : ℕ) :
    (∀ w, (φ.relabel f).varOccs w ≤ m) ↔ ∀ v, φ.varOccs v ≤ m := by
  classical
  constructor
  · intro h v
    by_cases hv : v ∈ φ.vars
    · rw [← CNF.varOccs_relabel_of_mem hf hv]
      exact h _
    · rw [CNF.varOccs_eq_zero_of_notMem hv]
      exact Nat.zero_le m
  · intro h w
    by_cases hw : ∃ v ∈ φ.vars, f v = w
    · obtain ⟨v, hv, rfl⟩ := hw
      rw [CNF.varOccs_relabel_of_mem hf hv]
      exact h v
    · rw [CNF.varOccs_relabel_eq_zero (fun v hv hfv ↦ hw ⟨v, hv, hfv⟩)]
      exact Nat.zero_le m

/-- Relabeling along an injection cannot increase occurrence counts: `f v`
occurs in the relabeled formula exactly as often as `v` in the original, and
labels outside the range of `f` do not occur at all. This is what transports
the occurrence bound of a gadget across the realization of its tagged fresh
names as numbers. -/
theorem CNF.varOccs_relabel_le [DecidableEq V] [DecidableEq W] {f : V → W}
    (hf : Function.Injective f) {φ : CNF V} {m : ℕ}
    (h : ∀ v, φ.varOccs v ≤ m) (w : W) : (φ.relabel f).varOccs w ≤ m :=
  (CNF.forall_varOccs_relabel_le hf.injOn m).mpr h w

/-- 3SAT, restricted to clauses of length *two or three* with every variable
occurring at most three times — the bounded-occurrence version of 3SAT, in
the promise-free formulation of `Problem.restrict`.

Length-2 clauses must be allowed for the restriction to be honest: by Tovey's
theorem, a CNF all of whose clauses have length exactly three and whose
variables each occur at most three times is *always* satisfiable (via Hall's
theorem), so that variant is trivial rather than hard. Hardness proofs (in
`BoundedOcc/`): from SAT (`FromSat.lean`, `satToSat3Occ3`) and from 3SAT
(`sat3ToSat3Occ3`, by composition through weakening). -/
def SAT3_OCC3 : Problem SatInstance :=
  SAT.restrict fun x ↦
    (∀ c ∈ x.φ, 2 ≤ c.length ∧ c.length ≤ 3) ∧ ∀ v, x.φ.varOccs v ≤ 3

end Hardness


