-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_P21DetFront20261121
-- name    : LinearSetReconciliation327_Main_P21DetFront20261121
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-21T13:58:55.229217+00:00
-- url     : https://prove2.me/theorems/bc6e1b71-201b-446f-b4d9-3dc13f4dda63
-- title:
--   Proposition 2.1's decoder with the weakened det contract: read + key solver
-- statement:
--   The read stage and the key solver of Proposition 2.1's decoder, re-derived with the `det`
--   hypothesis weakened from `E.det = detStd t N b ι` to `DetAgrees`: agreement with `detStd` on the ten
--   header slots the decoder loads ($0,1,2,4,5,6,8,9,10,12$) and on every table address
--   $\ge \mathrm{detMulBase}(w) = 64$.  Slots $3$, $7$, $11$ and $13\dots63$ are therefore free for a
--   composite sketch's own header, which is what Theorem 6.5's row loop needs.
-- source:
--   arXiv:2611.11409, §2.1–2.2, Proposition 2.1; the four published stage contracts re-derived with the `det` hypothesis weakened to the slots the decoder reads.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderTables
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Definitions.Def_LinearSetReconciliation327_Main_P21RunStmt

/-!
# Proposition 2.1's decoder, weakened `det` contract — the read and key-solver stages

`pinsketch_decoding_at` is stated in `detEnv (8*w) (detStd t N b ι)`: the whole table must be
`detStd`.  A composite sketch needs its own header somewhere in `det`.  This bundle re-derives the
read stage, the key solver, and the shared read prologue with

  `DetAgrees E t N b ι` := agreement with `detStd` on the ten header slots the decoder reads
  (`0,1,2,4,5,6,8,9,10,12`) and on every table address `≥ detMulBase w`,

which leaves `3`, `7`, `11` and `13 … 63` free.  See `Def_…_P21DetBack20261121` for the root-search
and verifier stages and `Sol_p21_decode_at_det.lean` for the assembled contract.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace LinearSetReconciliation327.Main

/-!
# Proposition 2.1's decoder, weakened `det` contract

`pinsketch_decoding_at` (platform, Proved, id `19915f16-22fd-4377-b2e0-80c43a7a8a9f`) is stated in
`detEnv (8*w) (detStd t N b ι)`: it requires the *whole* table to be `detStd`.  A composite sketch
cannot meet that, because it must put its own header somewhere in `det`.  This file proves the
**weakened** contract: the decoder only ever reads

* the header slots `detHdrRead = {0,1,2,4,5,6,8,9,10,12}` (`paramBody` reads `0,1,4,5,6,12`;
  `saveHeaderCode` `0,4`; `saveDestinationCode` `0`; `decoderMetadataAssignments` `1,2`; the
  field-table codes `6,8,9,10`), and
* table addresses `≥ detMulBase w = 64`,

so agreeing with `detStd` on `detHdrRead ∪ [detMulBase w, ∞)` is enough.  Slots `3`, `7`, `11` and
`13 … 63` are free: the composite header may live there (`detExt`).

The four stage proofs are the published ones (`Theorems.Thm_…_pinsketch_decoder_{read, key_solver,
root_search, verifier}`, Proved on the platform), with `hdet` re-pointed from `E.det = detStd t N b ι`
to `DetAgrees E t N b ι`; the composition is `Sol_p21_decode_at.lean`'s, likewise re-pointed.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false


/-! ## 0. The read set, and the weakened contract -/

/-- The `det` header slots 2.1's decoder reads, extracted from `positiveDecoderStmt`. -/
def detHdrRead (a : ℕ) : Prop :=
  a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 12

instance detHdrRead_decidable (a : ℕ) : Decidable (detHdrRead a) := by
  unfold detHdrRead; infer_instance

/-- A `det` slot is **free** if the decoder never reads it as a header slot: everything below the
first table except the ten header slots.  Explicitly `3`, `7`, `11` and `13 … 63`. -/
def detFree (w a : ℕ) : Prop := ¬ detHdrRead a ∧ a < detMulBase w

instance detFree_decidable (w a : ℕ) : Decidable (detFree w a) := by
  unfold detFree; infer_instance

theorem detFree_three {w : ℕ} : detFree w 3 := by
  refine ⟨by decide, ?_⟩
  unfold detMulBase; norm_num

theorem detFree_seventeen {w : ℕ} : detFree w 17 := by
  refine ⟨by decide, ?_⟩
  unfold detMulBase; norm_num

theorem detFree_of_ge {w a : ℕ} (h13 : 13 ≤ a) (h64 : a < detMulBase w) : detFree w a := by
  refine ⟨?_, h64⟩
  intro h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

variable {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}
variable {b : Module.Basis (Fin w) (ZMod 2) F} {ι : ℕ → F}

/-- **The weakened `det` contract**: `E.det` agrees with `detStd` on every slot the decoder reads. -/
def DetAgrees (E : RAMEnv) (t N : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) : Prop :=
  (∀ a, detHdrRead a → E.det a = detStd t N b ι a) ∧
  (∀ a, detMulBase w ≤ a → E.det a = detStd t N b ι a)

/-- The **composite table**: 2.1's table, with the free slots replaced by the composite's header. -/
noncomputable def detExt (hdr : ℕ → ℕ) (t N : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (ι : ℕ → F) : ℕ → ℕ :=
  fun a => if detFree w a then hdr a else detStd t N b ι a

theorem detExt_of_free {hdr : ℕ → ℕ} {a : ℕ} (h : detFree w a) :
    detExt hdr t N b ι a = hdr a := by
  unfold detExt; rw [if_pos h]

theorem detExt_of_read {hdr : ℕ → ℕ} {a : ℕ} (h : ¬ detFree w a) :
    detExt hdr t N b ι a = detStd t N b ι a := by
  unfold detExt; rw [if_neg h]

/-- **`detExt` satisfies the weakened contract**, for *any* composite header. -/
theorem detExt_agrees (hdr : ℕ → ℕ) (t N : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (ι : ℕ → F) : DetAgrees (detEnv (8 * w) (detExt hdr t N b ι)) t N b ι := by
  constructor
  · intro a ha
    exact detExt_of_read (hdr := hdr) (fun hf => hf.1 ha)
  · intro a ha
    exact detExt_of_read (hdr := hdr) (fun hf => absurd hf.2 (by omega))


theorem detMulBase_le_detSqBase (w : ℕ) : detMulBase w ≤ detSqBase w := by
  unfold detSqBase; exact Nat.le_add_right _ _

theorem detSqBase_le_detInvBase (w : ℕ) : detSqBase w ≤ detInvBase w := by
  unfold detInvBase; exact Nat.le_add_right _ _

theorem detInvBase_le_detPosBase (w : ℕ) : detInvBase w ≤ detPosBase w := by
  unfold detPosBase; exact Nat.le_add_right _ _

theorem detPosBase_le_detImgBase (w : ℕ) : detPosBase w ≤ detImgBase w := by
  unfold detImgBase; exact Nat.le_add_right _ _

theorem detImgBase_le_detEnd (w : ℕ) : detImgBase w ≤ detEnd w := by
  unfold detEnd; exact Nat.le_add_right _ _

theorem detMulBase_le_detInvBase (w : ℕ) : detMulBase w ≤ detInvBase w :=
  le_trans (detMulBase_le_detSqBase w) (detSqBase_le_detInvBase w)

theorem detMulBase_le_detPosBase (w : ℕ) : detMulBase w ≤ detPosBase w :=
  le_trans (detMulBase_le_detInvBase w) (detInvBase_le_detPosBase w)

theorem detMulBase_le_detImgBase (w : ℕ) : detMulBase w ≤ detImgBase w :=
  le_trans (detMulBase_le_detPosBase w) (detPosBase_le_detImgBase w)

theorem detMulBase_le_detEnd (w : ℕ) : detMulBase w ≤ detEnd w :=
  le_trans (detMulBase_le_detImgBase w) (detImgBase_le_detEnd w)

theorem detMulBase_pair (w a c : ℕ) : detMulBase w ≤ detMulBase w + pairIdx w a c :=
  Nat.le_add_right _ _

/-! Child C1: `LinearSetReconciliation327.Main.pinsketch_syndrome_recovery`.

Generated by `p21opt/gen/emit.py` by skeleton subtraction from
`Solutions/_p21_opt3.lean` (Stage-2 declaration spans). -/

set_option autoImplicit false

open scoped ENNReal
open Finset Polynomial


section FieldFacts

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

/-- A field that is a `ZMod 2`-algebra has characteristic two. -/
theorem pinsketch_two_eq_zero : (2 : F) = 0 := by
  have h : ((2 : ℕ) : F) = 0 := by
    rw [← map_natCast (algebraMap (ZMod 2) F) 2, CharP.cast_eq_zero (ZMod 2) 2, map_zero]
  simpa using h

theorem pinsketch_charP : CharP F 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero pinsketch_two_eq_zero

/-- In characteristic two, `a + a = 0`. -/
theorem pinsketch_add_self (a : F) : a + a = 0 := by
  haveI := pinsketch_charP (F := F)
  exact CharTwo.add_self_eq_zero a

/-- In characteristic two, `a + b = 0` forces `a = b`. -/
theorem pinsketch_eq_of_add_eq_zero {a b : F} (h : a + b = 0) : a = b := by
  haveI := pinsketch_charP (F := F)
  exact CharTwo.add_eq_zero.mp h

/-- The freshman's dream: squaring is additive in characteristic two. -/
theorem pinsketch_sum_sq {α : Type} (s : Finset α) (f : α → F) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 := by
  haveI := pinsketch_charP (F := F)
  exact CharTwo.sum_sq s f

/-- `(n : F)` is `0` or `1` according to the parity of `n`, in characteristic two. -/
theorem pinsketch_natCast_eq_ite (n : ℕ) : (n : F) = if Even n then 0 else 1 := by
  haveI := pinsketch_charP (F := F)
  exact CharTwo.natCast_eq_ite n

/-- The only two elements of `ZMod 2`. -/
theorem zmod2_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  exact h z

/-- Scalar multiplication by a `ZMod 2`-element is either `0` or the identity. -/
theorem zmod2_smul_eq (z : ZMod 2) (v : F) : z • v = if z = 1 then v else 0 := by
  rcases zmod2_eq_zero_or_one z with h | h <;> simp [h]

end FieldFacts

section PowerSums

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

variable {N : ℕ}

/-- `P_a(x)` is the `a`-th power sum of the field elements indexed by the support. -/
theorem pinPower_eq_sum_supp (ι : ℕ → F) (a : ℕ) (x : Fin N → ZMod 2) :
    pinPower ι a x = ∑ i ∈ binSupp x, ι i.val ^ a := by
  rw [pinPower]
  calc ∑ i, x i • ι i.val ^ a
      = ∑ i, (if x i = 1 then ι i.val ^ a else 0) := by
        exact Finset.sum_congr rfl (fun i _ => zmod2_smul_eq (x i) _)
    _ = ∑ i ∈ univ.filter (fun i => x i = 1), ι i.val ^ a :=
        (Finset.sum_filter (s := univ) (p := fun i => x i = 1) (f := fun i => ι i.val ^ a)).symm

/-- The power sums are additive: the map `x ↦ P_a(x)` is `F₂`-linear. -/
theorem pinPower_add (ι : ℕ → F) (a : ℕ) (x y : Fin N → ZMod 2) :
    pinPower ι a (x + y) = pinPower ι a x + pinPower ι a y := by
  simp only [pinPower, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- **Frobenius**, as in the paper: in characteristic two, `P_{2a}(x) = P_a(x)^2`. -/
theorem pinPower_frobenius (ι : ℕ → F) (a : ℕ) (x : Fin N → ZMod 2) :
    pinPower ι (2 * a) x = (pinPower ι a x) ^ 2 := by
  rw [pinPower_eq_sum_supp, pinPower_eq_sum_supp]
  calc ∑ i ∈ binSupp x, ι i.val ^ (2 * a)
      = ∑ i ∈ binSupp x, (ι i.val ^ a) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Nat.mul_comm 2 a, pow_mul]
    _ = (∑ i ∈ binSupp x, ι i.val ^ a) ^ 2 := (pinsketch_sum_sq _ _).symm

/-- Two binary vectors with the same support of the sum: the support of `x + x'` is contained in
the union of the supports. -/
theorem binSupp_add_subset (x x' : Fin N → ZMod 2) :
    binSupp (x + x') ⊆ binSupp x ∪ binSupp x' := by
  intro i hi
  simp only [binSupp, mem_filter, mem_univ, true_and, mem_union] at hi ⊢
  rcases zmod2_eq_zero_or_one (x i) with hx | hx <;> rcases zmod2_eq_zero_or_one (x' i) with hy | hy
  · rw [Pi.add_apply, hx, hy] at hi; simp at hi
  · exact Or.inr hy
  · exact Or.inl hx
  · rw [Pi.add_apply, hx, hy] at hi; simp at hi

end PowerSums

section Enc

variable {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}

end Enc

section Tables

variable {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}

end Tables

section ReadInt

end ReadInt

section ReadLoop

end ReadLoop

section ProgramAt

end ProgramAt

section ReadSpec

end ReadSpec

section ReadStmt

end ReadStmt

section Bounds

end Bounds

section Prologue

end Prologue

section ReadAssembly

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end ReadAssembly

section Expand

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end Expand

section ExpandStd

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end ExpandStd

section PinBits

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end PinBits

section Uniqueness

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

/-- **Vandermonde lemma.** `m` distinct nonzero field elements cannot have `m` consecutive
vanishing power sums starting at `s`: the Vandermonde matrix of the family is invertible, so the
vector of all ones would be zero. -/
theorem vandermonde_window {α : Type} [Fintype α]
    (v : α → F) (hinj : Function.Injective v) (hne : ∀ i, v i ≠ 0) (s : ℕ)
    (h : ∀ j : Fin (Fintype.card α), ∑ i : α, v i ^ (s + j.val) = 0) :
    Fintype.card α = 0 := by
  classical
  by_contra hcard
  have hpos : 0 < Fintype.card α := Nat.pos_of_ne_zero hcard
  let v' : Fin (Fintype.card α) → F := fun k => v ((Fintype.equivFin α).symm k)
  have hinj' : Function.Injective v' := by
    intro a b hab
    exact (Fintype.equivFin α).symm.injective (hinj hab)
  have hne' : ∀ k : Fin (Fintype.card α), v' k ≠ 0 := fun k => hne _
  have h' : ∀ j : Fin (Fintype.card α),
      ∑ k : Fin (Fintype.card α), v' k ^ (s + j.val) = 0 := by
    intro j
    have hsumeq := Fintype.sum_equiv (Fintype.equivFin α)
      (fun i : α => v i ^ (s + j.val)) (fun k : Fin (Fintype.card α) => v' k ^ (s + j.val))
      (fun i => by simp [v'])
    rw [← hsumeq]
    exact h j
  -- the vector of `s`-th powers and its Vandermonde image
  let c : Fin (Fintype.card α) → F := fun k => v' k ^ s
  have hker : Matrix.mulVec (Matrix.transpose (Matrix.vandermonde v')) c = 0 := by
    funext j
    simp only [Pi.zero_apply]
    have h0 := h' j
    have hthis : Matrix.mulVec (Matrix.transpose (Matrix.vandermonde v')) c j
        = ∑ k : Fin (Fintype.card α), v' k ^ (s + j.val) := by
      rw [Matrix.mulVec_apply_eq_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Matrix.transpose_apply, Matrix.vandermonde_apply]
      show v' k ^ (j : ℕ) * v' k ^ s = v' k ^ (s + j.val)
      rw [← pow_add, Nat.add_comm]
    rw [hthis, h0]
  have hdet : (Matrix.transpose (Matrix.vandermonde v')).det ≠ 0 := by
    rw [Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
    exact hinj'
  have hc : c = 0 :=
    Matrix.mulVec_injective_of_det_ne_zero hdet (by rw [hker, Matrix.mulVec_zero])
  have hlast : v' ⟨0, hpos⟩ ^ s = 0 := by
    have := congrFun hc ⟨0, hpos⟩
    simpa [c] using this
  exact (pow_ne_zero s (hne' ⟨0, hpos⟩)) hlast

end Uniqueness

section Slp

variable {F : Type} [Field F]

end Slp


open LinearSetReconciliation327.Main in
theorem LinearSetReconciliation327.Main.pinsketch_syndrome_recovery
    {F : Type} [Field F] [Algebra (ZMod 2) F] {N t : ℕ} (ι : ℕ → F)
    (h0 : ∀ v < N, ι v ≠ 0) (hinj : Set.InjOn ι (Set.Iio N)) {x x' : Fin N → ZMod 2}
    (hx : (univ.filter fun i => x i = 1).card ≤ t)
    (hx' : (univ.filter fun i => x' i = 1).card ≤ t)
    (hp : pin ι t x = pin ι t x') : x = x' := by
  classical
  set y : Fin N → ZMod 2 := x + x' with hy
  -- the weight of the difference is at most `2t`
  have hm2 : (binSupp y).card ≤ 2 * t := by
    calc (binSupp y).card ≤ (binSupp x ∪ binSupp x').card :=
          Finset.card_le_card (binSupp_add_subset x x')
      _ ≤ (binSupp x).card + (binSupp x').card := Finset.card_union_le _ _
      _ ≤ t + t := Nat.add_le_add hx hx'
      _ = 2 * t := by omega
  -- the odd power sums vanish
  have hodd : ∀ j : Fin t, pinPower ι (2 * j.val + 1) y = 0 := by
    intro j
    have hpj : pinPower ι (2 * j.val + 1) x = pinPower ι (2 * j.val + 1) x' := by
      have h1 := congrFun hp j
      simpa [pin] using h1
    rw [hy, pinPower_add, hpj, pinsketch_add_self]
  -- Frobenius upgrades this to all power sums up to `2t - 1`
  have hP : ∀ a, 1 ≤ a → a ≤ 2 * t - 1 → pinPower ι a y = 0 := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro ha1 ha2
      rcases Nat.even_or_odd a with he | ho
      · obtain ⟨k, rfl⟩ := he
        have hkpos : 0 < k := by omega
        have hklt : k < k + k := by omega
        have hk1 : 1 ≤ k := hkpos
        have hk2 : k ≤ 2 * t - 1 := by omega
        have hstep : pinPower ι (k + k) y = (pinPower ι k y) ^ 2 := by
          rw [show k + k = 2 * k by omega, pinPower_frobenius]
        rw [hstep, ih k hklt hk1 hk2]
        simp
      · obtain ⟨k, rfl⟩ := ho
        have hkt : k < t := by omega
        exact hodd ⟨k, hkt⟩
  -- the window of `|supp y|` consecutive power sums that vanishes
  have hm0 : (binSupp y).card = 0 := by
    have hcard : Fintype.card {i : Fin N // i ∈ binSupp y} = (binSupp y).card := by
      simp
    have hz : Fintype.card {i : Fin N // i ∈ binSupp y} = 0 := by
      refine vandermonde_window (α := {i : Fin N // i ∈ binSupp y})
        (v := fun i => ι (i : Fin N).val) ?_ ?_
        (if Even (binSupp y).card then 0 else 1) ?_
      · intro a b hab
        exact Subtype.ext (Fin.ext (hinj a.1.isLt b.1.isLt hab))
      · intro i
        exact h0 i.1.val i.1.isLt
      · intro j
        have hjlt : j.val < (binSupp y).card := by
          rw [← hcard]
          exact j.isLt
        have h1 : pinPower ι ((if Even (binSupp y).card then 0 else 1) + j.val) y = 0 := by
          by_cases hme : Even (binSupp y).card
          · rw [if_pos hme, Nat.zero_add]
            by_cases hj0 : j.val = 0
            · rw [hj0, pinPower_eq_sum_supp]
              simp only [pow_zero]
              rw [Finset.sum_const, nsmul_eq_mul, mul_one, pinsketch_natCast_eq_ite, if_pos hme]
            · have ha1 : 1 ≤ j.val := Nat.pos_of_ne_zero hj0
              have ha2 : j.val ≤ 2 * t - 1 := by omega
              exact hP j.val ha1 ha2
          · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hme
            rw [if_neg hme]
            have ha1 : 1 ≤ 1 + j.val := by omega
            have ha2 : 1 + j.val ≤ 2 * t - 1 := by omega
            exact hP (1 + j.val) ha1 ha2
        rw [pinPower_eq_sum_supp] at h1
        exact (Finset.sum_coe_sort (binSupp y)
          (fun i : Fin N => ι i.val ^ ((if Even (binSupp y).card then 0 else 1) + j.val))).trans h1
    rw [hcard] at hz
    exact hz
  -- hence the difference vanishes
  have hempty : binSupp y = ∅ := Finset.card_eq_zero.mp hm0
  have hy0 : y = 0 := by
    funext i
    have hi : i ∉ binSupp y := by rw [hempty]; simp
    simp only [binSupp, mem_filter, mem_univ, true_and, not_not] at hi
    rcases zmod2_eq_zero_or_one (y i) with h | h
    · exact h
    · exact absurd h hi
  funext i
  have hxy : x i + x' i = 0 := by
    have h1 := congrFun hy0 i
    simpa [hy, Pi.add_apply] using h1
  exact pinsketch_eq_of_add_eq_zero hxy

/-! Child C2: `LinearSetReconciliation327.Main.pinsketch_decoder_read`.

Generated by `p21opt/gen/emit.py` by skeleton subtraction from
`Solutions/_p21_opt3.lean` (Stage-2 declaration spans). -/

set_option autoImplicit false

open scoped ENNReal
open Finset Polynomial


attribute [local simp] readState expandState

section FieldFacts

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end FieldFacts

section PowerSums

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

variable {N : ℕ}

end PowerSums

/-- Packing a `Fin K`-indexed family is the same as the sum of shifted fields. -/
theorem packL_ofFn (w K : ℕ) (f : Fin K → ℕ) :
    packL w (List.ofFn f) = ∑ j : Fin K, f j * 2 ^ (j.val * w) := by
  induction K with
  | zero => simp [packL]
  | succ n ih =>
      rw [List.ofFn_succ, Fin.sum_univ_succ]
      simp only [packL, Fin.val_zero, Nat.zero_mul, Nat.pow_zero, Nat.mul_one, Fin.val_succ]
      rw [ih (fun i => f i.succ), Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have h2 : 2 ^ ((j.val + 1) * w) = 2 ^ w * 2 ^ (j.val * w) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.pow_add, Nat.mul_comm]
      rw [h2]
      ring

/-- Extracting the `k`-th `w`-bit field, in division form. -/
theorem extract_field_div (w : ℕ) (_hw : 0 < w) (l : List ℕ) (hx : ∀ x ∈ l, x < 2 ^ w)
    (k : ℕ) : packL w l / 2 ^ (k * w) % 2 ^ w = l.getD k 0 := by
  induction k generalizing l with
  | zero =>
      cases l with
      | nil => simp [packL]
      | cons x xs =>
          have hx' : x < 2 ^ w := hx x (by simp)
          simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one, packL, List.getD_cons_zero]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx']
  | succ k ih =>
      cases l with
      | nil => simp [packL]
      | cons x xs =>
          have hx' : x < 2 ^ w := hx x (by simp)
          have hpw : 0 < 2 ^ w := Nat.two_pow_pos w
          have hsplit : 2 ^ ((k + 1) * w) = 2 ^ w * 2 ^ (k * w) := by
            rw [Nat.add_mul, Nat.one_mul, Nat.pow_add, Nat.mul_comm]
          have hlow : (x + 2 ^ w * packL w xs) / 2 ^ w = packL w xs := by
            rw [Nat.add_comm x (2 ^ w * packL w xs), Nat.mul_add_div hpw,
              Nat.div_eq_of_lt hx', Nat.add_zero]
          simp only [packL, List.getD_cons_succ, hsplit, ← Nat.div_div_eq_div_mul, hlow]
          exact ih xs (fun y hy => hx y (by simp [hy]))

/-- The `k`-th `w`-bit field of a packed word, extracted with `>>>` and `&&&`. -/
theorem extract_field (w : ℕ) (hw : 0 < w) (l : List ℕ) (hx : ∀ x ∈ l, x < 2 ^ w) (k : ℕ) :
    (packL w l >>> (k * w)) &&& (2 ^ w - 1) = l.getD k 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  exact extract_field_div w hw l hx k

/-- Field extraction in the form used by the sketches: a word whose `j`-th `w`-bit field is
`f j` yields `f k` by shifting and masking. -/
theorem extract_field_sum (w K : ℕ) (hw : 0 < w) (f : Fin K → ℕ) (hf : ∀ j, f j < 2 ^ w)
    (k : Fin K) :
    ((∑ j : Fin K, f j * 2 ^ (j.val * w)) >>> (k.val * w)) &&& (2 ^ w - 1) = f k := by
  rw [← packL_ofFn w K f]
  rw [extract_field w hw (List.ofFn f) ?_ k.val]
  · have hk : k.val < (List.ofFn f).length := by simp only [List.length_ofFn]; exact k.isLt
    rw [List.getD_eq_getElem (List.ofFn f) 0 hk]
    simp [List.getElem_ofFn]
  · intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact hf j

theorem payloadBit_lt_two {M : ℕ} (y : Fin M → ZMod 2) (p : ℕ) : payloadBit y p < 2 :=
  ZMod.val_lt _

theorem payloadBit_le_one {M : ℕ} (y : Fin M → ZMod 2) (p : ℕ) : payloadBit y p ≤ 1 := by
  have h := payloadBit_lt_two y p
  omega

/-- In `ZMod 2` the value of an element is `1` exactly at `1`. -/
theorem zmod2_val (z : ZMod 2) : z.val = if z = 1 then 1 else 0 := by
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h z with h | h
  · rw [h]; decide
  · rw [h]; decide

/-- Adding one payload bit at the end only changes the bit at position `M`. -/
theorem payloadBit_succ {M : ℕ} (y : Fin (M + 1) → ZMod 2) (p : ℕ) :
    payloadBit y p =
      payloadBit (fun i : Fin M => y i.castSucc) p +
        (if p = M then (if y (Fin.last M) = 1 then 1 else 0) else 0) := by
  have hlast : (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1)) = Fin.last M := Fin.ext rfl
  unfold payloadBit payloadAt
  by_cases h : p < M
  · rw [dif_pos h, dif_pos (Nat.lt_succ_of_lt h), if_neg (by omega)]
    simp
  · by_cases h2 : p = M
    · rw [h2, dif_pos (Nat.lt_succ_self M), if_pos rfl, hlast]
      simp [zmod2_val]
    · rw [dif_neg (by omega : ¬ p < M + 1), dif_neg (by omega : ¬ p < M), if_neg h2]
      simp

/-- Peeling the last payload bit off the word that holds it. -/
theorem packMem_succ {W M : ℕ} (y : Fin (M + 1) → ZMod 2) (addr : ℕ) :
    packMem W y addr =
      packMem W (fun i : Fin M => y i.castSucc) addr +
        (if M / W = addr ∧ y (Fin.last M) = 1 then 2 ^ (M % W) else 0) := by
  have hsplit := Fin.sum_univ_castSucc
    (f := fun p : Fin (M + 1) =>
      (if p.val / W = addr ∧ y p = 1 then 2 ^ (p.val % W) else 0))
  simp only [packMem]
  rw [hsplit]
  simp only [Fin.val_castSucc, Fin.val_last]

/-- The bit position inside a word determines the word index. -/
theorem div_eq_of_mul_add {W M c b : ℕ} (hW : 0 < W) (hb : b < W) (h : c * W + b = M) :
    M / W = c := by
  rw [← h, Nat.mul_comm c W, Nat.mul_add_div hW, Nat.div_eq_of_lt hb, Nat.add_zero]

/-- The word `addr` contributes to exactly one bit position, namely `M % W` when `M / W = addr`. -/
theorem sum_range_ite_bit {W M addr v : ℕ} (hW : 0 < W) :
    (∑ b ∈ Finset.range W, (if addr * W + b = M then v else 0) * 2 ^ b)
      = if M / W = addr then v * 2 ^ (M % W) else 0 := by
  by_cases h : M / W = addr
  · have hsingle : addr * W + M % W = M := by
      have h0 := Nat.div_add_mod M W
      rw [h] at h0
      rw [Nat.mul_comm W addr] at h0
      exact h0
    rw [if_pos h,
      Finset.sum_eq_single (M % W)
        (fun b _ hne => by
          rw [if_neg (by intro he; exact hne (by omega))]
          simp)
        (fun hmem => absurd (Finset.mem_range.mpr (Nat.mod_lt M hW)) hmem),
      if_pos hsingle]
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun b hb => ?_)
    rw [Finset.mem_range] at hb
    rw [if_neg (by intro he; exact h (div_eq_of_mul_add hW hb he))]
    simp

/-- **The packed-word layout**: a packed word is the sum of its payload bits, weighted by
position.  This is `packMem` seen bit by bit. -/
theorem packMem_eq_sum_bits {W : ℕ} (hW : 0 < W) :
    ∀ (M : ℕ) (y : Fin M → ZMod 2) (addr : ℕ),
      packMem W y addr = ∑ b ∈ Finset.range W, payloadBit y (addr * W + b) * 2 ^ b := by
  intro M
  induction M with
  | zero => intro y addr; simp [packMem, payloadBit, payloadAt]
  | succ M ih =>
      intro y addr
      have hstep :
          (∑ b ∈ Finset.range W, payloadBit y (addr * W + b) * 2 ^ b)
            = (∑ b ∈ Finset.range W,
                payloadBit (fun i : Fin M => y i.castSucc) (addr * W + b) * 2 ^ b)
              + (if M / W = addr ∧ y (Fin.last M) = 1 then 2 ^ (M % W) else 0) := by
        have hpt : ∀ b ∈ Finset.range W,
            payloadBit y (addr * W + b) * 2 ^ b
              = payloadBit (fun i : Fin M => y i.castSucc) (addr * W + b) * 2 ^ b
                + (if addr * W + b = M then (if y (Fin.last M) = 1 then 1 else 0) else 0)
                    * 2 ^ b := by
          intro b _
          rw [payloadBit_succ, Nat.add_mul]
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, sum_range_ite_bit hW]
        congr 1
        by_cases h1 : M / W = addr <;> by_cases h2 : y (Fin.last M) = 1 <;> simp [h1, h2]
      rw [packMem_succ y addr, ih (fun i : Fin M => y i.castSucc) addr, hstep]

theorem sum_range_two_pow_lt (w : ℕ) : (∑ k ∈ Finset.range w, 2 ^ k) < 2 ^ w := by
  induction w with
  | zero => simp
  | succ w ih =>
      rw [Finset.sum_range_succ, Nat.pow_succ]
      omega

/-- A `w`-bit field built from payload bits is a `w`-bit number. -/
theorem bits_sum_lt_two_pow {w M : ℕ} (y : Fin M → ZMod 2) (c : ℕ) :
    (∑ k ∈ Finset.range w, payloadBit y (c + k) * 2 ^ k) < 2 ^ w := by
  have h1 : (∑ k ∈ Finset.range w, payloadBit y (c + k) * 2 ^ k)
      ≤ ∑ k ∈ Finset.range w, 2 ^ k := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    calc payloadBit y (c + k) * 2 ^ k ≤ 1 * 2 ^ k :=
          Nat.mul_le_mul_right _ (payloadBit_le_one y (c + k))
      _ = 2 ^ k := Nat.one_mul _
  exact lt_of_le_of_lt h1 (sum_range_two_pow_lt w)

/-- Splitting the bits of `n` words of `w` bits into `n` fields of `w` bits. -/
theorem sum_range_bits_split (w n : ℕ) (f : ℕ → ℕ) :
    (∑ b ∈ Finset.range (n * w), f b * 2 ^ b)
      = ∑ i ∈ Finset.range n,
          (∑ k ∈ Finset.range w, f (i * w + k) * 2 ^ k) * 2 ^ (i * w) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Nat.pow_add]
      ring

/-- The coordinates of `payloadField` are the payload bits. -/
theorem payloadField_apply {F : Type} [Field F] [Algebra (ZMod 2) F] {w M : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin M → ZMod 2) (j : ℕ) (k : Fin w) :
    b.repr (payloadField b y j) k = payloadAt y (j * w + k.val) := by
  rw [payloadField, LinearEquiv.apply_symm_apply]
  simp only [Finsupp.coe_equivFunOnFinite_symm]

@[simp] theorem execInstr_imm (E : RAMEnv) (s : RAMState) (d : Fin 16) (v : ℕ) :
    execInstr (.imm d v) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (v % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_add (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.add d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) + (s.regs b)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_mul (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.mul d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) * (s.regs b)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_div (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.div d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) / (s.regs b)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_mod (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.mod d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) % (s.regs b)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_band (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.band d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) &&& (s.regs b)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_shr (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.shr d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) / 2 ^ (s.regs b)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_lt (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.lt d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((if (s.regs a) < (s.regs b) then 1 else 0) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_load (E : RAMEnv) (s : RAMState) (d a : Fin 16) :
    execInstr (.load d a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((s.mem (s.regs a)) % 2 ^ E.W) } := rfl

@[simp] theorem execInstr_store (E : RAMEnv) (s : RAMState) (a v : Fin 16) :
    execInstr (.store a v) E s = { s with pc := s.pc + 1, mem := Function.update s.mem (s.regs a) (s.regs v) } := rfl

@[simp] theorem execInstr_jz (E : RAMEnv) (s : RAMState) (c : Fin 16) (t : ℕ) :
    execInstr (.jz c t) E s = { s with pc := if (s.regs c) = 0 then t else s.pc + 1 } := rfl

@[simp] theorem execInstr_jmp (E : RAMEnv) (s : RAMState) (t : ℕ) :
    execInstr (.jmp t) E s = { s with pc := t } := rfl

@[simp] theorem execInstr_qDet (E : RAMEnv) (s : RAMState) (d a : Fin 16) :
    execInstr (.qDet d a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((E.det (s.regs a)) % 2 ^ E.W) } := rfl

/-- `step` runs the branch of `execInstr` at the current program counter. -/
theorem step_eq_execInstr (P : Program) (E : RAMEnv) (s : RAMState) (i : Instr)
    (h : P[s.pc]? = some i) : step P E s = execInstr i E s := by
  unfold step execInstr
  rw [h]
  cases i <;> rfl

/-- Two machine states with the same program counter, memory and registers are equal. -/
theorem ramState_eq_of (a b : RAMState) (hpc : a.pc = b.pc) (hmem : a.mem = b.mem)
    (hregs : ∀ d, a.regs d = b.regs d) : a = b := by
  obtain ⟨p1, r1', m1⟩ := a
  obtain ⟨p2, r2', m2⟩ := b
  simp only at hpc hmem hregs
  subst hpc
  subst hmem
  rw [funext hregs]

/-- A non-branching, non-halting instruction advances the program counter by one. -/
theorem execInstr_pc (i : Instr) (E : RAMEnv) (s : RAMState) (hno : i.NoBranchI) :
    (execInstr i E s).pc = s.pc + 1 := by
  obtain ⟨h1, h2, h3⟩ := hno
  cases i <;> simp_all [execInstr]

@[simp] theorem noBranch_nil : NoBranch ([] : List Instr) ↔ True := by simp [NoBranch]

@[simp] theorem noBranch_cons (i : Instr) (c : List Instr) :
    NoBranch (i :: c) ↔ i.NoBranchI ∧ NoBranch c := by simp [NoBranch]

@[simp] theorem noBranchI_imm (d : Fin 16) (v : ℕ) : (iImm d v).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_add (d a b : Fin 16) : (iAdd d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_mul (d a b : Fin 16) : (iMul d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_div (d a b : Fin 16) : (iDiv d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_mod (d a b : Fin 16) : (iMod d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_band (d a b : Fin 16) : (iBand d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_shr (d a b : Fin 16) : (iShr d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_lt (d a b : Fin 16) : (iLt d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_load (d a : Fin 16) : (iLd d a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_store (a v : Fin 16) : (iSt a v).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_qDet (d a : Fin 16) : (iTbl d a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem runBlock_nil (E : RAMEnv) (s : RAMState) : runBlock [] E s = s := rfl

@[simp] theorem runBlock_cons (i : Instr) (code : List Instr) (E : RAMEnv) (s : RAMState) :
    runBlock (i :: code) E s = runBlock code E (execInstr i E s) := by
  simp [runBlock, List.foldl_cons]

/-- Concatenation of straight-line blocks. -/
theorem runBlock_append (c₁ c₂ : List Instr) (E : RAMEnv) (s : RAMState) :
    runBlock (c₁ ++ c₂) E s = runBlock c₂ E (runBlock c₁ E s) := by
  simp [runBlock, List.foldl_append]

/-- A straight-line block advances the program counter by its length. -/
theorem runBlock_pc (code : List Instr) (E : RAMEnv) (s : RAMState) (hno : NoBranch code) :
    (runBlock code E s).pc = s.pc + code.length := by
  induction code generalizing s with
  | nil => simp
  | cons i tl ih =>
      obtain ⟨hi, ht⟩ := hno
      rw [runBlock_cons, ih (s := execInstr i E s) ht, execInstr_pc i E s hi]
      simp only [List.length_cons]
      omega

/-- Front peeling of iterates: the first step is applied first. -/
theorem iterate_succ_apply_front {α : Type} (f : α → α) (n : ℕ) (x : α) :
    f^[n + 1] x = (f^[n]) (f x) := by
  rw [Function.iterate_add_apply]
  rfl

theorem At.cons {P : Program} {a : ℕ} {i : Instr} {l : List Instr} :
    At P a (i :: l) ↔ P[a]? = some i ∧ At P (a + 1) l := by
  constructor
  · intro h
    refine ⟨?_, fun r hr => ?_⟩
    · have h0 := h 0 (by simp)
      simpa using h0
    · have h1 := h (r + 1) (by simpa using hr)
      rw [show a + (r + 1) = a + 1 + r from by omega] at h1
      simpa using h1
  · rintro ⟨h1, h2⟩ r hr
    cases r with
    | zero => simpa using h1
    | succ r =>
        have h3 := h2 r (by simpa using hr)
        rw [show a + (r + 1) = a + 1 + r from by omega]
        simpa using h3

@[simp] theorem At.nil {P : Program} {a : ℕ} : At P a ([] : List Instr) ↔ True := by
  unfold At
  simp

theorem At.append {P : Program} {a : ℕ} {l₁ l₂ : List Instr} :
    At P a (l₁ ++ l₂) ↔ At P a l₁ ∧ At P (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · have h' := h r (by simp only [List.length_append]; omega)
      rwa [List.getElem?_append_left hr] at h'
    · have h' := h (l₁.length + r) (by simp only [List.length_append]; omega)
      rw [List.getElem?_append_right (by omega : l₁.length ≤ l₁.length + r)] at h'
      rw [show l₁.length + r - l₁.length = r from by omega] at h'
      rwa [show a + (l₁.length + r) = a + l₁.length + r from by omega] at h'
  · intro ⟨h₁, h₂⟩ r hr
    by_cases hlt : r < l₁.length
    · rw [List.getElem?_append_left hlt]
      exact h₁ r hlt
    · rw [List.getElem?_append_right (by omega : l₁.length ≤ r)]
      have hlen : (l₁ ++ l₂).length = l₁.length + l₂.length := List.length_append ..
      rw [hlen] at hr
      have h := h₂ (r - l₁.length) (by omega)
      rwa [show a + l₁.length + (r - l₁.length) = a + r from by omega] at h

/-- A block found by `At` runs exactly as `runBlock` says. -/
theorem iterate_runBlock_of_at (P : Program) (E : RAMEnv) :
    ∀ (l : List Instr) (s : RAMState), At P s.pc l → NoBranch l →
      (step P E)^[l.length] s = runBlock l E s
  | [], s, _, _ => by simp
  | i :: tl, s, ha, hno => by
      obtain ⟨hi, ht⟩ := hno
      have hg : P[s.pc]? = some i := by
        have h := ha 0 (by simp)
        simpa using h
      have hstep : step P E s = execInstr i E s := step_eq_execInstr P E s i hg
      have hpc : (execInstr i E s).pc = s.pc + 1 := execInstr_pc i E s hi
      have ha' : At P (execInstr i E s).pc tl := by
        intro r hr
        rw [hpc]
        have h := ha (r + 1) (by simpa using hr)
        rw [show s.pc + (r + 1) = s.pc + 1 + r from by omega] at h
        simpa using h
      rw [List.length_cons, iterate_succ_apply_front, hstep, runBlock_cons]
      exact iterate_runBlock_of_at P E tl (execInstr i E s) ha' ht

theorem Cond.noBranch_code (c : Cond) : NoBranch c.code := by
  cases c with
  | neqz r => simp [Cond.code]
  | lt d a b => simp [Cond.code]

/-- A test holds exactly when its test register, after the test code, is nonzero. -/
theorem Cond.eval_iff (c : Cond) (E : RAMEnv) (s : RAMState) (hW : 1 < 2 ^ E.W) :
    c.eval s ↔ (runBlock c.code E s).regs c.test ≠ 0 := by
  cases c with
  | neqz r => simp [Cond.eval, Cond.code, Cond.test]
  | lt d a b =>
      have hcode : Cond.code (Cond.lt d a b) = [iLt d a b] := rfl
      have htest : Cond.test (Cond.lt d a b) = d := rfl
      have hrun : (runBlock (Cond.code (Cond.lt d a b)) E s).regs (Cond.test (Cond.lt d a b))
          = (if s.regs a < s.regs b then 1 else 0) % 2 ^ E.W := by
        rw [hcode, htest, runBlock_cons, runBlock_nil, execInstr_lt]
        simp
      rw [hrun]
      by_cases h : s.regs a < s.regs b
      · rw [if_pos h, Nat.mod_eq_of_lt hW]
        exact ⟨fun _ => one_ne_zero, fun _ => h⟩
      · rw [if_neg h]
        exact ⟨fun hc => absurd hc h, fun hc => absurd hc (by simp)⟩

theorem Stmt.length_compile (s : Stmt) (base : ℕ) : (s.compile base).length = s.len := by
  induction s generalizing base with
  | code l => rfl
  | seq a b iha ihb =>
      simp only [Stmt.compile, Stmt.len, iha, ihb, List.length_append] <;> omega
  | ite c a b iha ihb =>
      simp only [Stmt.compile, Stmt.len, iha, ihb, List.length_append, List.length_singleton,
        List.length_cons, List.length_nil] <;> omega
  | loop c b ih =>
      simp only [Stmt.compile, Stmt.len, ih, List.length_append, List.length_singleton,
        List.length_cons, List.length_nil] <;> omega

theorem at_loop {P : Program} {a : ℕ} {c : Cond} {b : Stmt}
    (h : At P a (Stmt.compile (Stmt.loop c b) a)) :
    At P a c.code ∧ P[a + c.code.length]? = some (iJz c.test (a + c.code.length + b.len + 2)) ∧
      At P (a + c.code.length + 1) (b.compile (a + c.code.length + 1)) ∧
      P[a + c.code.length + 1 + b.len]? = some (iJmp a) := by
  simpa [Stmt.compile, Stmt.length_compile, At.append, At.cons, At.nil] using h

/-- A block runs exactly as `runBlock` says. -/
theorem Sem.block (P : Program) (E : RAMEnv) (a : ℕ) (l : List Instr) (s : RAMState)
    (hAt : At P a l) (hno : NoBranch l) (hpc : s.pc = a) :
    Sem P E a (a + l.length) s (fun k s' => k = l.length ∧ s' = runBlock l E s) := by
  refine ⟨hpc, l.length, runBlock l E s, ?_, ?_, rfl, rfl⟩
  · exact iterate_runBlock_of_at P E l s (hpc.symm ▸ hAt) hno
  · rw [runBlock_pc l E s hno, hpc]

/-- One instruction. -/
theorem Sem.exec (P : Program) (E : RAMEnv) (a b : ℕ) (s : RAMState) (i : Instr)
    (hAt : P[a]? = some i) (hpc : s.pc = a) (hb : (execInstr i E s).pc = b) :
    Sem P E a b s (fun k s' => k = 1 ∧ s' = execInstr i E s) := by
  refine ⟨hpc, 1, execInstr i E s, ?_, hb, rfl, rfl⟩
  rw [Function.iterate_one, step_eq_execInstr P E s i (by rwa [← hpc] at hAt)]

/-- Weakening the postcondition. -/
theorem Sem.mono {P : Program} {E : RAMEnv} {a b : ℕ} {s : RAMState}
    {Q Q' : ℕ → RAMState → Prop} (h : Sem P E a b s Q) (hQ : ∀ k s', Q k s' → Q' k s') :
    Sem P E a b s Q' := by
  obtain ⟨hpc, k, s', hstep, hb, hQ'⟩ := h
  exact ⟨hpc, k, s', hstep, hb, hQ k s' hQ'⟩

/-- A `jz` whose test register is zero takes its target, in one step. -/
theorem Sem.jz_taken (P : Program) (E : RAMEnv) (a t : ℕ) (c : Cond) (s : RAMState)
    (hAt : P[a]? = some (iJz c.test t)) (hpc : s.pc = a) (h0 : s.regs c.test = 0) :
    Sem P E a t s (fun k s' => k = 1 ∧ s' = { s with pc := t }) := by
  refine Sem.mono (Sem.exec P E a t s (iJz c.test t) hAt hpc ?_) ?_
  · simp [execInstr_jz, h0]
  · intro k s' h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [execInstr_jz, h0]⟩

/-- A `jz` whose test register is nonzero falls through, in one step. -/
theorem Sem.jz_next (P : Program) (E : RAMEnv) (a t : ℕ) (c : Cond) (s : RAMState)
    (hAt : P[a]? = some (iJz c.test t)) (hpc : s.pc = a) (h0 : s.regs c.test ≠ 0) :
    Sem P E a (a + 1) s (fun k s' => k = 1 ∧ s' = { s with pc := a + 1 }) := by
  refine Sem.mono (Sem.exec P E a (a + 1) s (iJz c.test t) hAt hpc ?_) ?_
  · simp [execInstr_jz, h0, hpc]
  · intro k s' h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [execInstr_jz, h0, hpc]⟩

/-- Two exact runs glue, and the costs add. -/
theorem Sem.trans {P : Program} {E : RAMEnv} {a b c : ℕ} {s : RAMState} {n₁ n₂ : ℕ}
    {s₁ s₂ : RAMState}
    (h₁ : Sem P E a b s (fun k s' => k = n₁ ∧ s' = s₁))
    (h₂ : Sem P E b c s₁ (fun k s' => k = n₂ ∧ s' = s₂)) :
    Sem P E a c s (fun k s' => k = n₁ + n₂ ∧ s' = s₂) := by
  obtain ⟨hpc, k₁, t₁, hs₁, -, hk₁, ht₁⟩ := h₁
  obtain ⟨-, k₂, t₂, hs₂, hc, hk₂, ht₂⟩ := h₂
  refine ⟨hpc, k₁ + k₂, s₂, ?_, ?_, by omega, rfl⟩
  · rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, hs₁, ht₁, hs₂, ht₂]
  · rw [← ht₂]
    exact hc

/-- Sequential composition: the second run may depend on the cost and the state of the first. -/
theorem Sem.seq {P : Program} {E : RAMEnv} {a b c : ℕ} {s : RAMState}
    {Q₁ : ℕ → RAMState → Prop} {Q₂ : ℕ → ℕ → RAMState → Prop}
    (h₁ : Sem P E a b s Q₁)
    (h₂ : ∀ (k₁ : ℕ) (s₁ : RAMState), Q₁ k₁ s₁ → Sem P E b c s₁ (Q₂ k₁)) :
    Sem P E a c s (fun k s' => ∃ k₁ k₂, k = k₁ + k₂ ∧ Q₂ k₁ k₂ s') := by
  obtain ⟨hpc, k₁, s₁, hs₁, -, hQ₁⟩ := h₁
  obtain ⟨-, k₂, s₂, hs₂, hc, hQ₂⟩ := h₂ k₁ s₁ hQ₁
  refine ⟨hpc, k₁ + k₂, s₂, ?_, hc, k₁, k₂, rfl, hQ₂⟩
  rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, hs₁, hs₂]

/-- Append a `jmp`: the postcondition sees the state with its program counter already moved. -/
theorem Sem.jmp_append {P : Program} {E : RAMEnv} {a b c : ℕ} {s : RAMState}
    {Q : ℕ → RAMState → Prop} (hAt : P[b]? = some (iJmp c))
    (h : Sem P E a b s (fun t s' => Q (t + 1) { s' with pc := c })) :
    Sem P E a c s Q := by
  obtain ⟨hpc, k, s', hstep, hpb, hQ⟩ := h
  have hstep' : (step P E)^[k + 1] s = { s' with pc := c } := by
    rw [show k + 1 = 1 + k from by omega, Function.iterate_add_apply, Function.iterate_one, hstep,
      step_eq_execInstr P E s' (iJmp c) (by rw [hpb]; exact hAt), execInstr_jmp]
  exact ⟨hpc, k + 1, { s' with pc := c }, hstep', rfl, hQ⟩

/-- Leaving the loop: the test fails, the `jz` fires, control lands past the statement. -/
theorem Sem.loopExit (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt) (s : RAMState)
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W) (hpc : s.pc = a)
    (hstop : ¬ c.eval s) :
    Sem P E a (a + c.code.length + b.len + 2) s
      (fun k s' => k = c.code.length + 1 ∧
        s' = { runBlock c.code E s with pc := a + c.code.length + b.len + 2 }) := by
  obtain ⟨hcode, hjz, -, -⟩ := at_loop hAt
  have htest : Sem P E a (a + c.code.length) s
      (fun k s' => k = c.code.length ∧ s' = runBlock c.code E s) :=
    Sem.block P E a c.code s hcode (Cond.noBranch_code c) hpc
  have hpcT : (runBlock c.code E s).pc = a + c.code.length := by
    rw [runBlock_pc c.code E s (Cond.noBranch_code c), hpc]
  have h0 : (runBlock c.code E s).regs c.test = 0 := by
    by_contra hne
    exact hstop ((Cond.eval_iff c E s hW).mpr hne)
  exact Sem.trans htest
    (Sem.jz_taken P E (a + c.code.length) (a + c.code.length + b.len + 2) c _ hjz hpcT h0)

/-- One iteration that returns to the head: the test holds, the `jz` falls through, the body runs
from the body entry back to the loop head. -/
theorem Sem.loopStep (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt)
    (s s' : RAMState) (cost : ℕ) (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W)
    (hpc : s.pc = a) (hgo : c.eval s)
    (hbody : Sem P E (a + c.code.length + 1) a { runBlock c.code E s with pc := a + c.code.length + 1 }
      (fun k s'' => k = cost ∧ s'' = s')) :
    Sem P E a a s (fun k s'' => k = (c.code.length + 1) + cost ∧ s'' = s') := by
  obtain ⟨hcode, hjz, -, -⟩ := at_loop hAt
  have htest : Sem P E a (a + c.code.length) s
      (fun k s' => k = c.code.length ∧ s' = runBlock c.code E s) :=
    Sem.block P E a c.code s hcode (Cond.noBranch_code c) hpc
  have hne : (runBlock c.code E s).regs c.test ≠ 0 := (Cond.eval_iff c E s hW).mp hgo
  have hpcT : (runBlock c.code E s).pc = a + c.code.length := by
    rw [runBlock_pc c.code E s (Cond.noBranch_code c), hpc]
  have hfall : Sem P E (a + c.code.length) (a + c.code.length + 1) (runBlock c.code E s)
      (fun k s' => k = 1 ∧ s' = { runBlock c.code E s with pc := a + c.code.length + 1 }) :=
    Sem.jz_next P E (a + c.code.length) (a + c.code.length + b.len + 2) c _ hjz hpcT hne
  exact Sem.trans (Sem.trans htest hfall) hbody

/-- **The loop rule.**  `n` iterations from the loop head, then the failing test.  The iteration
invariant is an explicit family `s : ℕ → RAMState` of loop-head states, with per-iteration costs
`cost : ℕ → ℕ`; the caller supplies one `Sem` per iteration. -/
theorem Sem.loop (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt)
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W) :
    ∀ (n : ℕ) (s : ℕ → RAMState) (cost : ℕ → ℕ),
      (∀ j, (s j).pc = a) →
      (∀ j < n, c.eval (s j)) →
      (¬ c.eval (s n)) →
      (∀ j < n, Sem P E (a + c.code.length + 1) a
        { runBlock c.code E (s j) with pc := a + c.code.length + 1 }
        (fun k s' => k = cost j ∧ s' = s (j + 1))) →
      Sem P E a (a + c.code.length + b.len + 2) (s 0)
        (fun k s' => k ≤ (c.code.length + 1) +
            ∑ j ∈ Finset.range n, (c.code.length + 1 + cost j) ∧
          s' = { runBlock c.code E (s n) with pc := a + c.code.length + b.len + 2 }) := by
  intro n
  induction n with
  | zero =>
      intro s cost hpc _ hstop _
      refine Sem.mono (Sem.loopExit P E a c b (s 0) hAt hW (hpc 0) hstop) ?_
      intro k s' h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, rfl⟩
  | succ n ih =>
      intro s cost hpc hgo hstop hstep
      have hfirst : Sem P E a a (s 0) (fun k s' => k = (c.code.length + 1) + cost 0 ∧ s' = s 1) :=
        Sem.loopStep P E a c b (s 0) (s 1) (cost 0) hAt hW (hpc 0) (hgo 0 (by omega))
          (hstep 0 (by omega))
      have hrest : Sem P E a (a + c.code.length + b.len + 2) (s 1)
          (fun k s' => k ≤ (c.code.length + 1) +
              ∑ j ∈ Finset.range n, (c.code.length + 1 + cost (j + 1)) ∧
            s' = { runBlock c.code E (s (n + 1)) with pc := a + c.code.length + b.len + 2 }) :=
        ih (fun j => s (j + 1)) (fun j => cost (j + 1)) (fun j => hpc (j + 1))
          (fun j hj => hgo (j + 1) (by omega)) (by simpa using hstop)
          (fun j hj => hstep (j + 1) (by omega))
      refine Sem.mono (Sem.seq (Q₂ := fun k₁ k₂ s' =>
        k₁ = (c.code.length + 1) + cost 0 ∧
          (k₂ ≤ (c.code.length + 1) +
              ∑ j ∈ Finset.range n, (c.code.length + 1 + cost (j + 1)) ∧
            s' = { runBlock c.code E (s (n + 1)) with pc := a + c.code.length + b.len + 2 })) hfirst ?_) ?_
      · intro k₁ s₁ hQ₁
        obtain ⟨rfl, rfl⟩ : k₁ = (c.code.length + 1) + cost 0 ∧ s₁ = s 1 := hQ₁
        exact Sem.mono hrest (fun k s' h => ⟨rfl, h.1, h.2⟩)
      · intro k s' h
        obtain ⟨k₁, k₂, hk, h₁, h₂, hstate⟩ := h
        rw [Finset.sum_range_succ']
        exact ⟨by omega, hstate⟩

section Enc

variable {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}

/-- A bit of the integer spelling is the corresponding basis coordinate. -/
theorem enc_bit (b : Module.Basis (Fin w) (ZMod 2) F) (z : F) (k : Fin w) :
    enc b z / 2 ^ (k : ℕ) % 2 = (b.repr z k).val := by
  have hf : ∀ j : Fin w, (b.repr z j).val < 2 ^ 1 := by
    intro j
    have := ZMod.val_lt (b.repr z j)
    simpa using this
  have h := extract_field_sum 1 w (by norm_num) (fun j : Fin w => (b.repr z j).val) hf k
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow] at h
  simpa [enc, Nat.mul_one] using h

/-- `dec` inverts `enc`. -/
theorem dec_enc (b : Module.Basis (Fin w) (ZMod 2) F) (z : F) : dec b (enc b z) = z := by
  have h : ∀ k : Fin w, b.repr (dec b (enc b z)) k = b.repr z k := by
    intro k
    rw [dec, LinearEquiv.apply_symm_apply]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    rw [show (((enc b z / 2 ^ (k : ℕ)) % 2 : ℕ) : ZMod 2) = (((b.repr z k).val : ℕ) : ZMod 2) from by
      rw [enc_bit b z k]]
    exact ZMod.natCast_zmod_val (b.repr z k)
  apply b.repr.injective
  ext k
  exact h k

/-- The integer spelling of a field element is a `w`-bit number. -/
theorem enc_lt (b : Module.Basis (Fin w) (ZMod 2) F) (z : F) : enc b z < 2 ^ w := by
  have h1 : enc b z ≤ ∑ k : Fin w, 2 ^ (k : ℕ) := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    calc (b.repr z k).val * 2 ^ (k : ℕ) ≤ 1 * 2 ^ (k : ℕ) := by
          refine Nat.mul_le_mul_right _ ?_
          have := ZMod.val_lt (b.repr z k)
          omega
      _ = 2 ^ (k : ℕ) := Nat.one_mul _
  have h2 : (∑ k : Fin w, 2 ^ (k : ℕ)) = ∑ k ∈ Finset.range w, 2 ^ k :=
    Fin.sum_univ_eq_sum_range (fun k => 2 ^ k) w
  rw [h2] at h1
  exact lt_of_le_of_lt h1 (sum_range_two_pow_lt w)

/-- **The bridge**: the integer the machine reads out of the packed payload is the integer spelling
of the `j`-th syndrome coordinate. -/
theorem enc_payloadField (b : Module.Basis (Fin w) (ZMod 2) F) {M : ℕ} (y : Fin M → ZMod 2)
    (j : ℕ) :
    enc b (payloadField b y j)
      = ∑ k ∈ Finset.range w, payloadBit y (j * w + k) * 2 ^ k := by
  have h : ∀ k : Fin w,
      (b.repr (payloadField b y j) k).val * 2 ^ (k : ℕ)
        = payloadBit y (j * w + k) * 2 ^ (k : ℕ) := by
    intro k
    rw [payloadField_apply b y j k]
    rfl
  rw [enc, Finset.sum_congr rfl (fun k _ => h k)]
  exact Fin.sum_univ_eq_sum_range (fun k => payloadBit y (j * w + k) * 2 ^ k) w

end Enc

section Tables

variable {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}

@[simp] theorem hdrTab_zero (t N w : ℕ) : hdrTab t N w 0 = t := rfl

@[simp] theorem hdrTab_one (t N w : ℕ) : hdrTab t N w 1 = w := rfl

@[simp] theorem hdrTab_four (t N w : ℕ) : hdrTab t N w 4 = wordsOf (8 * w) (t * w) := rfl

@[simp] theorem hdrTab_five (t N w : ℕ) : hdrTab t N w 5 = 2 ^ w - 1 := rfl

@[simp] theorem hdrTab_six (t N w : ℕ) : hdrTab t N w 6 = detSqBase w := rfl

@[simp] theorem hdrTab_twelve (t N w : ℕ) : hdrTab t N w 12 = 8 * w := rfl

theorem detStd_hdr (t N w : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) {a : ℕ}
    (ha : a < 13) : detStd t N b ι a = hdrTab t N w a := by
  simp [detStd, ha]

/-- `detSqBase` in explicit form. -/
theorem detSqBase_eq (w : ℕ) : detSqBase w = 64 + 2 ^ (2 * w) := rfl

/-- `detMulBase` in explicit form. -/
theorem detMulBase_eq (w : ℕ) : detMulBase w = 64 := rfl

/-- **The squaring table is at a known address**: `detSqBase w + a` holds `sqTab b a` for every
`w`-bit `a`. -/
theorem detStd_sq (t N w : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) {a : ℕ}
    (ha : a < 2 ^ w) : detStd t N b ι (detSqBase w + a) = sqTab b a := by
  have hpos : (0 : ℕ) < 2 ^ (2 * w) := Nat.two_pow_pos _
  have hwle : (2 : ℕ) ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : ¬ (detSqBase w + a < 13) := by rw [detSqBase_eq]; omega
  have h2 : ¬ (detSqBase w + a < detMulBase w) := by rw [detSqBase_eq, detMulBase_eq]; omega
  have h3 : ¬ (detSqBase w + a < detSqBase w) := by omega
  have h4 : detSqBase w + a < detInvBase w := by unfold detInvBase; omega
  unfold detStd
  rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  congr 1
  omega

end Tables

section ReadInt

/-- **Extraction of the `i`-th field of word `addr`**, for a word of `m * w` bits. -/
theorem packMem_field_mul {w m : ℕ} (hw : 0 < w) (hm : 0 < m) (M : ℕ) (y : Fin M → ZMod 2)
    (addr : ℕ) (i : Fin m) :
    packMem (m * w) y addr / 2 ^ (i.val * w) % 2 ^ w
      = ∑ k ∈ Finset.range w, payloadBit y (addr * (m * w) + i.val * w + k) * 2 ^ k := by
  have hmw : 0 < m * w := Nat.mul_pos hm hw
  have hpack : packMem (m * w) y addr
      = ∑ j : Fin m,
          (∑ k ∈ Finset.range w, payloadBit y (addr * (m * w) + j.val * w + k) * 2 ^ k)
            * 2 ^ (j.val * w) := by
    rw [packMem_eq_sum_bits hmw,
      sum_range_bits_split w m (fun b => payloadBit y (addr * (m * w) + b))]
    simp only [Nat.add_assoc]
    exact (Fin.sum_univ_eq_sum_range (fun j => (∑ k ∈ Finset.range w,
      payloadBit y (addr * (m * w) + (j * w + k)) * 2 ^ k) * 2 ^ (j * w)) m).symm
  rw [hpack, ← Nat.and_two_pow_sub_one_eq_mod, ← Nat.shiftRight_eq_div_pow]
  exact extract_field_sum w m hw _ (fun j => bits_sum_lt_two_pow y _) i

/-- **The read of syndrome coordinate `j`**: shift the payload word down by the offset of `j` and
mask the low `w` bits. -/
theorem read_syndrome {w : ℕ} (hw : 0 < w) (M : ℕ) (y : Fin M → ZMod 2) (j : ℕ) :
    ((packMem (8 * w) y (j / 8) >>> ((j % 8) * w)) &&& (2 ^ w - 1)) = syndromeInt w y j := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [packMem_field_mul hw (by norm_num) M y (j / 8) ⟨j % 8, Nat.mod_lt _ (by norm_num)⟩]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h1 : (j / 8) * 8 + j % 8 = j := by
    rw [Nat.mul_comm (j / 8) 8]
    exact Nat.div_add_mod j 8
  have h2 : (j / 8) * (8 * w) + (j % 8) * w = j * w := by
    rw [← Nat.mul_assoc, ← Nat.add_mul, h1]
  rw [h2]

theorem mul_div_eight (w : ℕ) (hw : 0 < w) (k : ℕ) : k * w / (8 * w) = k / 8 := by
  rw [Nat.mul_comm k w, Nat.mul_comm 8 w, Nat.mul_div_mul_left k 8 hw]

theorem mul_mod_eight (w : ℕ) (k : ℕ) : k * w % (8 * w) = k % 8 * w :=
  Nat.mul_mod_mul_right w k 8

/-- Divisions are unchanged by adding a remainder that stays below the divisor. -/
theorem add_div_of_mod_add_lt {A b c : ℕ} (h : A % c + b < c) : (A + b) / c = A / c := by
  have hc : 0 < c := by omega
  have h1 : c * (A / c) + (A % c + b) = A + b := by
    have h2 := Nat.div_add_mod A c
    omega
  rw [← h1, Nat.mul_add_div hc, Nat.div_eq_of_lt h, Nat.add_zero]

/-- `wordsOf` for a word that holds eight `w`-bit fields: `⌈t/8⌉` words.  `as in the paper`, the
payload of `tw` bits occupies `tw / W = ⌈t/8⌉` words of `W = 8w` bits. -/
theorem wordsOf_eight (w t : ℕ) (hw : 0 < w) : wordsOf (8 * w) (t * w) = (t + 7) / 8 := by
  unfold wordsOf
  have h1 : t * w + 8 * w - 1 = (t + 7) * w + (w - 1) := by
    have h2 : t * w + 8 * w = (t + 8) * w := by rw [Nat.add_mul]
    have h3 : (t + 8) * w = (t + 7) * w + w := by
      rw [show t + 8 = t + 7 + 1 from rfl, Nat.succ_mul]
    rw [h2, h3]
    omega
  rw [h1]
  have h4 : (t + 7) * w % (8 * w) + (w - 1) < 8 * w := by
    rw [Nat.mul_mod_mul_right w (t + 7) 8]
    have h5 : (t + 7) % 8 ≤ 7 := by
      have h6 : (t + 7) % 8 < 8 := Nat.mod_lt _ (by norm_num)
      omega
    have h6 : (t + 7) % 8 * w ≤ 7 * w := Nat.mul_le_mul_right w h5
    omega
  rw [add_div_of_mod_add_lt h4, Nat.mul_comm (t + 7) w, Nat.mul_comm 8 w,
    Nat.mul_div_mul_left (t + 7) 8 hw]

end ReadInt

section ReadLoop

/-- A packed word is a `W`-bit word. -/
theorem packMem_lt {w M : ℕ} (hw : 0 < w) (y : Fin M → ZMod 2) (addr : ℕ) :
    packMem (8 * w) y addr < 2 ^ (8 * w) := by
  have hW : 0 < 8 * w := by omega
  rw [packMem_eq_sum_bits hW]
  have h1 : (∑ b ∈ Finset.range (8 * w), payloadBit y (addr * (8 * w) + b) * 2 ^ b)
      ≤ ∑ b ∈ Finset.range (8 * w), 2 ^ b := by
    refine Finset.sum_le_sum (fun b _ => ?_)
    calc payloadBit y (addr * (8 * w) + b) * 2 ^ b ≤ 1 * 2 ^ b :=
          Nat.mul_le_mul_right _ (payloadBit_le_one y _)
      _ = 2 ^ b := Nat.one_mul _
  exact lt_of_le_of_lt h1 (sum_range_two_pow_lt (8 * w))

theorem readMem_zero {M : ℕ} (S0 w : ℕ) (y : Fin M → ZMod 2) :
    readMem S0 w y 0 = fun addr => if addr < S0 then packMem (8 * w) y addr else 0 := by
  funext addr
  simp only [readMem]
  by_cases h : addr < S0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    rw [if_neg (by omega : ¬ ((addr - S0) % 2 = 0 ∧ (addr - S0) / 2 < 0))]

theorem readMem_succ {M : ℕ} (S0 w : ℕ) (y : Fin M → ZMod 2) (k : ℕ) :
    readMem S0 w y (k + 1)
      = Function.update (readMem S0 w y k) (S0 + 2 * k) (syndromeInt w y k) := by
  funext addr
  by_cases h : addr = S0 + 2 * k
  · subst h
    rw [Function.update_self]
    simp only [readMem]
    rw [if_neg (by omega)]
    have h2 : S0 + 2 * k - S0 = 2 * k := by omega
    rw [h2, if_pos ⟨by omega, by omega⟩]
    norm_num
  · rw [Function.update_of_ne h]
    simp only [readMem]
    by_cases hlt : addr < S0
    · rw [if_pos hlt, if_pos hlt]
    · rw [if_neg hlt, if_neg hlt]
      by_cases hc : (addr - S0) % 2 = 0 ∧ (addr - S0) / 2 < k
      · rw [if_pos hc, if_pos ⟨hc.1, by omega⟩]
      · rw [if_neg hc, if_neg]
        intro hc'
        obtain ⟨h1, h2⟩ := hc'
        have h3 : (addr - S0) / 2 = k := by omega
        have h4 : (addr - S0) = 2 * k := by
          have h5 := Nat.div_add_mod (addr - S0) 2
          omega
        omega

theorem readMem_below {M : ℕ} (S0 w : ℕ) (y : Fin M → ZMod 2) (k : ℕ) {addr : ℕ}
    (h : addr < S0) : readMem S0 w y k addr = packMem (8 * w) y addr := by
  simp only [readMem]
  rw [if_pos h]

@[simp] theorem readBody_length : readBody.length = 16 := by simp [readBody]

@[simp] theorem readLoopAt_length (base : ℕ) : (readLoopAt base).length = 19 := by
  simp [readLoopAt]

end ReadLoop

section ProgramAt

end ProgramAt

section ReadSpec

/-- The read of coordinate `j` in division form, which is what the machine computes. -/
theorem read_syndrome_div {w : ℕ} (hw : 0 < w) (M : ℕ) (y : Fin M → ZMod 2) (j : ℕ) :
    packMem (8 * w) y (j / 8) / 2 ^ (j % 8 * w) % 2 ^ w = syndromeInt w y j := by
  rw [← Nat.and_two_pow_sub_one_eq_mod, ← Nat.shiftRight_eq_div_pow]
  exact read_syndrome hw M y j

/-- The value the machine ends up with when it reads coordinate `j`: the shift/mask pipeline applied
to the packed payload word. -/
theorem read_value {w : ℕ} {W : ℕ} (hwe : w ≤ W) (hw : 0 < w) (M : ℕ) (y : Fin M → ZMod 2) (j : ℕ) :
    (packMem (8 * w) y (j / 8) / 2 ^ (j % 8 * w)) % 2 ^ W % 2 ^ w = syndromeInt w y j := by
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hwe)]
  exact read_syndrome_div hw M y j

/-- The address the body computes (`j + j + S0`) is the syndrome address. -/
theorem haddr2_of {k S0 W : ℕ} (haddr : (S0 + 2 * k) % 2 ^ W = S0 + 2 * k) :
    (k + k + S0) % 2 ^ W = S0 + 2 * k := by
  have h : k + k + S0 = S0 + 2 * k := by omega
  rw [h, haddr]

/-- **The read-loop body, as a state map.**  One pass reads coordinate `k` out of the payload
(eight fields per word), stores `P_{2k+1}` at `S0 + 2k`, and clears the scratch registers so that
the loop invariant stays a function of the counter alone. -/
theorem readBody_spec (E : RAMEnv) (base S0 w t k : ℕ) (y : Fin (t * w) → ZMod 2) (s : RAMState)
    (hpc : s.pc = base + 2) (hregs : s.regs = Function.update (readState base S0 w t y k).regs r14 1)
    (hmem : s.mem = readMem S0 w y k)
    (hW : E.W = 8 * w) (hwe : w ≤ E.W) (hw : 0 < w)
    (hmul : k * w % 2 ^ E.W = k * w) (hdiv : k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : k * w % (8 * w) % 2 ^ E.W = k % 8 * w) (haddr : (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : k / 8 < S0) (hpk : packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8)) :
    runBlock readBody E s = { readState base S0 w t y (k + 1) with pc := base + 18 } := by
  have haddr2 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k := haddr2_of haddr
  have hval : ((packMem (8 * w) y (k / 8) / 2 ^ (k % 8 * w)) % 2 ^ E.W % 2 ^ w) % 2 ^ E.W
      = syndromeInt w y k := by
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos w))
      (Nat.pow_le_pow_right (by norm_num) hwe))]
    exact read_value hwe hw (t * w) y k
  have hpc' : (runBlock readBody E s).pc = base + 18 := by
    rw [runBlock_pc readBody E s (by simp [readBody]), hpc, readBody_length]
  refine ramState_eq_of _ _ hpc' ?_ ?_
  · funext addr
    show (runBlock readBody E s).mem addr = readMem S0 w y (k + 1) addr
    by_cases h : addr = S0 + 2 * k
    · rw [h, readMem_succ, Function.update_self]
      simp only [readBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_mul,
        hregs, readState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        Matrix.cons_val_one, Matrix.cons_val_zero, hmul, hmem, execInstr_div, Function.update_self, hdiv,
        execInstr_mod, hmod, execInstr_load, readMem_below S0 w y k hword, hpk, execInstr_shr,
        Function.update_idem, execInstr_band, Nat.and_two_pow_sub_one_eq_mod, hval, execInstr_add,
        Nat.mod_add_mod, haddr2, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil]
    · rw [readMem_succ, Function.update_of_ne h]
      simp [readBody, runBlock_cons, runBlock_nil, hregs, hmem, readState, hmul, hdiv, hmod,
        haddr, haddr2, hk1, hmask, readMem_below S0 w y k hword, hpk, hval, Function.update_of_ne h]
  · intro d
    simp only [readBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_mul,
      hregs, readState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero, hmul, execInstr_div, Function.update_self, hdiv,
      execInstr_mod, hmod, execInstr_load, execInstr_shr, Function.update_idem, execInstr_band,
      Nat.and_two_pow_sub_one_eq_mod, execInstr_add, Nat.mod_add_mod, execInstr_store, hk1, execInstr_imm,
      Nat.zero_mod, runBlock_nil]
    fin_cases d <;>
      simp only [readBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_mul,
        hregs, readState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        Matrix.cons_val_one, Matrix.cons_val_zero, hmul, execInstr_div, Function.update_self, hdiv,
        execInstr_mod, hmod, execInstr_load, execInstr_shr, Function.update_idem, execInstr_band,
        Nat.and_two_pow_sub_one_eq_mod, execInstr_add, Nat.mod_add_mod, execInstr_store, hk1, execInstr_imm,
        Nat.zero_mod, runBlock_nil, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Nat.add_left_cancel_iff]

end ReadSpec

section ReadStmt

theorem readCond_code_length : readCond.code.length = 1 := rfl

/-- `readLoopAt` is exactly the compilation of the statement: `base + 19` is *computed*. -/
theorem readLoopStmt_compile (base : ℕ) : Stmt.compile readLoopStmt base = readLoopAt base := by
  simp [Stmt.compile, Stmt.len, Cond.code, Cond.test, readLoopAt, readBody_length]

theorem readLoopStmt_length (base : ℕ) : (Stmt.compile readLoopStmt base).length = 19 := by
  rw [readLoopStmt_compile, readLoopAt_length]

/-- The three facts a compiled read loop provides, read off `At` elementwise (so that no
`Stmt.compile` unfolding is needed at the use sites). -/
theorem at_loop_read {P : Program} {base : ℕ}
    (hAt : At P base (Stmt.compile readLoopStmt base)) :
    P[base + 1]? = some (iJz r14 (base + 19)) ∧ At P (base + 2) readBody ∧
      P[base + 18]? = some (iJmp base) := by
  have hlen := readLoopStmt_length base
  refine ⟨?_, ?_, ?_⟩
  · have h := hAt 1 (by omega)
    rw [readLoopStmt_compile] at h
    simpa [readLoopAt] using h
  · intro r hr
    have hr16 : r < 16 := by rw [← readBody_length]; exact hr
    have h := hAt (r + 2) (by omega)
    rw [readLoopStmt_compile] at h
    have hlist : (readLoopAt base)[r + 2]? = readBody[r]? := by
      simp only [readLoopAt]
      rw [List.append_assoc]
      rw [List.getElem?_append_right
        (by simp : ([iLt r14 r5 r0, iJz r14 (base + 19)]).length ≤ r + 2)]
      rw [show r + 2 - ([iLt r14 r5 r0, iJz r14 (base + 19)]).length = r from by simp]
      exact List.getElem?_append_left hr
    rw [hlist] at h
    rwa [show base + (r + 2) = base + 2 + r from by omega] at h
  · have h := hAt 18 (by omega)
    rw [readLoopStmt_compile] at h
    simpa [readLoopAt] using h

theorem readState_regs_eq (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (readState base S0 w t y k).regs
      = ![t, w, S0, 2 ^ w - 1, detSqBase w, k, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8 * w] := rfl

@[simp] theorem readState_r14 (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (readState base S0 w t y k).regs r14 = 0 := by
  rw [readState_regs_eq]
  simp

/-- A loop-head state with its own program counter written back is unchanged. -/
theorem readState_eta (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    ({ readState base S0 w t y k with pc := base } : RAMState) = readState base S0 w t y k := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp
  · simp
  · intro d; simp

/-- The loop test holds exactly when the counter is below `t`. -/
theorem readCond_eval (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    readCond.eval (readState base S0 w t y k) ↔ k < t := by
  simp [Cond.eval, readState_regs_eq]

/-- At the exit the test fails. -/
theorem readCond_false (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) :
    ¬ readCond.eval (readState base S0 w t y t) := by
  rw [readCond_eval]
  exact lt_irrefl t

/-- A constant sum over a range. -/
theorem sum_range_const_mul (t c : ℕ) : (∑ j ∈ Finset.range t, c) = c * t := by
  induction t with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Overwriting a register whose value is already `0` changes nothing. -/
theorem update_zero_eq (s : RAMState) (h : s.regs r14 = 0) :
    Function.update s.regs r14 0 = s.regs := by
  rw [← h]
  exact Function.update_eq_self _ _

/-- Running the test materialises `r14 = (j < t)` and advances to the body. -/
theorem runBlock_readCond (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    runBlock readCond.code E (readState base S0 w t y k) = { pc := base + 1, regs := Function.update (readState base S0 w t y k).regs r14 ((if k < t then 1 else 0) % 2 ^ E.W), mem := readMem S0 w y k } := by
  have hcode : readCond.code = [iLt r14 r5 r0] := rfl
  rw [hcode, runBlock_cons, runBlock_nil, execInstr_lt]
  dsimp only [readState]
  try rfl

/-- The same with the test known to hold: `r14` becomes `1`. -/
theorem runBlock_readCond_of_lt (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hW : 1 < 2 ^ E.W) (hk : k < t) :
    runBlock readCond.code E (readState base S0 w t y k) = { readState base S0 w t y k with pc := base + 1, regs := Function.update (readState base S0 w t y k).regs r14 1 } := by
  rw [runBlock_readCond, if_pos hk, Nat.mod_eq_of_lt hW]
  try rfl

/-- The same with the test known to fail: `r14` becomes `0`. -/
theorem runBlock_readCond_of_ge (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hk : ¬ k < t) :
    runBlock readCond.code E (readState base S0 w t y k) = { readState base S0 w t y k with pc := base + 1, regs := Function.update (readState base S0 w t y k).regs r14 0 } := by
  rw [runBlock_readCond, if_neg hk, Nat.zero_mod]
  try rfl

/-- At the exit, the test run leaves the state alone apart from the program counter. -/
theorem runBlock_readCond_exit (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) :
    runBlock readCond.code E (readState base S0 w t y t) = { readState base S0 w t y t with pc := base + 1 } := by
  have h0 : (readState base S0 w t y t).regs r14 = 0 := readState_r14 base S0 w t y t
  have h := runBlock_readCond_of_ge E base S0 w t y t (lt_irrefl t)
  rw [update_zero_eq _ h0] at h
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · rw [h]
  · rw [h]
  · intro d
    rw [h]

/-- The body entry state, in the shape the loop rule produces. -/
theorem readBodyIn_eq (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hW : 1 < 2 ^ E.W) (hk : k < t) :
    ({ runBlock readCond.code E (readState base S0 w t y k) with pc := base + readCond.code.length + 1 } : RAMState) = readBodyIn base S0 w t y k := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hrun := runBlock_readCond_of_lt E base S0 w t y k hW hk
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp only [readBodyIn]
    rw [hcl]
  · simp only [readBodyIn]
    rw [hrun]
    simp
  · intro d
    simp only [readBodyIn]
    rw [hrun]

/-- The body of the read loop, as a `Sem` run: from the body entry to the `jmp`, in 16 steps. -/
theorem readBody_sem (P : Program) (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2)
    (k : ℕ) (hAt : At P (base + 2) readBody)
    (hW : 1 < 2 ^ E.W) (hW8 : E.W = 8 * w) (hwe : w ≤ E.W) (hw : 0 < w)
    (hmul : k * w % 2 ^ E.W = k * w) (hdiv : k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : k * w % (8 * w) % 2 ^ E.W = k % 8 * w) (haddr : (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : k / 8 < S0)
    (hpk : packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8)) :
    Sem P E (base + 2) (base + 18) (readBodyIn base S0 w t y k)
      (fun c s' => c = 16 ∧ s' = { readState base S0 w t y (k + 1) with pc := base + 18 }) := by
  refine Sem.mono (Sem.block P E (base + 2) readBody (readBodyIn base S0 w t y k) hAt
    (by simp [readBody]) rfl) ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hc, readBody_length]
  · rw [hs]
    exact readBody_spec E base S0 w t k y (readBodyIn base S0 w t y k) rfl rfl rfl hW8 hwe hw hmul
      hdiv hmod haddr hk1 hmask hword hpk

/-- The iteration *after* the test: from the body entry back to the loop head, in 17 steps
(`16` for the body, `1` for the `jmp`).  This is what `Sem.loop` consumes. -/
theorem readBodyIter (P : Program) (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2)
    (k : ℕ) (hAt : At P base (Stmt.compile readLoopStmt base)) (hW : 1 < 2 ^ E.W)
    (hW8 : E.W = 8 * w) (hwe : w ≤ E.W) (hw : 0 < w) (hk : k < t)
    (hmul : k * w % 2 ^ E.W = k * w) (hdiv : k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : k * w % (8 * w) % 2 ^ E.W = k % 8 * w) (haddr : (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : k / 8 < S0)
    (hpk : packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8)) :
    Sem P E (base + readCond.code.length + 1) base ({ runBlock readCond.code E (readState base S0 w t y k) with pc := base + readCond.code.length + 1 } : RAMState)
      (fun c s' => c = 17 ∧ s' = readState base S0 w t y (k + 1)) := by
  obtain ⟨hjz, hbodyAt, hjmp⟩ := at_loop_read hAt
  have hbody := readBody_sem P E base S0 w t y k hbodyAt hW hW8 hwe hw hmul hdiv hmod haddr hk1
    hmask hword hpk
  rw [readBodyIn_eq E base S0 w t y k hW hk]
  refine Sem.jmp_append (hAt := hjmp) ?_
  refine Sem.mono hbody ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨by omega, ?_⟩
  rw [hs]
  exact readState_eta base S0 w t y (k + 1)

/-- The exit state of the read loop: the test run only moves the program counter. -/
theorem readLoop_exit_state (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) :
    ({ runBlock readCond.code E (readState base S0 w t y t) with pc := base + readCond.code.length + (Stmt.code readBody).len + 2 } : RAMState) = { readState base S0 w t y t with pc := base + 19 } := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hbl : (Stmt.code readBody).len = 16 := readBody_length
  have hrun := runBlock_readCond_exit E base S0 w t y
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp only [hcl, hbl]
  · simp only [hrun]
  · intro d
    simp only [hrun]

/-- **The read loop.**  One `Sem.loop` call: `t` iterations of `2 + 17` steps, then the failing
test (`2` more).  The state invariant is a function of the counter alone. -/
theorem readLoop_spec (P : Program) (E : RAMEnv) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2)
    (hAt : At P base (Stmt.compile readLoopStmt base)) (hW : 1 < 2 ^ E.W) (hW8 : E.W = 8 * w)
    (hwe : w ≤ E.W) (hw : 0 < w)
    (hmul : ∀ k < t, k * w % 2 ^ E.W = k * w)
    (hdiv : ∀ k < t, k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : ∀ k < t, k * w % (8 * w) % 2 ^ E.W = k % 8 * w)
    (haddr : ∀ k < t, (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1)
    (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : ∀ k < t, k / 8 < S0)
    (hpk : ∀ k < t, packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8)) :
    Sem P E base (base + 19) (readState base S0 w t y 0)
      (fun c s' => c ≤ 19 * t + 2 ∧ s' = { readState base S0 w t y t with pc := base + 19 }) := by
  have hloop := Sem.loop P E base readCond (Stmt.code readBody) hAt hW t
    (fun j => readState base S0 w t y j) (fun _ => 17)
    (fun j => rfl)
    (fun j hj => (readCond_eval base S0 w t y j).mpr hj)
    (readCond_false base S0 w t y)
    (fun j hj => readBodyIter P E base S0 w t y j hAt hW hW8 hwe hw hj (hmul j hj) (hdiv j hj)
      (hmod j hj) (haddr j hj) (hk1 j hj) hmask (hword j hj) (hpk j hj))
  have h19 : ((readCond.code.length + 1) + 17) = 19 := by
    rw [readCond_code_length]
  have hsum19 : (∑ j ∈ Finset.range t, (19 : ℕ)) = 19 * t := sum_range_const_mul t 19
  have hsum : (∑ j ∈ Finset.range t, ((readCond.code.length + 1) + 17)) = 19 * t := by
    rw [← hsum19]
    exact Finset.sum_congr rfl (fun j _ => h19)
  refine Sem.mono hloop ?_
  intro c s' hQ
  obtain ⟨hle, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hsum] at hle
    rw [readCond_code_length] at hle
    omega
  · rw [hs]
    exact readLoop_exit_state E base S0 w t y

end ReadStmt

section Bounds

/-- `k * w` and the syndrome addresses of the first `t` coordinates fit in a word. `as in the
paper`: the payload has `tw` bits and `W = 8w`, so every index the read loop forms is below `2^W`. -/
theorem mul_lt_two_pow_eight {w N k : ℕ} (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (hkN : k < N) :
    k * w < 2 ^ (8 * w) := by
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  have hk2 : k ≤ 2 ^ w - 1 := by omega
  have hw2 : w ≤ 2 ^ w - 1 := by
    have := Nat.lt_two_pow_self (n := w)
    omega
  have h1 : k * w ≤ (2 ^ w - 1) * w := Nat.mul_le_mul_right w hk2
  have h2 : (2 ^ w - 1) * w ≤ (2 ^ w - 1) * (2 ^ w - 1) := Nat.mul_le_mul_left _ hw2
  have h4 : (2 ^ w - 1) < 2 ^ w := by omega
  have h3 : (2 ^ w - 1) * (2 ^ w - 1) < 2 ^ w * 2 ^ w := by
    calc (2 ^ w - 1) * (2 ^ w - 1) < 2 ^ w * (2 ^ w - 1) :=
          Nat.mul_lt_mul_of_pos_right h4 (by omega)
      _ < 2 ^ w * 2 ^ w := Nat.mul_lt_mul_of_pos_left h4 hpos
  have h5 : 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have h6 : 2 ^ (2 * w) ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The syndrome address `S0 + 2k` of coordinate `k < t` fits in a word. -/
theorem addr_lt_two_pow_eight {w t k S0 : ℕ} (hw1 : 1 ≤ w) (hNw : t < 2 ^ w)
    (hS0 : S0 ≤ t) (hk : k < t) : S0 + 2 * k < 2 ^ (8 * w) := by
  have hk2 : 2 * k < 2 ^ (w + 1) := by
    have h : 2 * k < 2 * 2 ^ w := by omega
    calc 2 * k < 2 * 2 ^ w := h
      _ = 2 ^ (w + 1) := by rw [Nat.pow_succ]; ring
  have h1 : S0 + 2 * k < 2 ^ w + 2 ^ (w + 1) := by omega
  have h2 : (2 : ℕ) ^ w + 2 ^ (w + 1) ≤ 2 ^ (w + 2) := by
    have e1 : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ]; ring
    have e2 : (2 : ℕ) ^ (w + 2) = 4 * 2 ^ w := by
      rw [show w + 2 = w + 1 + 1 from rfl, Nat.pow_succ, e1]
      ring
    omega
  have h3 : (2 : ℕ) ^ (w + 2) ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The address `S0 + 2k + 1` the expansion loop stores at fits in a word. -/
theorem addr_succ_lt_two_pow_eight {w t k S0 : ℕ} (hw1 : 1 ≤ w) (hNw : t < 2 ^ w)
    (hS0 : S0 ≤ t) (hk : k < t) : S0 + 2 * k + 1 < 2 ^ (8 * w) := by
  have hk2 : 2 * k < 2 ^ (w + 1) := by
    have h : 2 * k < 2 * 2 ^ w := by omega
    calc 2 * k < 2 * 2 ^ w := h
      _ = 2 ^ (w + 1) := by rw [Nat.pow_succ]; ring
  have h1 : S0 + 2 * k + 1 < 2 ^ w + 2 ^ (w + 1) + 1 := by omega
  have h2 : (2 : ℕ) ^ w + 2 ^ (w + 1) + 1 ≤ 2 ^ (w + 2) := by
    have e1 : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ]; ring
    have e2 : (2 : ℕ) ^ (w + 2) = 4 * 2 ^ w := by
      rw [show w + 2 = w + 1 + 1 from rfl, Nat.pow_succ, e1]
      ring
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    omega
  have h3 : (2 : ℕ) ^ (w + 2) ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- `wordsOf (8w) (tw) ≤ t`: the payload never needs more words than it has syndrome coordinates. -/
theorem wordsOf_le (w t : ℕ) (hw1 : 1 ≤ w) : wordsOf (8 * w) (t * w) ≤ t := by
  rw [wordsOf_eight w t (by omega)]
  omega

/-- The squaring table of `det` starts inside a word: `detSqBase w = 64 + 2^{2w} < 2^{8w}`. -/
theorem detSqBase_lt {w : ℕ} (hw1 : 1 ≤ w) : detSqBase w < 2 ^ (8 * w) := by
  by_cases hw4 : w ≤ 3
  · unfold detSqBase detMulBase
    interval_cases w <;> norm_num
  · have hw4' : 3 < w := by omega
    have h3 : (64 : ℕ) ≤ 2 ^ (2 * w) := by
      have h : (2 : ℕ) ^ 6 ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * w) := h
    have h5 : (2 : ℕ) ^ (2 * w) + 2 ^ (2 * w) = 2 ^ (2 * w + 1) := by
      rw [Nat.pow_succ]
      ring
    have h6 : (2 : ℕ) ^ (2 * w + 1) < 2 ^ (8 * w) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h7 : 64 + 2 ^ (2 * w) ≤ 2 ^ (2 * w) + 2 ^ (2 * w) := by omega
    rw [detSqBase, detMulBase]
    calc 64 + 2 ^ (2 * w) ≤ 2 ^ (2 * w) + 2 ^ (2 * w) := h7
      _ = 2 ^ (2 * w + 1) := h5
      _ < 2 ^ (8 * w) := h6

/-- The whole table ends inside a word: `detInvBase w < 2^{8w}`. -/
theorem detInvBase_lt {w : ℕ} (hw1 : 1 ≤ w) : detInvBase w < 2 ^ (8 * w) := by
  by_cases hw3 : w ≤ 2
  · unfold detInvBase detSqBase detMulBase
    interval_cases w <;> norm_num
  · have h3 : (64 : ℕ) ≤ 2 ^ (2 * w) := by
      have h : (2 : ℕ) ^ 6 ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * w) := h
    have hA : (2 : ℕ) ^ (2 * w) + 2 ^ (2 * w) = 2 ^ (2 * w + 1) := by
      rw [Nat.pow_succ]
      ring
    have hB : (2 : ℕ) ^ (2 * w + 1) + 2 ^ (2 * w + 1) = 2 ^ (2 * w + 2) := by
      rw [Nat.pow_succ]
      ring
    have h1 : detInvBase w ≤ 2 ^ (2 * w + 2) := by
      unfold detInvBase detSqBase detMulBase
      omega
    have h2 : (2 : ℕ) ^ (2 * w + 2) < 2 ^ (8 * w) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

/-- A squared table entry fits in a word: `detSqBase w + a < 2^{8w}` for every `w`-bit `a`. -/
theorem detSqBase_add_lt {w a : ℕ} (hw1 : 1 ≤ w) (ha : a < 2 ^ w) :
    detSqBase w + a < 2 ^ (8 * w) := by
  have hwle : (2 : ℕ) ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : detSqBase w + a < detInvBase w := by
    unfold detInvBase
    omega
  exact lt_trans h1 (detInvBase_lt hw1)

end Bounds

section Prologue

@[simp] theorem paramBody_length : paramBody.length = 14 := by simp [paramBody]

/-- **The prologue, as a state map.**  It reads the six parameters it needs and nothing else; the
memory is untouched. -/
theorem paramBody_spec (E : RAMEnv) (N t w S0 : ℕ) (y : Fin (t * w) → ZMod 2)
    (hS0 : S0 = wordsOf (8 * w) (t * w)) (hW : E.W = 8 * w) (hw1 : 1 ≤ w)
    (h0 : E.det 0 % 2 ^ E.W = t) (h1 : E.det 1 % 2 ^ E.W = w) (h4 : E.det 4 % 2 ^ E.W = S0)
    (h5 : E.det 5 % 2 ^ E.W = 2 ^ w - 1) (h6 : E.det 6 % 2 ^ E.W = detSqBase w)
    (h12 : E.det 12 % 2 ^ E.W = 8 * w) (h1W : (1 : ℕ) % 2 ^ E.W = 1) :
    runBlock paramBody E (decoderStart (8 * w) y []) = readState paramBody.length S0 w t y 0 := by
  have hmem : (decoderStart (8 * w) y []).mem = readMem S0 w y 0 := by
    funext addr
    rw [show (decoderStart (8 * w) y []).mem = hintMem (8 * w) y ([] : List ℕ) from rfl]
    simp only [readMem_zero, hintMem, hS0, List.getD_nil]
  have hpc' : (runBlock paramBody E (decoderStart (8 * w) y [])).pc = paramBody.length := by
    rw [runBlock_pc paramBody E _ (by simp [paramBody])]
    simp [decoderStart, initState, paramBody_length]
  have hbig : 16 ≤ 2 ^ E.W := by
    rw [hW]
    have h2 : 2 ^ 8 ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4m : (4 : ℕ) % 2 ^ E.W = 4 := Nat.mod_eq_of_lt (by omega)
  have h5m : (5 : ℕ) % 2 ^ E.W = 5 := Nat.mod_eq_of_lt (by omega)
  have h6m : (6 : ℕ) % 2 ^ E.W = 6 := Nat.mod_eq_of_lt (by omega)
  have h12m : (12 : ℕ) % 2 ^ E.W = 12 := Nat.mod_eq_of_lt (by omega)
  refine ramState_eq_of _ _ hpc' ?_ ?_
  · funext addr
    simp only [paramBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_imm,
      Nat.zero_mod, hmem, execInstr_qDet, Function.update_self, runBlock_nil, readState, List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd]
  · intro d
    simp only [paramBody, readState, h0, h1, h4, h5, h6, h12, h1W, h4m, h5m, h6m, h12m,
      decoderStart, initState, runBlock_cons, runBlock_nil, execInstr_imm, execInstr_qDet,
      Function.update_idem]
    fin_cases d <;>
      simp [paramBody, readState, h0, h1, h4, h5, h6, h12, h1W, h4m, h5m, h6m, h12m,
        decoderStart, initState, runBlock_cons, runBlock_nil]

end Prologue

section ReadAssembly

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end ReadAssembly

section Expand

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

/-- The successor step, stated with an explicit `Nat.succ` so that the generated `match`
reduces during elaboration. -/
theorem eSeq_succ {w : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) {M : ℕ} (y : Fin M → ZMod 2) (n : ℕ) :
    eSeq b y (Nat.succ n)
      = if Even (Nat.succ n) then payloadField b y (Nat.succ n / 2)
        else (eSeq b y (Nat.succ n / 2)) ^ 2 := by
  rw [eSeq.eq_def]

theorem eSeq_even {w : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) {M : ℕ} (y : Fin M → ZMod 2) (k : ℕ) :
    eSeq b y (2 * k) = payloadField b y k := by
  cases k with
  | zero => rw [eSeq.eq_def]
  | succ j =>
      have harg : 2 * (j + 1) = Nat.succ (2 * j + 1) := by omega
      rw [harg, eSeq_succ,
        if_pos (show Even (Nat.succ (2 * j + 1)) from ⟨j + 1, by omega⟩)]
      congr 1
      show (2 * j + 2) / 2 = j + 1
      omega

theorem eSeq_odd {w : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) {M : ℕ} (y : Fin M → ZMod 2) (k : ℕ) :
    eSeq b y (2 * k + 1) = (eSeq b y k) ^ 2 := by
  have harg : 2 * k + 1 = Nat.succ (2 * k) := by omega
  rw [harg, eSeq_succ,
    if_neg (show ¬ Even (Nat.succ (2 * k)) from by rintro ⟨r, hr⟩; omega)]
  rw [show Nat.succ (2 * k) / 2 = k from by
    show (2 * k + 1) / 2 = k
    omega]

/-- The squaring table, applied to a reading of `eSeq k`, returns `eSeq (2k+1)`. -/
theorem sqTab_enc {w : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) {M : ℕ} (y : Fin M → ZMod 2) (k : ℕ) :
    sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)) := by
  show enc b ((dec b (enc b (eSeq b y k))) ^ 2) = enc b (eSeq b y (2 * k + 1))
  rw [dec_enc, ← eSeq_odd]

/-- **The read loop's output is the expansion's input.** -/
theorem expandMem_zero {w M : ℕ} (S0 : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin M → ZMod 2) (t : ℕ) :
    expandMem S0 b y t 0 = readMem S0 w y t := by
  funext addr
  simp only [expandMem, readMem]
  by_cases h : addr < S0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    by_cases he : (addr - S0) % 2 = 0
    · rw [if_pos he]
      by_cases ht : (addr - S0) / 2 < t
      · rw [if_pos ht, if_pos ⟨he, ht⟩]
      · rw [if_neg ht, if_neg (fun hh => ht hh.2)]
    · rw [if_neg he]
      rw [if_neg (fun hh : (addr - S0) % 2 = 0 ∧ (addr - S0) / 2 < t => he hh.1)]
      rw [if_neg (Nat.not_lt_zero _)]

/-- **One expansion step**: the only memory cell that changes is `S0 + 2k + 1`. -/
theorem expandMem_succ {w M : ℕ} (S0 : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin M → ZMod 2) (t k : ℕ) :
    expandMem S0 b y t (k + 1)
      = Function.update (expandMem S0 b y t k) (S0 + 2 * k + 1) (enc b (eSeq b y (2 * k + 1))) := by
  funext addr
  by_cases h : addr = S0 + 2 * k + 1
  · subst h
    rw [Function.update_self]
    simp only [expandMem]
    rw [if_neg (by omega : ¬ S0 + 2 * k + 1 < S0)]
    rw [show S0 + 2 * k + 1 - S0 = 2 * k + 1 from by omega]
    rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]
    rw [if_pos (by omega : (2 * k + 1) / 2 < k + 1)]
    rw [show 2 * ((2 * k + 1) / 2) + 1 = 2 * k + 1 from by omega]
  · rw [Function.update_of_ne h]
    simp only [expandMem]
    by_cases hs : addr < S0
    · rw [if_pos hs, if_pos hs]
    · rw [if_neg hs, if_neg hs]
      by_cases he : (addr - S0) % 2 = 0
      · rw [if_pos he, if_pos he]
      · rw [if_neg he, if_neg he]
        have hmod2 : (addr - S0) % 2 < 2 := Nat.mod_lt _ (by norm_num)
        have hne : (addr - S0) / 2 ≠ k := by
          intro hqk
          have h2 := Nat.div_add_mod (addr - S0) 2
          omega
        by_cases hq : (addr - S0) / 2 < k
        · rw [if_pos (by omega : (addr - S0) / 2 < k + 1), if_pos hq]
        · rw [if_neg (by omega : ¬ (addr - S0) / 2 < k + 1), if_neg hq]

/-- **The source slot is already final**: `mem[S0 + a] = enc (eSeq a)` while the loop runs. -/
theorem expandMem_get {w M : ℕ} (S0 : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin M → ZMod 2) (t k a : ℕ) (ht : a / 2 < t) (hk : a % 2 = 1 → a / 2 < k) :
    expandMem S0 b y t k (S0 + a) = enc b (eSeq b y a) := by
  simp only [expandMem]
  rw [if_neg (by omega : ¬ S0 + a < S0)]
  rw [show S0 + a - S0 = a from by omega]
  have hmod2 : a % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_cases he : a % 2 = 0
  · rw [if_pos he, if_pos ht]
    conv_rhs => rw [show a = 2 * (a / 2) from by omega]
    rw [eSeq_even]
    exact (enc_payloadField b y (a / 2)).symm
  · rw [if_neg he, if_pos (hk (by omega))]
    conv_rhs => rw [show a = 2 * (a / 2) + 1 from by omega]

/-- The slot the expansion loop reads: `e[k]`. -/
theorem expandMem_src {w M : ℕ} (S0 : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin M → ZMod 2) (t k : ℕ) (hk : k < t) :
    expandMem S0 b y t k (S0 + k) = enc b (eSeq b y k) :=
  expandMem_get S0 b y t k k (by omega) (fun _ => by omega)

/-- **The array is complete**: after `t` iterations every slot `S0 + a`, `a < 2t`, holds the
integer spelling of `eSeq a`. -/
theorem expandMem_complete {w M : ℕ} (S0 : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin M → ZMod 2) (t : ℕ) {a : ℕ} (ha : a < 2 * t) :
    expandMem S0 b y t t (S0 + a) = enc b (eSeq b y a) :=
  expandMem_get S0 b y t t a (by omega) (fun _ => by omega)

@[simp] theorem expandBody_length : expandBody.length = 16 := by simp [expandBody]

@[simp] theorem expandLoopAt_length (base : ℕ) : (expandLoopAt base).length = 19 := by
  simp [expandLoopAt]

theorem expandLoopStmt_compile (base : ℕ) : Stmt.compile expandLoopStmt base = expandLoopAt base := by
  simp [Stmt.compile, Stmt.len, Cond.code, Cond.test, expandLoopAt, expandBody_length]

theorem expandLoopStmt_length (base : ℕ) : (Stmt.compile expandLoopStmt base).length = 19 := by
  rw [expandLoopStmt_compile, expandLoopAt_length]

/-- The three facts a compiled expansion loop provides. -/
theorem at_loop_expand {P : Program} {base : ℕ}
    (hAt : At P base (Stmt.compile expandLoopStmt base)) :
    P[base + 1]? = some (iJz r14 (base + 19)) ∧ At P (base + 2) expandBody ∧
      P[base + 18]? = some (iJmp base) := by
  have hlen := expandLoopStmt_length base
  refine ⟨?_, ?_, ?_⟩
  · have h := hAt 1 (by omega)
    rw [expandLoopStmt_compile] at h
    simpa [expandLoopAt] using h
  · intro r hr
    have hr16 : r < 16 := by rw [← expandBody_length]; exact hr
    have h := hAt (r + 2) (by omega)
    rw [expandLoopStmt_compile] at h
    have hlist : (expandLoopAt base)[r + 2]? = expandBody[r]? := by
      simp only [expandLoopAt]
      rw [List.append_assoc]
      rw [List.getElem?_append_right
        (by simp : ([iLt r14 r5 r0, iJz r14 (base + 19)]).length ≤ r + 2)]
      rw [show r + 2 - ([iLt r14 r5 r0, iJz r14 (base + 19)]).length = r from by simp]
      exact List.getElem?_append_left hr
    rw [hlist] at h
    rwa [show base + (r + 2) = base + 2 + r from by omega] at h
  · have h := hAt 18 (by omega)
    rw [expandLoopStmt_compile] at h
    simpa [expandLoopAt] using h

theorem expandState_regs_eq (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (expandState base S0 w t b y k).regs
      = ![t, w, S0, 2 ^ w - 1, detSqBase w, k, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8 * w] := rfl

@[simp] theorem expandState_r14 (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) : (expandState base S0 w t b y k).regs r14 = 0 := by
  rw [expandState_regs_eq]
  simp

/-- A loop-head state with its own program counter written back is unchanged. -/
theorem expandState_eta (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    ({ expandState base S0 w t b y k with pc := base } : RAMState) = expandState base S0 w t b y k := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp
  · simp
  · intro d; simp

/-- The loop test for the expansion loop. -/
theorem expandCond_eval (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    readCond.eval (expandState base S0 w t b y k) ↔ k < t := by
  simp [Cond.eval, expandState_regs_eq]

theorem expandCond_false (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) : ¬ readCond.eval (expandState base S0 w t b y t) := by
  rw [expandCond_eval]
  exact lt_irrefl t

/-- Running the expansion test. -/
theorem runBlock_expandCond (E : RAMEnv) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    runBlock readCond.code E (expandState base S0 w t b y k) = { pc := base + 1, regs := Function.update (expandState base S0 w t b y k).regs r14 ((if k < t then 1 else 0) % 2 ^ E.W), mem := expandMem S0 b y t k } := by
  have hcode : readCond.code = [iLt r14 r5 r0] := rfl
  rw [hcode, runBlock_cons, runBlock_nil, execInstr_lt]
  dsimp only [expandState]
  try rfl

theorem runBlock_expandCond_of_lt (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hW : 1 < 2 ^ E.W) (hk : k < t) :
    runBlock readCond.code E (expandState base S0 w t b y k) = { expandState base S0 w t b y k with pc := base + 1, regs := Function.update (expandState base S0 w t b y k).regs r14 1 } := by
  rw [runBlock_expandCond, if_pos hk, Nat.mod_eq_of_lt hW]
  try rfl

theorem runBlock_expandCond_of_ge (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hk : ¬ k < t) :
    runBlock readCond.code E (expandState base S0 w t b y k) = { expandState base S0 w t b y k with pc := base + 1, regs := Function.update (expandState base S0 w t b y k).regs r14 0 } := by
  rw [runBlock_expandCond, if_neg hk, Nat.zero_mod]
  try rfl

theorem runBlock_expandCond_exit (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) :
    runBlock readCond.code E (expandState base S0 w t b y t) = { expandState base S0 w t b y t with pc := base + 1 } := by
  have h0 : (expandState base S0 w t b y t).regs r14 = 0 := expandState_r14 base S0 w t b y t
  have h := runBlock_expandCond_of_ge E base S0 w t b y t (lt_irrefl t)
  rw [update_zero_eq _ h0] at h
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · rw [h]
  · rw [h]
  · intro d
    rw [h]

theorem expandBodyIn_eq (E : RAMEnv) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) (hW : 1 < 2 ^ E.W) (hk : k < t) :
    ({ runBlock readCond.code E (expandState base S0 w t b y k) with pc := base + readCond.code.length + 1 } : RAMState) = expandBodyIn base S0 w t b y k := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hrun := runBlock_expandCond_of_lt E base S0 w t b y k hW hk
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp only [expandBodyIn]
    rw [hcl]
  · simp only [expandBodyIn]
    rw [hrun]
    simp
  · intro d
    simp only [expandBodyIn]
    rw [hrun]

/-- **The expansion body, as a state map.**  It reads `e[k]`, squares it through the table at
`detSqBase`, stores the result at `S0 + 2k + 1`, advances the counter and clears the scratch
registers. -/
theorem expandBody_spec (E : RAMEnv) (base S0 w t k : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (s : RAMState)
    (hpc : s.pc = base + 2)
    (hregs : s.regs = Function.update (expandState base S0 w t b y k).regs r14 1)
    (hmem : s.mem = expandMem S0 b y t k)
    (hsrc : (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : expandMem S0 b y t k (S0 + k) = enc b (eSeq b y k))
    (hld : enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) :
    runBlock expandBody E s = { expandState base S0 w t b y (k + 1) with pc := base + 18 } := by
  have hpc' : (runBlock expandBody E s).pc = base + 18 := by
    rw [runBlock_pc expandBody E s (by simp [expandBody]), hpc, expandBody_length]
  refine ramState_eq_of _ _ hpc' ?_ ?_
  · funext addr
    show (runBlock expandBody E s).mem addr = expandMem S0 b y t (k + 1) addr
    by_cases h : addr = S0 + 2 * k + 1
    · rw [h, expandMem_succ, Function.update_self]
      simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add,
        hregs, expandState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        hsrc, hmem, execInstr_load, Function.update_self, hsrcval, hld, hsq, execInstr_qDet, htab, hval, hkk,
        hkkS0, Function.update_idem, haddr, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil]
    · rw [expandMem_succ, Function.update_of_ne h]
      simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add,
        hregs, expandState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        hsrc, hmem, execInstr_load, Function.update_self, hsrcval, hld, hsq, execInstr_qDet, htab, hval, hkk,
        hkkS0, Function.update_idem, haddr, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil,
        Function.update_of_ne h]
  · intro d
    simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add,
      hregs, expandState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
      hsrc, execInstr_load, Function.update_self, Nat.add_mod_mod, execInstr_qDet, hkk, hkkS0,
      Function.update_idem, haddr, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil]
    fin_cases d <;>
      simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add,
        hregs, expandState, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        hsrc, execInstr_load, Function.update_self, Nat.add_mod_mod, execInstr_qDet, hkk, hkkS0,
        Function.update_idem, haddr, execInstr_store, hk1, execInstr_imm, Nat.zero_mod, runBlock_nil,
        Fin.zero_eta, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
        Nat.add_left_cancel_iff]

/-- The expansion body as a `Sem` run. -/
theorem expandBody_sem (P : Program) (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hAt : At P (base + 2) expandBody)
    (hsrc : (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : expandMem S0 b y t k (S0 + k) = enc b (eSeq b y k))
    (hld : enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) :
    Sem P E (base + 2) (base + 18) (expandBodyIn base S0 w t b y k)
      (fun c s' => c = 16 ∧ s' = { expandState base S0 w t b y (k + 1) with pc := base + 18 }) := by
  refine Sem.mono (Sem.block P E (base + 2) expandBody (expandBodyIn base S0 w t b y k) hAt
    (by simp [expandBody]) rfl) ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hc, expandBody_length]
  · rw [hs]
    exact expandBody_spec E base S0 w t k b y (expandBodyIn base S0 w t b y k) rfl rfl rfl hsrc
      hsrcval hld hsq htab hval hkk hkkS0 haddr hk1

/-- The expansion iteration after the test: body entry back to the loop head, in 17 steps. -/
theorem expandBodyIter (P : Program) (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hAt : At P base (Stmt.compile expandLoopStmt base)) (hW : 1 < 2 ^ E.W) (hk : k < t)
    (hsrc : (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : expandMem S0 b y t k (S0 + k) = enc b (eSeq b y k))
    (hld : enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) :
    Sem P E (base + readCond.code.length + 1) base ({ runBlock readCond.code E (expandState base S0 w t b y k) with pc := base + readCond.code.length + 1 } : RAMState)
      (fun c s' => c = 17 ∧ s' = expandState base S0 w t b y (k + 1)) := by
  obtain ⟨hjz, hbodyAt, hjmp⟩ := at_loop_expand hAt
  have hbody := expandBody_sem P E base S0 w t b y k hbodyAt hsrc hsrcval hld hsq htab hval hkk hkkS0
    haddr hk1
  rw [expandBodyIn_eq E base S0 w t b y k hW hk]
  refine Sem.jmp_append (hAt := hjmp) ?_
  refine Sem.mono hbody ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨by omega, ?_⟩
  rw [hs]
  exact expandState_eta base S0 w t b y (k + 1)

/-- The exit state of the expansion loop. -/
theorem expandLoop_exit_state (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) :
    ({ runBlock readCond.code E (expandState base S0 w t b y t) with pc := base + readCond.code.length + (Stmt.code expandBody).len + 2 } : RAMState) = { expandState base S0 w t b y t with pc := base + 19 } := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hbl : (Stmt.code expandBody).len = 16 := expandBody_length
  have hrun := runBlock_expandCond_exit E base S0 w t b y
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp only [hcl, hbl]
  · simp only [hrun]
  · intro d
    simp only [hrun]

/-- **The expansion loop.**  One `Sem.loop` call, exactly as for the read loop. -/
theorem expandLoop_spec (P : Program) (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2)
    (hAt : At P base (Stmt.compile expandLoopStmt base)) (hW : 1 < 2 ^ E.W)
    (hsrc : ∀ k < t, (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : ∀ k < t, expandMem S0 b y t k (S0 + k) = enc b (eSeq b y k))
    (hld : ∀ k < t, enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : ∀ k < t, (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : ∀ k < t, E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : ∀ k < t, sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : ∀ k < t, (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : ∀ k < t, (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : ∀ k < t, (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1) :
    Sem P E base (base + 19) (expandState base S0 w t b y 0)
      (fun c s' => c ≤ 19 * t + 2 ∧ s' = { expandState base S0 w t b y t with pc := base + 19 }) := by
  have hloop := Sem.loop P E base readCond (Stmt.code expandBody) hAt hW t
    (fun j => expandState base S0 w t b y j) (fun _ => 17)
    (fun j => rfl)
    (fun j hj => (expandCond_eval base S0 w t b y j).mpr hj)
    (expandCond_false base S0 w t b y)
    (fun j hj => expandBodyIter P E base S0 w t b y j hAt hW hj (hsrc j hj) (hsrcval j hj) (hld j hj)
      (hsq j hj) (htab j hj) (hval j hj) (hkk j hj) (hkkS0 j hj) (haddr j hj) (hk1 j hj))
  have h19 : ((readCond.code.length + 1) + 17) = 19 := by
    rw [readCond_code_length]
  have hsum19 : (∑ j ∈ Finset.range t, (19 : ℕ)) = 19 * t := sum_range_const_mul t 19
  have hsum : (∑ j ∈ Finset.range t, ((readCond.code.length + 1) + 17)) = 19 * t := by
    rw [← hsum19]
    exact Finset.sum_congr rfl (fun j _ => h19)
  refine Sem.mono hloop ?_
  intro c s' hQ
  obtain ⟨hle, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hsum] at hle
    rw [readCond_code_length] at hle
    omega
  · rw [hs]
    exact expandLoop_exit_state E base S0 w t b y

/-- **The array is complete when the loop exits.**  The expansion trace above plus
`expandMem_complete`: after `t` iterations, every one of the `2t` syndrome slots holds the integer
spelling of `eSeq a`. -/
theorem expandLoop_result (P : Program) (E : RAMEnv) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2)
    (hAt : At P base (Stmt.compile expandLoopStmt base)) (hW : 1 < 2 ^ E.W)
    (hsrc : ∀ k < t, (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : ∀ k < t, expandMem S0 b y t k (S0 + k) = enc b (eSeq b y k))
    (hld : ∀ k < t, enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : ∀ k < t, (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : ∀ k < t, E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : ∀ k < t, sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : ∀ k < t, (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : ∀ k < t, (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : ∀ k < t, (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1) :
    Sem P E base (base + 19) (expandState base S0 w t b y 0)
      (fun c s' => c ≤ 19 * t + 2 ∧ s' = { expandState base S0 w t b y t with pc := base + 19 } ∧
        ∀ a, a < 2 * t → s'.mem (S0 + a) = enc b (eSeq b y a)) := by
  refine Sem.mono (expandLoop_spec P E base S0 w t b y hAt hW hsrc hsrcval hld hsq htab hval hkk
    hkkS0 haddr hk1) ?_
  intro c s' hQ
  obtain ⟨hle, hs⟩ := hQ
  refine ⟨hle, hs, ?_⟩
  intro a ha
  rw [hs]
  exact expandMem_complete S0 b y t ha

end Expand

section ExpandStd

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end ExpandStd

@[simp] theorem enc_zero {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) : enc b 0 = 0 := by
  simp [enc]

theorem writeArray_frame (B : ℕ) (m f : ℕ → ℕ) (n a : ℕ)
    (ha : a < B ∨ B + n ≤ a) : writeArray B m f n a = m a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [writeArray, Function.update_of_ne (by omega : a ≠ B + n)]
      exact ih (by omega)

theorem writeArray_get (B : ℕ) (m f : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    writeArray B m f n (B + i) = f i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : i = n
      · subst i
        simp [writeArray]
      · rw [writeArray, Function.update_of_ne (by omega : B + i ≠ B + n)]
        exact ih (by omega)

theorem copyBody_spec (E : RAMEnv) (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (j : ℕ) (hj : j < L) (hW : 1 < 2 ^ E.W) (hL : L < 2 ^ E.W)
    (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src)
    (hword : ∀ i < L, m (src + i) < 2 ^ E.W) :
    runBlock copyBody E { runBlock copyCond.code E (copyState pc dst src L m r j) with pc := pc + 2 } =
      { copyState pc dst src L m r (j + 1) with pc := pc + 11 } := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hsj : (src + j) % 2 ^ E.W = src + j := Nat.mod_eq_of_lt (by omega)
  have hdj : (dst + j) % 2 ^ E.W = dst + j := Nat.mod_eq_of_lt (by omega)
  have hj1 : (j + 1) % 2 ^ E.W = j + 1 := Nat.mod_eq_of_lt (by omega)
  have hm : writeArray dst m (fun i => m (src + i)) j (src + j) = m (src + j) :=
    writeArray_frame dst m _ j _ (by omega)
  have hv : m (src + j) % 2 ^ E.W = m (src + j) := Nat.mod_eq_of_lt (hword j hj)
  apply ramState_eq_of
  ·     simp only [copyBody, Fin.isValue, Cond.code, copyCond, copyState, runBlock_cons, execInstr, ↓reduceIte,
      one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
      Function.update_self, Nat.zero_mod, Nat.add_right_cancel_iff, Nat.add_left_cancel_iff] <;> omega
  ·     simp only [copyBody, Fin.isValue, Cond.code, copyCond, copyState, runBlock_cons, execInstr, ↓reduceIte,
      one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, hsj,
      Function.update_self, hm, hv, hdj, Nat.zero_mod, writeArray]
  · intro d
    fin_cases d <;>
      simp only [copyBody, Fin.isValue, Cond.code, copyCond, copyState, runBlock_cons, execInstr, ↓reduceIte,
        one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
        Function.update_self, hj1, Nat.zero_mod, Fin.zero_eta, Nat.add_left_cancel_iff, Fin.mk_one,
        Fin.reduceFinMk]

theorem copyCond_eval (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ) :
    copyCond.eval (copyState pc dst src L m r j) ↔ j < L := by
  simp [copyCond, Cond.eval, copyState]

theorem copyBodyIter (P : Program) (E : RAMEnv) (pc dst src L : ℕ)
    (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ) (hj : j < L)
    (hAt : At P pc (Stmt.compile copyStmt pc))
    (hW : 1 < 2 ^ E.W) (hL : L < 2 ^ E.W)
    (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src)
    (hword : ∀ i < L, m (src + i) < 2 ^ E.W) :
    Sem P E (pc + copyCond.code.length + 1) pc
      { runBlock copyCond.code E (copyState pc dst src L m r j) with pc := pc + copyCond.code.length + 1 }
      (fun k s' => k = 10 ∧ s' = copyState pc dst src L m r (j + 1)) := by
  obtain ⟨_, _, hbody, hjmp⟩ := at_loop hAt
  have hbodyAt : At P (pc + 2) copyBody := hbody
  have hjmpAt : P[pc + 11]? = some (iJmp pc) := hjmp
  have hrun : Sem P E (pc + 2) (pc + 11)
      { runBlock copyCond.code E (copyState pc dst src L m r j) with pc := pc + 2 }
      (fun k s' => k = 9 ∧ s' = { copyState pc dst src L m r (j + 1) with pc := pc + 11 }) := by
    refine Sem.mono (Sem.block P E (pc + 2) copyBody _ hbodyAt (by simp [copyBody]) rfl) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    refine ⟨hk, ?_⟩
    rw [hs]
    exact copyBody_spec E pc dst src L m r j hj hW hL hdst hsrc hdisj hword
  refine Sem.jmp_append (hAt := hjmpAt) (Sem.mono hrun ?_)
  intro k s' h
  obtain ⟨hk, hs⟩ := h
  refine ⟨by omega, ?_⟩
  rw [hs]
  rfl

theorem copyCond_exit (E : RAMEnv) (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) :
    ({ runBlock copyCond.code E (copyState pc dst src L m r L) with pc := pc + 12 } : RAMState) =
      { copyState pc dst src L m r L with pc := pc + 12 } := by
  apply ramState_eq_of
  · rfl
  · rfl
  · intro d
    fin_cases d <;> simp [copyCond, Cond.code, copyState, runBlock_cons, runBlock_nil, execInstr]

/-- Copy a disjoint word array, preserving every address outside the target. -/
theorem copyArray_spec (P : Program) (E : RAMEnv) (pc dst src L : ℕ)
    (m : ℕ → ℕ) (r : Fin 16 → ℕ) (hAt : At P pc (Stmt.compile copyStmt pc))
    (hW : 1 < 2 ^ E.W) (hL : L < 2 ^ E.W)
    (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src)
    (hword : ∀ i < L, m (src + i) < 2 ^ E.W) :
    Sem P E pc (pc + 12) (copyState pc dst src L m r 0)
      (fun k s' => k ≤ 12 * L + 2 ∧ s' = { copyState pc dst src L m r L with pc := pc + 12 }) := by
  have h := Sem.loop P E pc copyCond (.code copyBody) hAt hW L
    (fun j => copyState pc dst src L m r j) (fun _ => 10)
    (fun _ => rfl)
    (fun j hj => (copyCond_eval pc dst src L m r j).mpr hj)
    (fun hf => (Nat.lt_irrefl L) ((copyCond_eval pc dst src L m r L).mp hf))
    (fun j hj => copyBodyIter P E pc dst src L m r j hj hAt hW hL hdst hsrc hdisj hword)
  refine Sem.mono h ?_
  intro k s' hQ
  obtain ⟨hcost, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · have hsum : (∑ j ∈ Finset.range L, (copyCond.code.length + 1 + 10)) = 12 * L := by
      change (∑ j ∈ Finset.range L, (12 : ℕ)) = 12 * L
      exact sum_range_const_mul L 12
    rw [hsum] at hcost
    change k ≤ 2 + 12 * L at hcost
    omega
  · rw [hs]
    exact copyCond_exit E pc dst src L m r

theorem zeroRegs_spec (E : RAMEnv) (s : RAMState) :
    runBlock zeroRegsCode E s = boundaryState (s.pc + 16) s.mem := by
  apply ramState_eq_of
  ·     simp only [zeroRegsCode, Fin.isValue, runBlock_cons, execInstr, Nat.zero_mod, runBlock_nil,
      boundaryState, Nat.add_right_cancel_iff, Nat.add_left_cancel_iff] <;> omega
  · rfl
  · intro d
    fin_cases d <;>                     simp only [zeroRegsCode, Fin.isValue, runBlock_cons, execInstr, Nat.zero_mod,
                      runBlock_nil, Fin.zero_eta, ne_eq, Fin.reduceEq, not_false_eq_true,
                      Function.update_of_ne, zero_ne_one, Function.update_self, boundaryState, Fin.mk_one,
                      Fin.reduceFinMk]

/-- Read the two components of a compiled sequence inside a surrounding program. -/
theorem At.seqStmt {P : Program} {base : ℕ} {a b : Stmt}
    (h : At P base (Stmt.compile (.seq a b) base)) :
    At P base (Stmt.compile a base) ∧
      At P (base + a.len) (Stmt.compile b (base + a.len)) := by
  simpa only [Stmt.compile, At.append, Stmt.length_compile] using h

/-- Bounded-cost sequential composition with a state invariant. -/
theorem Sem.seq_bound {P : Program} {E : RAMEnv} {a b c A B : ℕ} {s : RAMState}
    {I J : RAMState → Prop}
    (h₁ : Sem P E a b s (fun k s' => k ≤ A ∧ I s'))
    (h₂ : ∀ s', s'.pc = b → I s' → Sem P E b c s' (fun k s'' => k ≤ B ∧ J s'')) :
    Sem P E a c s (fun k s' => k ≤ A + B ∧ J s') := by
  obtain ⟨hpc, k₁, s₁, hrun₁, hb, hcost₁, hI⟩ := h₁
  obtain ⟨_, k₂, s₂, hrun₂, hc, hcost₂, hJ⟩ := h₂ s₁ hb hI
  refine ⟨hpc, k₁ + k₂, s₂, ?_, hc, by omega, hJ⟩
  rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, hrun₁, hrun₂]

theorem decoderWorkspace_fits {w t : ℕ} (hw : 1 ≤ w) (ht : t < 2 ^ w) :
    decoderWorkspaceEnd t < 2 ^ (8 * w) := by
  let q : ℕ := 2 ^ w
  change t < q at ht
  have hq : 2 ≤ q := by
    have h := Nat.pow_le_pow_right (n := 2) (by norm_num) hw
    exact h
  have ht1 : t + 1 ≤ q := by omega
  have hsq : (t + 1) * (t + 1) ≤ q * q := Nat.mul_le_mul ht1 ht1
  have hq2 : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq
  have hq4 : 4 ≤ q * q := by
    simpa using Nat.mul_le_mul hq hq
  have hfirst : decoderWorkspaceEnd t ≤ 8 * q * q + 48 * q + 104 := by
    unfold decoderWorkspaceEnd
    nlinarith only [hsq, ht1]
  have hsecond : 8 * q * q + 48 * q + 104 ≤ 58 * q * q := by
    nlinarith only [hq2, hq4]
  have hthird : 58 * q * q < 64 * q * q := by
    have hp : 0 < q * q := Nat.mul_pos (by omega) (by omega)
    nlinarith only [hp]
  have hpow : 64 * q * q = 2 ^ (w + w + 6) := by
    dsimp only [q]
    rw [Nat.pow_add, Nat.pow_add]
    norm_num <;> ring
  have hupper : (2 : ℕ) ^ (w + w + 6) ≤ 2 ^ (8 * w) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlower : decoderWorkspaceEnd t < 64 * q * q :=
    lt_of_le_of_lt hfirst (lt_of_le_of_lt hsecond hthird)
  rw [hpow] at hlower
  exact lt_of_lt_of_le hlower hupper

/-- Clear registers at a straight-line boundary without changing memory. -/
theorem Sem.zero_block (P : Program) (E : RAMEnv) (pc : ℕ) (s : RAMState)
    (hAt : At P pc zeroRegsCode) (hpc : s.pc = pc) :
    Sem P E pc (pc + 16) s (fun k z => k ≤ 16 ∧ z = boundaryState (pc + 16) s.mem) := by
  refine Sem.mono (Sem.block P E pc zeroRegsCode s hAt (by simp [zeroRegsCode]) hpc) ?_
  intro k z hQ
  obtain ⟨hk, hz⟩ := hQ
  refine ⟨by change k = 16 at hk; omega, ?_⟩
  rw [hz, zeroRegs_spec, hpc]

/-- A straight-line block can be placed at any program counter. -/
theorem runBlock_replace_pc (code : List Instr) (E : RAMEnv) (s : RAMState) (pc : ℕ) (hn : NoBranch code) :
    runBlock code E { s with pc := pc } = { runBlock code E s with pc := pc + code.length } := by
  induction code generalizing s pc with
  | nil => rfl
  | cons i code ih =>
      obtain ⟨hni, hnc⟩ := hn
      have hi : execInstr i E { s with pc := pc } = { execInstr i E s with pc := pc + 1 } := by
        cases i <;> simp_all [Instr.NoBranchI, execInstr]
      simp only [runBlock_cons, hi]
      rw [ih _ _ hnc]
      apply ramState_eq_of
      · simp only [List.length_cons]
        omega
      · rfl
      · intro _; rfl

/-- Reuse the verified header reader at the embedding address. -/
theorem paramBodyAt_spec (E : RAMEnv) (base N t w S0 : ℕ) (y : Fin (t * w) → ZMod 2)
    (hS0 : S0 = wordsOf (8 * w) (t * w)) (hW : E.W = 8 * w) (hw1 : 1 ≤ w)
    (h0 : E.det 0 % 2 ^ E.W = t) (h1 : E.det 1 % 2 ^ E.W = w) (h4 : E.det 4 % 2 ^ E.W = S0)
    (h5 : E.det 5 % 2 ^ E.W = 2 ^ w - 1) (h6 : E.det 6 % 2 ^ E.W = detSqBase w)
    (h12 : E.det 12 % 2 ^ E.W = 8 * w) (h1W : (1 : ℕ) % 2 ^ E.W = 1) :
    runBlock paramBody E { decoderStart (8 * w) y [] with pc := base } = readState (base + 14) S0 w t y 0 := by
  rw [runBlock_replace_pc paramBody E _ base (by simp [paramBody]),
    paramBody_spec E N t w S0 y hS0 hW hw1 h0 h1 h4 h5 h6 h12 h1W]
  rfl

theorem inputRead_spec {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (P : Program) (base N t w : ℕ) (y : Fin (t * w) → ZMod 2)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile inputReadStmt base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : DetAgrees E t N b ι) :
    Sem P E base (base + 33) { decoderStart (8 * w) y [] with pc := base }
      (fun k z => k ≤ 19 * t + 16 ∧
        z = { readState (base + 14) (wordsOf (8 * w) (t * w)) w t y t with pc := base + 33 }) := by
  have hpos : 0 < w := by omega
  have h2w : (2 : ℕ) ^ w ≤ 2 ^ (8 * w) :=
    Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : w ≤ 8 * w)
  have htW : t < 2 ^ (8 * w) := lt_of_le_of_lt htN (lt_of_lt_of_le hNw h2w)
  have hwW : w < 2 ^ (8 * w) := lt_of_lt_of_le (Nat.lt_two_pow_self (n := w)) h2w
  have hS0W : wordsOf (8 * w) (t * w) < 2 ^ (8 * w) :=
    lt_of_le_of_lt (wordsOf_le w t hw1) htW
  have hmaskW : 2 ^ w - 1 < 2 ^ (8 * w) := by
    have := Nat.two_pow_pos w
    omega
  have h1E : (1 : ℕ) < 2 ^ E.W := by
    rw [hW]
    have h0 : 0 < 8 * w := by omega
    have h := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h0
    simpa using h
  -- the six header reads
  have h0 : E.det 0 % 2 ^ E.W = t := by
    rw [hdet.1 0 (by decide), detStd_hdr t N w b ι (by norm_num : (0 : ℕ) < 13), hdrTab_zero, hW]
    exact Nat.mod_eq_of_lt htW
  have h1 : E.det 1 % 2 ^ E.W = w := by
    rw [hdet.1 1 (by decide), detStd_hdr t N w b ι (by norm_num : (1 : ℕ) < 13), hdrTab_one, hW]
    exact Nat.mod_eq_of_lt hwW
  have h4 : E.det 4 % 2 ^ E.W = wordsOf (8 * w) (t * w) := by
    rw [hdet.1 4 (by decide), detStd_hdr t N w b ι (by norm_num : (4 : ℕ) < 13), hdrTab_four, hW]
    exact Nat.mod_eq_of_lt hS0W
  have h5 : E.det 5 % 2 ^ E.W = 2 ^ w - 1 := by
    rw [hdet.1 5 (by decide), detStd_hdr t N w b ι (by norm_num : (5 : ℕ) < 13), hdrTab_five, hW]
    exact Nat.mod_eq_of_lt hmaskW
  have h6 : E.det 6 % 2 ^ E.W = detSqBase w := by
    rw [hdet.1 6 (by decide), detStd_hdr t N w b ι (by norm_num : (6 : ℕ) < 13), hdrTab_six, hW]
    exact Nat.mod_eq_of_lt (detSqBase_lt hw1)
  have h12 : E.det 12 % 2 ^ E.W = 8 * w := by
    rw [hdet.1 12 (by decide), detStd_hdr t N w b ι (by norm_num : (12 : ℕ) < 13), hdrTab_twelve, hW]
    exact Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := 8 * w))
  have h1W : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt h1E
  -- per-iteration arithmetic
  have hmul : ∀ k < t, k * w % 2 ^ E.W = k * w := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (mul_lt_two_pow_eight hw1 hNw (lt_of_lt_of_le hk htN))
  have hdiv : ∀ k < t, k * w / (8 * w) % 2 ^ E.W = k / 8 := by
    intro k hk
    rw [mul_div_eight w hpos k, hW]
    refine Nat.mod_eq_of_lt ?_
    calc k / 8 ≤ k := Nat.div_le_self _ _
      _ < 2 ^ w := by omega
      _ ≤ 2 ^ (8 * w) := h2w
  have hmod : ∀ k < t, k * w % (8 * w) % 2 ^ E.W = k % 8 * w := by
    intro k hk
    rw [mul_mod_eight, hW]
    refine Nat.mod_eq_of_lt ?_
    calc k % 8 * w ≤ 7 * w := Nat.mul_le_mul_right w (by
          have := Nat.mod_lt k (by norm_num : (0 : ℕ) < 8)
          omega)
      _ < 8 * w := by omega
      _ ≤ 2 ^ (8 * w) := le_of_lt (Nat.lt_two_pow_self (n := 8 * w))
  have haddr : ∀ k < t, (wordsOf (8 * w) (t * w) + 2 * k) % 2 ^ E.W
      = wordsOf (8 * w) (t * w) + 2 * k := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (addr_lt_two_pow_eight hw1
      (lt_of_le_of_lt htN hNw) (wordsOf_le w t hw1) hk)
  have hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1 := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h1' : k + 1 ≤ t := by omega
    omega
  have hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1 := by
    rw [hW]
    exact Nat.mod_eq_of_lt hmaskW
  have hword : ∀ k < t, k / 8 < wordsOf (8 * w) (t * w) := by
    intro k hk
    rw [wordsOf_eight w t hpos]
    omega
  have hpk : ∀ k < t, packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8) := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (packMem_lt hpos y (k / 8))
  obtain ⟨hParamAt, hLoopAt⟩ := At.seqStmt hAt
  have hPro : Sem P E base (base + 14) { decoderStart (8 * w) y [] with pc := base }
      (fun k z => k ≤ 14 ∧ z = readState (base + 14) (wordsOf (8 * w) (t * w)) w t y 0) := by
    refine Sem.mono (Sem.block P E base paramBody _ hParamAt (by simp [paramBody]) rfl) ?_
    intro k z hQ
    have hk : k = 14 := hQ.1
    exact ⟨by omega, hQ.2.trans (paramBodyAt_spec E base N t w (wordsOf (8 * w) (t * w)) y rfl
      hW hw1 h0 h1 h4 h5 h6 h12 h1W)⟩
  have hLoop := readLoop_spec P E (base + 14) (wordsOf (8 * w) (t * w)) w t y hLoopAt
    h1E hW (by rw [hW]; omega) hpos hmul hdiv hmod haddr hk1 hmask hword hpk
  have hFull := Sem.seq_bound hPro (fun z _ hz => by subst z; exact hLoop)
  exact Sem.mono hFull (fun k z hQ => ⟨by omega, hQ.2⟩)

theorem expandAt_spec {F : Type} [Field F] [Algebra (ZMod 2) F]
    (P : Program) (E : RAMEnv) (N t w base : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile expandLoopStmt base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : DetAgrees E t N b ι) :
    Sem P E base (base + 19) (expandState base (wordsOf (8 * w) (t * w)) w t b y 0)
      (fun k z => k ≤ 19 * t + 2 ∧
        z = { expandState base (wordsOf (8 * w) (t * w)) w t b y t with pc := base + 19 } ∧
        ∀ a, a < 2 * t → z.mem (wordsOf (8 * w) (t * w) + a) = enc b (eSeq b y a)) := by
  have hpos : 0 < w := by omega
  have h2w : (2 : ℕ) ^ w ≤ 2 ^ (8 * w) :=
    Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : w ≤ 8 * w)
  have htW : t < 2 ^ (8 * w) := lt_of_le_of_lt htN (lt_of_lt_of_le hNw h2w)
  have hS0t : wordsOf (8 * w) (t * w) ≤ t := wordsOf_le w t hw1
  have h1E : (1 : ℕ) < 2 ^ E.W := by
    rw [hW]
    have h0 : 0 < 8 * w := by omega
    have h := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h0
    simpa using h
  -- the per-iteration side conditions
  have hsrc : ∀ k < t, (wordsOf (8 * w) (t * w) + k) % 2 ^ E.W = wordsOf (8 * w) (t * w) + k := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h1 : wordsOf (8 * w) (t * w) + k < 2 ^ w + 2 ^ w := by omega
    calc wordsOf (8 * w) (t * w) + k < 2 ^ w + 2 ^ w := h1
      _ = 2 ^ (w + 1) := by rw [Nat.pow_succ]; ring
      _ ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have henc : ∀ k < t, enc b (eSeq b y k) < 2 ^ E.W := by
    intro k hk
    rw [hW]
    exact lt_of_lt_of_le (enc_lt b _) h2w
  have hsrcval : ∀ k < t, expandMem (wordsOf (8 * w) (t * w)) b y t k
      (wordsOf (8 * w) (t * w) + k) = enc b (eSeq b y k) := by
    intro k hk
    exact expandMem_src (wordsOf (8 * w) (t * w)) b y t k hk
  have hld : ∀ k < t, enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k) := by
    intro k hk
    exact Nat.mod_eq_of_lt (henc k hk)
  have hsq : ∀ k < t,
      (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k) := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (detSqBase_add_lt hw1 (enc_lt b _))
  have htab : ∀ k < t,
      E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)) := by
    intro k hk
    rw [hdet.2 _ (by have h := detMulBase_le_detSqBase w; omega), detStd_sq t N w b ι (enc_lt b _), hW]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (enc_lt b _) h2w)
  have hval : ∀ k < t, sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)) := by
    intro k hk
    exact sqTab_enc b y k
  have hkk : ∀ k < t, (k + k) % 2 ^ E.W = k + k := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h1 : k + k < 2 ^ w + 2 ^ w := by omega
    calc k + k < 2 ^ w + 2 ^ w := h1
      _ = 2 ^ (w + 1) := by rw [Nat.pow_succ]; ring
      _ ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkkS0 : ∀ k < t,
      (k + k + wordsOf (8 * w) (t * w)) % 2 ^ E.W = wordsOf (8 * w) (t * w) + 2 * k := by
    intro k hk
    have h := addr_lt_two_pow_eight (w := w) (t := t) (k := k)
      (S0 := wordsOf (8 * w) (t * w)) hw1 (lt_of_le_of_lt htN hNw) hS0t hk
    have h2 : k + k + wordsOf (8 * w) (t * w) = wordsOf (8 * w) (t * w) + 2 * k := by omega
    rw [h2, hW]
    exact Nat.mod_eq_of_lt h
  have haddr : ∀ k < t,
      (wordsOf (8 * w) (t * w) + 2 * k + 1) % 2 ^ E.W = wordsOf (8 * w) (t * w) + 2 * k + 1 := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (addr_succ_lt_two_pow_eight hw1 (lt_of_le_of_lt htN hNw) hS0t hk)
  have hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1 := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h2 : k + 1 ≤ t := by omega
    omega
  exact expandLoop_result P E base (wordsOf (8 * w) (t * w)) w t b y
    hAt
    h1E hsrc hsrcval hld hsq htab hval hkk hkkS0 haddr hk1

theorem readToExpansion_spec {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (readBase pc S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) :
    runBlock [iImm r5 0] E { readState readBase S0 w t y t with pc := pc } = expandState (pc + 1) S0 w t b y 0 := by
  apply ramState_eq_of
  · rfl
  · exact (expandMem_zero S0 b y t).symm
  · intro r
    fin_cases r <;> simp [runBlock_cons, runBlock_nil, execInstr, readState, expandState]

/-- The expanded input writes no words beyond the 2t coefficient array. -/
theorem expandMem_after_zero {F : Type} [Field F] [Algebra (ZMod 2) F] {w M : ℕ}
    (S0 : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin M → ZMod 2) (t addr : ℕ)
    (haddr : S0 + 2 * t ≤ addr) : expandMem S0 b y t t addr = 0 := by
  have h0 : ¬ addr < S0 := by omega
  have h1 : ¬ (addr - S0) / 2 < t := by omega
  simp [expandMem, h0, h1]

theorem inputFront_spec {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (P : Program) (base N t w : ℕ) (y : Fin (t * w) → ZMod 2)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile inputFrontStmt base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : DetAgrees E t N b ι) :
    Sem P E base (base + 69) { decoderStart (8 * w) y [] with pc := base }
      (fun k z => k ≤ 38 * t + 35 ∧
        z = boundaryState (base + 69) (expandMem (wordsOf (8 * w) (t * w)) b y t t) ∧
        FieldArrayStored b z.mem (wordsOf (8 * w) (t * w)) (2 * t) (eSeq b y) ∧
        ∀ addr, wordsOf (8 * w) (t * w) + 2 * t ≤ addr → z.mem addr = 0) := by
  let S0 := wordsOf (8 * w) (t * w)
  obtain ⟨hReadAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hResetAt, hRest2At⟩ := At.seqStmt hRestAt
  obtain ⟨hExpandAt, hZeroAt⟩ := At.seqStmt hRest2At
  have hRead := inputRead_spec E P base N t w y b ι hReadAt hW hw1 hNw htN hdet
  have hReset : Sem P E (base + 33) (base + 34)
      { readState (base + 14) S0 w t y t with pc := base + 33 }
      (fun k z => k ≤ 1 ∧ z = expandState (base + 34) S0 w t b y 0) := by
    refine Sem.mono (Sem.block P E (base + 33) [iImm r5 0] _ hResetAt (by simp) rfl) ?_
    intro k z hQ
    have hk : k = 1 := hQ.1
    exact ⟨by omega, hQ.2.trans (readToExpansion_spec E (base + 14) (base + 33) S0 w t b y)⟩
  have hExpand := expandAt_spec P E N t w (base + 34) b y ι hExpandAt hW hw1 hNw htN hdet
  have hExpandExact : Sem P E (base + 34) (base + 53) (expandState (base + 34) S0 w t b y 0)
      (fun k z => k ≤ 19 * t + 2 ∧ z = { expandState (base + 34) S0 w t b y t with pc := base + 53 }) :=
    Sem.mono hExpand (fun _ _ hQ => ⟨hQ.1, hQ.2.1⟩)
  have hZero := Sem.zero_block P E (base + 53)
    { expandState (base + 34) S0 w t b y t with pc := base + 53 } hZeroAt rfl
  have hFull := Sem.seq_bound hRead (fun z _ hz => by
    subst z
    exact Sem.seq_bound hReset (fun z _ hz => by
      subst z
      exact Sem.seq_bound hExpandExact (fun z _ hz => by subst z; exact hZero)))
  refine Sem.mono hFull ?_
  intro k z hQ
  refine ⟨by omega, hQ.2, ?_, ?_⟩
  · rw [hQ.2]
    intro j hj
    exact expandMem_complete S0 b y t hj
  · rw [hQ.2]
    intro addr ha
    exact expandMem_after_zero S0 b y t addr ha

theorem decoderAllocEnd_eq (t : ℕ) : decoderAllocEnd t = 8 * t * t + 44 * t + 144 := by
  unfold decoderAllocEnd decoderVerifyBase decoderOutputBase decoderQueue1 decoderQueue0 decoderRowBase
    decoderSavedBase decoderCapacity decoderLength
  ring

theorem decoderAllocEnd_fits (t w : ℕ) (hw : 1 ≤ w) (ht : t < 2 ^ w) : decoderAllocEnd t < 2 ^ (8 * w) := by
  have h := decoderWorkspace_fits hw ht
  rw [decoderAllocEnd_eq]
  dsimp [decoderWorkspaceEnd] at h
  omega

theorem saveHeader_spec (E : RAMEnv) (s : RAMState) (t S0 : ℕ)
    (hmeta : (128 : ℕ) < 2 ^ E.W) (ht : 2 * t < 2 ^ E.W)
    (h0 : E.det 0 % 2 ^ E.W = t) (h4 : E.det 4 % 2 ^ E.W = S0) :
    runBlock saveHeaderCode E s =
      { s with pc := s.pc + 5, regs := Function.update (Function.update (Function.update s.regs r1 (2 * t)) r3 S0) r14 4 } := by
  have hsmall (i : ℕ) (hi : i ≤ 128) : i % 2 ^ E.W = i := Nat.mod_eq_of_lt (by omega)
  have h2t : (t + t) % 2 ^ E.W = 2 * t := by rw [show t + t = 2 * t by omega, Nat.mod_eq_of_lt ht]
  apply ramState_eq_of
  · simp [saveHeaderCode, runBlock_cons, runBlock_nil, execInstr] <;> omega
  · rfl
  · intro r
    fin_cases r <;> simp [saveHeaderCode, runBlock_cons, runBlock_nil, execInstr, hsmall, h0, h4, h2t]

theorem saveDestination_spec (E : RAMEnv) (s : RAMState) (t : ℕ)
    (hmeta : (128 : ℕ) < 2 ^ E.W) (hB : decoderSavedBase t < 2 ^ E.W)
    (h0 : E.det 0 % 2 ^ E.W = t) :
    runBlock saveDestinationCode E s =
      { s with pc := s.pc + 8, regs := Function.update (Function.update (Function.update s.regs r2 (decoderSavedBase t)) r4 1) r14 0 } := by
  have hsmall (i : ℕ) (hi : i ≤ 128) : i % 2 ^ E.W = i := Nat.mod_eq_of_lt (by omega)
  have hmul : (t * 3) % 2 ^ E.W = t * 3 := Nat.mod_eq_of_lt (by dsimp [decoderSavedBase] at hB; omega)
  have hadd : (t * 3 + 128) % 2 ^ E.W = decoderSavedBase t := by
    rw [show t * 3 + 128 = decoderSavedBase t by unfold decoderSavedBase; omega, Nat.mod_eq_of_lt hB]
  apply ramState_eq_of
  ·     simp only [saveDestinationCode, Fin.isValue, runBlock_cons, execInstr, Nat.zero_mod,
      Function.update_self, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Nat.mul_mod_mod,
      Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod, runBlock_nil, Nat.add_right_cancel_iff,
      Nat.add_left_cancel_iff] <;> omega
  · rfl
  · intro r
    fin_cases r <;>                     simp only [saveDestinationCode, Fin.isValue, runBlock_cons, execInstr, zero_le, hsmall,
                      Function.update_self, h0, Nat.reduceLeDiff, ne_eq, Fin.reduceEq, not_false_eq_true,
                      Function.update_of_ne, hmul, Std.le_refl, hadd, Nat.one_le_ofNat, runBlock_nil,
                      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]

theorem saveArgs_spec (E : RAMEnv) (pc S0 t : ℕ) (m : ℕ → ℕ)
    (hmeta : (128 : ℕ) < 2 ^ E.W) (ht : 2 * t < 2 ^ E.W) (hB : decoderSavedBase t < 2 ^ E.W)
    (h0 : E.det 0 % 2 ^ E.W = t) (h4 : E.det 4 % 2 ^ E.W = S0) :
    runBlock saveArgsCode E (boundaryState pc m) = copyState (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) 0 := by
  rw [saveArgsCode, runBlock_append, saveHeader_spec E _ t S0 hmeta ht h0 h4, saveDestination_spec E _ t hmeta hB h0]
  apply ramState_eq_of
  · rfl
  · rfl
  · intro r
    fin_cases r <;> simp [boundaryState, copyState]

theorem saveSyndromeProcedure_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (P : Program) (E : RAMEnv) (pc S0 t : ℕ) (e : ℕ → F) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile saveSyndromeProcedure pc))
    (hmeta : (128 : ℕ) < 2 ^ E.W) (hwe : w ≤ E.W)
    (hS0 : S0 ≤ t) (hword : decoderSavedBase t + 2 * t ≤ 2 ^ E.W) (hBfit : decoderSavedBase t < 2 ^ E.W)
    (h0 : E.det 0 % 2 ^ E.W = t) (h4 : E.det 4 % 2 ^ E.W = S0)
    (hsums : FieldArrayStored b m S0 (2 * t) e) (htail : ∀ addr, S0 + 2 * t ≤ addr → m addr = 0) :
    Sem P E pc (pc + 41) (boundaryState pc m)
      (fun k z => k ≤ 12 * (2 * t) + 31 ∧
        z = boundaryState (pc + 41) (writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t)) ∧
        FieldArrayStored b z.mem (decoderSavedBase t) (2 * t) e ∧
        ∀ addr, decoderSavedBase t + 2 * t ≤ addr → z.mem addr = 0) := by
  have hlen : 2 * t < 2 ^ E.W := by
    have hb : 128 ≤ decoderSavedBase t := by unfold decoderSavedBase; omega
    omega
  have hsrc : S0 + 2 * t ≤ 2 ^ E.W := by dsimp [decoderSavedBase] at hword; omega
  have hdisj : S0 + 2 * t ≤ decoderSavedBase t := by unfold decoderSavedBase; omega
  obtain ⟨hArgsAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hCopyAt, hZeroAt⟩ := At.seqStmt hRestAt
  have hArgs : Sem P E pc (pc + 13) (boundaryState pc m)
      (fun k z => k ≤ 13 ∧ z = copyState (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) 0) := by
    refine Sem.mono (Sem.block P E pc saveArgsCode _ hArgsAt (by simp [saveArgsCode, saveHeaderCode, saveDestinationCode]) rfl) ?_
    intro k z hQ
    have hk : k = 13 := hQ.1
    exact ⟨by omega, hQ.2.trans (saveArgs_spec E pc S0 t m hmeta hlen hBfit h0 h4)⟩
  have hCopy := copyArray_spec P E (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) hCopyAt (by omega)
    hlen hword hsrc (Or.inl hdisj) (by
      intro j hj
      rw [hsums j hj]
      exact lt_of_lt_of_le (enc_lt b _) (Nat.pow_le_pow_right (by norm_num) hwe))
  have hZero := Sem.zero_block P E (pc + 25)
    { copyState (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) (2 * t) with pc := pc + 25 } hZeroAt rfl
  have hFull := Sem.seq_bound hArgs (fun z _ hz => by
    subst z
    exact Sem.seq_bound hCopy (fun z _ hz => by subst z; exact hZero))
  refine Sem.mono hFull ?_
  intro k z hQ
  refine ⟨by omega, hQ.2, ?_, ?_⟩
  · rw [hQ.2]
    change FieldArrayStored b (writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t)) (decoderSavedBase t) (2 * t) e
    intro j hj
    rw [writeArray_get _ _ _ (2 * t) j hj]
    exact hsums j hj
  · rw [hQ.2]
    change ∀ addr, decoderSavedBase t + 2 * t ≤ addr → writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t) addr = 0
    intro addr ha
    rw [writeArray_frame _ _ _ _ addr (Or.inr ha)]
    apply htail
    dsimp [decoderSavedBase] at ha
    omega

theorem syndromePoly_coeff {F : Type} [Field F] (e : ℕ → F) (t j : ℕ) :
    (syndromePoly e t).coeff j = if j < 2 * t then e j else 0 := by
  classical
  simp [syndromePoly, Polynomial.coeff_C_mul_X_pow, eq_comm]

theorem saved_syndrome_polynomial {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (t : ℕ) (e : ℕ → F) (m : ℕ → ℕ)
    (hstored : FieldArrayStored b m (decoderSavedBase t) (2 * t) e)
    (htail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → m addr = 0) :
    PolynomialStored b m (decoderSavedBase t) (decoderCapacity t) (syndromePoly e t) := by
  intro j hj
  rw [syndromePoly_coeff]
  by_cases h : j < 2 * t
  · rw [if_pos h]
    exact hstored j h
  · rw [if_neg h, enc_zero]
    exact htail _ (by omega)

section PinBits

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end PinBits

section Uniqueness

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end Uniqueness

section Slp

variable {F : Type} [Field F]

end Slp


open LinearSetReconciliation327.Main in
theorem LinearSetReconciliation327.Main.pinsketch_decoder_read
    {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (P : Program) (base N t w : ℕ) (y : Fin (t * w) → ZMod 2)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile inputSavedProcedure base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : DetAgrees E t N b ι) :
    Sem P E base (base + 110) { decoderStart (8 * w) y [] with pc := base }
      (fun k z => k ≤ 62 * t + 66 ∧ ∃ m', z = boundaryState (base + 110) m' ∧
        FieldArrayStored b m' (decoderSavedBase t) (2 * t) (eSeq b y) ∧
        PolynomialStored b m' (decoderSavedBase t) (decoderCapacity t) (syndromePoly (eSeq b y) t) ∧
        ∀ addr, decoderSavedBase t + 2 * t ≤ addr → m' addr = 0) := by
  let S0 := wordsOf (8 * w) (t * w)
  let m1 := expandMem S0 b y t t
  have hAlloc : decoderAllocEnd t < 2 ^ E.W := by
    rw [hW]
    exact decoderAllocEnd_fits t w hw1 (lt_of_le_of_lt htN hNw)
  have hEBword : decoderSavedBase t + 2 * t ≤ 2 ^ E.W := by
    have hE : decoderSavedBase t + 2 * t ≤ decoderAllocEnd t := by
      unfold decoderAllocEnd decoderVerifyBase decoderOutputBase decoderQueue1 decoderQueue0 decoderRowBase
      omega
    omega
  have hEBfit : decoderSavedBase t < 2 ^ E.W := by
    have he : decoderSavedBase t ≤ decoderAllocEnd t := by
      unfold decoderAllocEnd decoderVerifyBase decoderOutputBase decoderQueue1 decoderQueue0 decoderRowBase
      omega
    omega
  have hmeta : (128 : ℕ) < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : 128 < 2 ^ 8) hp
  have hS0 : S0 ≤ t := wordsOf_le w t hw1
  have h0 : E.det 0 % 2 ^ E.W = t := by
    rw [hdet.1 0 (by decide), detStd_hdr t N w b ι (by norm_num : 0 < 13), hdrTab_zero,
      Nat.mod_eq_of_lt (by omega)]
  have h4 : E.det 4 % 2 ^ E.W = S0 := by
    rw [hdet.1 4 (by decide), detStd_hdr t N w b ι (by norm_num : 4 < 13), hdrTab_four,
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hFrontAt, hSaveAt⟩ := At.seqStmt hAt
  have hFront := inputFront_spec E P base N t w y b ι hFrontAt hW hw1 hNw htN hdet
  have hFrontExact : Sem P E base (base + 69) { decoderStart (8 * w) y [] with pc := base }
      (fun k z => k ≤ 38 * t + 35 ∧ z = boundaryState (base + 69) m1) :=
    Sem.mono hFront (fun k z hQ => ⟨hQ.1, hQ.2.1⟩)
  have hValues : FieldArrayStored b m1 S0 (2 * t) (eSeq b y) := by intro j hj; exact expandMem_complete S0 b y t hj
  have hTail : ∀ addr, S0 + 2 * t ≤ addr → m1 addr = 0 := expandMem_after_zero S0 b y t
  have hSave := saveSyndromeProcedure_spec b P E (base + 69) S0 t (eSeq b y) m1 hSaveAt hmeta (by omega)
    hS0 hEBword hEBfit h0 h4 hValues hTail
  have hFull := Sem.seq_bound hFrontExact (fun z _ hz => by subst z; exact hSave)
  refine Sem.mono hFull ?_
  intro k z hQ
  obtain ⟨hk, hz, hsums, htail⟩ := hQ
  let m2 := writeArray (decoderSavedBase t) m1 (fun i => m1 (S0 + i)) (2 * t)
  have hValues2 : FieldArrayStored b m2 (decoderSavedBase t) (2 * t) (eSeq b y) := by simpa [hz, boundaryState, m2] using hsums
  have hTail2 : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → m2 addr = 0 := by simpa [hz, boundaryState, m2] using htail
  exact ⟨by omega, m2, hz, hValues2, saved_syndrome_polynomial b t (eSeq b y) m2 hValues2 hTail2, hTail2⟩

/-! Child C3: `LinearSetReconciliation327.Main.pinsketch_decoder_key_solver`.

Generated by `p21opt/gen/emit.py` by skeleton subtraction from
`Solutions/_p21_opt3.lean` (Stage-2 declaration spans). -/

set_option autoImplicit false

open scoped ENNReal
open Finset Polynomial


section FieldFacts

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end FieldFacts

section PowerSums

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

variable {N : ℕ}

end PowerSums

theorem pdec_X_pow_dvd_eq_zero {F : Type} [Field F] {n : ℕ} {f : F[X]}
    (h : X ^ n ∣ f) (hdeg : f.natDegree < n) : f = 0 := by
  rw [X_pow_dvd_iff] at h
  ext d
  simp only [coeff_zero]
  by_cases hd : d < n
  · exact h d hd
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- Cross-multiplied uniqueness of the pair `(σ, ω)` in the key equation `σ S ≡ ω (mod X^{2t})`:
both products `σ ω'` and `σ' ω` have degree `< 2t`, and `X ^ (2t)` divides their difference. -/
theorem key_equation_unique {F : Type} [Field F] (S : F[X]) (t : ℕ) {σ ω σ' ω' : F[X]}
    (hσ : σ ≠ 0) (hσ' : σ' ≠ 0)
    (hdegσ : σ.natDegree ≤ t) (hdegσ' : σ'.natDegree ≤ t)
    (hdegω : ω.natDegree < t) (hdegω' : ω'.natDegree < t)
    (h : X ^ (2 * t) ∣ σ * S - ω) (h' : X ^ (2 * t) ∣ σ' * S - ω') :
    σ * ω' = σ' * ω := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := h'
  have e1 : σ * S = ω + X ^ (2 * t) * u := by rw [← hu]; ring
  have e2 : σ' * S = ω' + X ^ (2 * t) * v := by rw [← hv]; ring
  have h4 : σ' * ω + X ^ (2 * t) * (σ' * u) = σ * ω' + X ^ (2 * t) * (σ * v) := by
    calc σ' * ω + X ^ (2 * t) * (σ' * u)
        = σ' * (ω + X ^ (2 * t) * u) := by ring
      _ = σ' * (σ * S) := by rw [e1]
      _ = σ * (σ' * S) := by ring
      _ = σ * (ω' + X ^ (2 * t) * v) := by rw [e2]
      _ = σ * ω' + X ^ (2 * t) * (σ * v) := by ring
  have key : σ * ω' - σ' * ω = X ^ (2 * t) * (σ' * u - σ * v) := by
    have h6 : σ * ω' - σ' * ω - X ^ (2 * t) * (σ' * u - σ * v) = 0 := by
      have hexp : σ * ω' - σ' * ω - X ^ (2 * t) * (σ' * u - σ * v)
          = (σ * ω' + X ^ (2 * t) * (σ * v)) - (σ' * ω + X ^ (2 * t) * (σ' * u)) := by
        ring
      rw [hexp, h4]
      ring
    exact sub_eq_zero.mp h6
  have hdeg : (σ * ω' - σ' * ω).natDegree < 2 * t := by
    have h6 : (σ * ω').natDegree ≤ σ.natDegree + ω'.natDegree := natDegree_mul_le
    have h7 : (σ' * ω).natDegree ≤ σ'.natDegree + ω.natDegree := natDegree_mul_le
    have h8 := natDegree_sub_le (σ * ω') (σ' * ω)
    omega
  have hdvd : X ^ (2 * t) ∣ σ * ω' - σ' * ω := ⟨σ' * u - σ * v, key⟩
  exact sub_eq_zero.mp (pdec_X_pow_dvd_eq_zero hdvd hdeg)

theorem pdec_natDegree_finset_sum_le {α F : Type} [Field F] [DecidableEq F] (s : Finset α)
    (f : α → F[X]) (n : ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ n) :
    (∑ i ∈ s, f i).natDegree ≤ n := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (natDegree_add_le _ _) (max_le (h a (Finset.mem_insert_self a s)) ?_)
      exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A Euclidean predecessor certifies minimality of a bounded key solution.
The certificate is an identity of polynomials, together with one key congruence;
no assumption about the existence of a decodable support is used. -/
theorem keySolEMin_of_euclidean_certificate
    {F : Type} [Field F] (e : ℕ → F) (t : ℕ)
    {τ ν σ ω : F[X]}
    (hkey : KeySolE e t σ ω)
    (hprev : X ^ (2 * t) ∣
      τ * (∑ j ∈ Finset.range (2 * t), C (e j) * X ^ j) - ν)
    (hdet : ν * σ - τ * ω = X ^ (2 * t)) :
    KeySolEMin e t σ ω := by
  refine ⟨hkey, ?_⟩
  intro σ' ω' hkey'
  let S : F[X] := ∑ j ∈ Finset.range (2 * t), C (e j) * X ^ j
  let M : F[X] := X ^ (2 * t)
  have hcross : σ * ω' = σ' * ω :=
    key_equation_unique S t hkey.1 hkey'.1 hkey.2.1 hkey'.2.1
      hkey.2.2.1 hkey'.2.2.1 hkey.2.2.2 hkey'.2.2.2
  have hdiv : M ∣ ν * σ' - τ * ω' := by
    have ha : M ∣ τ * (σ' * S - ω') := dvd_mul_of_dvd_right hkey'.2.2.2 τ
    have hb : M ∣ σ' * (τ * S - ν) := dvd_mul_of_dvd_right hprev σ'
    have hc := dvd_sub ha hb
    convert hc using 1 <;> ring
  obtain ⟨q, hq⟩ := hdiv
  have hprod : M * σ' = M * (σ * q) := by
    calc
      M * σ' = (ν * σ - τ * ω) * σ' := by rw [hdet]
      _ = ν * (σ * σ') - τ * (σ' * ω) := by ring
      _ = ν * (σ * σ') - τ * (σ * ω') := by rw [← hcross]
      _ = σ * (ν * σ' - τ * ω') := by ring
      _ = σ * (M * q) := by rw [hq]
      _ = M * (σ * q) := by ring
  have hM : M ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have hfactor : σ' = σ * q := mul_left_cancel₀ hM hprod
  exact Polynomial.natDegree_le_of_dvd ⟨q, hfactor⟩ hkey'.1

/-- Initial Euclidean rows: `(M, 0)` and `(S, 1)`. -/
theorem padeBasis_initial {F : Type} [Field F] (S M : F[X]) :
    PadeBasis S M 0 M 1 S := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨-1, by ring⟩
  · simp
  · ring

/-- One quotient update preserves the two congruences and the determinant.
Characteristic two removes the determinant sign when the rows are exchanged. -/
theorem padeBasis_step {F : Type} [Field F] [Algebra (ZMod 2) F]
    {S M τ ν σ ω : F[X]} (h : PadeBasis S M τ ν σ ω) (q : F[X]) :
    PadeBasis S M σ ω (τ - q * σ) (ν - q * ω) := by
  refine ⟨h.2.1, ?_, ?_⟩
  · have hd := dvd_sub h.1 (dvd_mul_of_dvd_right h.2.1 q)
    convert hd using 1 <;> ring
  · calc
      ω * (τ - q * σ) - σ * (ν - q * ω) = -(ν * σ - τ * ω) := by ring
      _ = -M := by rw [h.2.2]
      _ = M := by
        haveI : CharP F 2 := pinsketch_charP
        haveI : CharP F[X] 2 := inferInstance
        exact CharTwo.neg_eq M

/-- The machine's Euclidean invariant provides the minimality certificate
once its terminating row has the required key-equation degree bounds. -/
theorem padeBasis_minimal {F : Type} [Field F] (e : ℕ → F) (t : ℕ)
    {τ ν σ ω : F[X]}
    (h : PadeBasis (∑ j ∈ Finset.range (2 * t), C (e j) * X ^ j)
      (X ^ (2 * t)) τ ν σ ω)
    (hσ : σ ≠ 0) (hdegσ : σ.natDegree ≤ t) (hdegω : ω.natDegree < t) :
    KeySolEMin e t σ ω :=
  keySolEMin_of_euclidean_certificate e t ⟨hσ, hdegσ, hdegω, h.2.1⟩ h.1 h.2.2

theorem syndromePoly_natDegree_lt {F : Type} [Field F] (e : ℕ → F) (t : ℕ)
    (ht : 1 ≤ t) : (syndromePoly e t).natDegree < 2 * t := by
  classical
  have hle : (syndromePoly e t).natDegree ≤ 2 * t - 1 := by
    refine pdec_natDegree_finset_sum_le (Finset.range (2 * t))
      (fun j => C (e j) * X ^ j) (2 * t - 1) ?_
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le (e j) j) (by omega)
  omega

theorem padeInv_initial {F : Type} [Field F] (e : ℕ → F) (t : ℕ) (ht : 1 ≤ t) :
    PadeInv e t (padeInitial e t) := by
  refine ⟨padeBasis_initial _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pow_ne_zero _ Polynomial.X_ne_zero
  · exact one_ne_zero
  · simp [padeInitial]
  · simp only [padeInitial, Polynomial.natDegree_X_pow]
    omega
  · simp [padeInitial]
  · simpa only [padeInitial, Polynomial.natDegree_X_pow] using
      syndromePoly_natDegree_lt e t ht

/-- A quotient step strictly lowers the preceding remainder and preserves
all degree and congruence information. -/
theorem padeInv_next {F : Type} [Field F] [Algebra (ZMod 2) F]
    {e : ℕ → F} {t : ℕ} {s : PadeState F} (ht : 1 ≤ t)
    (h : PadeInv e t s) (hgo : t ≤ s.rem.natDegree) :
    PadeInv e t (padeNext s) := by
  let q : F[X] := s.prevR / s.rem
  have hrem_ne : s.rem ≠ 0 := by
    intro hz
    have hd : s.rem.natDegree = 0 := by rw [hz, Polynomial.natDegree_zero]
    omega
  have hdegree : s.rem.degree ≤ s.prevR.degree := by
    rw [Polynomial.degree_eq_natDegree hrem_ne, Polynomial.degree_eq_natDegree h.prev_ne]
    exact_mod_cast (le_of_lt h.rem_small)
  have hq_ne : q ≠ 0 := by
    intro hz
    have hlt := (Polynomial.div_eq_zero_iff hrem_ne).mp hz
    exact (not_lt_of_ge hdegree) hlt
  have hdivdeg : s.rem.natDegree + q.natDegree = s.prevR.natDegree := by
    have hd := Polynomial.degree_add_div (p := s.prevR) (q := s.rem) hrem_ne hdegree
    rw [Polynomial.degree_eq_natDegree hrem_ne,
      Polynomial.degree_eq_natDegree h.prev_ne, Polynomial.degree_eq_natDegree hq_ne] at hd
    exact_mod_cast hd
  have hq_pos : 0 < q.natDegree := by
    have hlt := h.rem_small
    omega
  have hmuldeg : (q * s.curC).natDegree = q.natDegree + s.curC.natDegree :=
    Polynomial.natDegree_mul hq_ne h.cur_ne
  have hless : s.prevC.natDegree < (q * s.curC).natDegree := by
    rw [hmuldeg]
    have hp := h.prev_small
    omega
  have hnewdeg : (s.prevC - q * s.curC).natDegree = q.natDegree + s.curC.natDegree := by
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt hless, hmuldeg]
  have hnew_ne : s.prevC - q * s.curC ≠ 0 := by
    intro hz
    rw [hz, Polynomial.natDegree_zero] at hnewdeg
    omega
  have hrem_eq : s.prevR - q * s.rem = s.prevR % s.rem := by
    dsimp only [q]
    linear_combination -(EuclideanDomain.div_add_mod s.prevR s.rem)
  have hb := padeBasis_step h.basis q
  rw [hrem_eq] at hb
  refine ⟨hb, hrem_ne, hnew_ne, ?_, hgo, ?_, ?_⟩
  · change s.rem.natDegree + (s.prevC - q * s.curC).natDegree = 2 * t
    rw [hnewdeg]
    have hbal := h.balance
    omega
  · change s.curC.natDegree ≤ (s.prevC - q * s.curC).natDegree
    rw [hnewdeg]
    omega
  · change (s.prevR % s.rem).natDegree < s.rem.natDegree
    exact Polynomial.natDegree_mod_lt _ (by omega)

/-- Sufficient fuel cannot be exhausted: remainders decrease before each
recursive call, and the degree balance survives every quotient. -/
theorem padeRun_spec {F : Type} [Field F] [Algebra (ZMod 2) F]
    (e : ℕ → F) (t : ℕ) (ht : 1 ≤ t) (fuel : ℕ) (s : PadeState F)
    (h : PadeInv e t s) (hfuel : s.prevR.natDegree < fuel) :
    PadeInv e t (padeRun t fuel s) ∧ (padeRun t fuel s).rem.natDegree < t := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
      by_cases hstop : s.rem.natDegree < t
      · rw [padeRun, if_pos hstop]
        exact ⟨h, hstop⟩
      · have hn := padeInv_next ht h (Nat.le_of_not_gt hstop)
        have hn_fuel : (padeNext s).prevR.natDegree < fuel := by
          change s.rem.natDegree < fuel
          have hd := h.rem_small
          omega
        rw [padeRun, if_neg hstop]
        exact ih (padeNext s) hn hn_fuel

/-- The complete abstract key-equation solver: for every syndrome sequence,
including undecodable ones, it returns a minimum-degree bounded solution. -/
theorem padeSolve_minimal {F : Type} [Field F] [Algebra (ZMod 2) F]
    (e : ℕ → F) (t : ℕ) (ht : 1 ≤ t) :
    KeySolEMin e t (padeSolve e t).curC (padeSolve e t).rem := by
  have hfuel : (padeInitial e t).prevR.natDegree < 2 * t + 1 := by
    simp [padeInitial]
  obtain ⟨h, hstop⟩ := padeRun_spec e t ht (2 * t + 1) (padeInitial e t)
    (padeInv_initial e t ht) hfuel
  have hdeg : (padeSolve e t).curC.natDegree ≤ t := by
    have hbal := h.balance
    have hlarge := h.prev_large
    change (padeSolve e t).prevR.natDegree + (padeSolve e t).curC.natDegree = 2 * t at hbal
    change t ≤ (padeSolve e t).prevR.natDegree at hlarge
    omega
  exact padeBasis_minimal e t h.basis h.cur_ne hdeg hstop

@[simp] theorem noBranch_append (a b : List Instr) : NoBranch (a ++ b) ↔ NoBranch a ∧ NoBranch b := by
  induction a with
  | nil => simp
  | cons i t ih => simp [ih, and_assoc]

@[simp] theorem noBranchI_sub (d a b : Fin 16) : (iSub d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_bor (d a b : Fin 16) : (iBor d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_bxor (d a b : Fin 16) : (iBxor d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

@[simp] theorem noBranchI_shl (d a b : Fin 16) : (iShl d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h

theorem at_ite {P : Program} {a : ℕ} {c : Cond} {sa sb : Stmt}
    (h : At P a (Stmt.compile (Stmt.ite c sa sb) a)) :
    At P a c.code ∧
      P[a + c.code.length]? = some (iJz c.test (a + c.code.length + sa.len + 2)) ∧
      At P (a + c.code.length + 1) (sa.compile (a + c.code.length + 1)) ∧
      P[a + c.code.length + 1 + sa.len]? = some (iJmp (a + c.code.length + sa.len + sb.len + 3)) ∧
      At P (a + c.code.length + 1 + sa.len + 1) (sb.compile (a + c.code.length + sa.len + 2)) ∧
      P[a + c.code.length + 1 + sa.len + 1 + sb.len]? =
        some (iJmp (a + c.code.length + sa.len + sb.len + 3)) := by
  simpa [Stmt.compile, Stmt.length_compile, At.append, At.cons, At.nil] using h

/-- A conditional.  Both branches run from their own entry address to their trailing `jmp`; the
postcondition sees the cost *plus* the test, the `jz` and the `jmp`, and the state with the program
counter already at the exit. -/
theorem Sem.ite (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (sa sb : Stmt) (s : RAMState)
    (Q : ℕ → RAMState → Prop) (hAt : At P a (Stmt.compile (Stmt.ite c sa sb) a)) (hW : 1 < 2 ^ E.W)
    (hpc : s.pc = a)
    (htrue : c.eval s → Sem P E (a + c.code.length + 1) (a + c.code.length + 1 + sa.len)
      { runBlock c.code E s with pc := a + c.code.length + 1 }
      (fun t s' => Q (c.code.length + 1 + t + 1) { s' with pc := a + c.code.length + sa.len + sb.len + 3 }))
    (hfalse : ¬ c.eval s → Sem P E (a + c.code.length + sa.len + 2)
      (a + c.code.length + 1 + sa.len + 1 + sb.len)
      { runBlock c.code E s with pc := a + c.code.length + sa.len + 2 }
      (fun t s' => Q (c.code.length + 1 + t + 1) { s' with pc := a + c.code.length + sa.len + sb.len + 3 })) :
    Sem P E a (a + c.code.length + sa.len + sb.len + 3) s Q := by
  obtain ⟨hcode, hjz, -, hjmpA, -, hjmpB⟩ := at_ite hAt
  have htest : Sem P E a (a + c.code.length) s
      (fun k s' => k = c.code.length ∧ s' = runBlock c.code E s) :=
    Sem.block P E a c.code s hcode (Cond.noBranch_code c) hpc
  have hpcT : (runBlock c.code E s).pc = a + c.code.length := by
    rw [runBlock_pc c.code E s (Cond.noBranch_code c), hpc]
  by_cases hgo : c.eval s
  · have hne : (runBlock c.code E s).regs c.test ≠ 0 := (Cond.eval_iff c E s hW).mp hgo
    have hstep : Sem P E (a + c.code.length) (a + c.code.length + 1) (runBlock c.code E s)
        (fun k s' => k = 1 ∧ s' = { runBlock c.code E s with pc := a + c.code.length + 1 }) :=
      Sem.jz_next P E (a + c.code.length) (a + c.code.length + sa.len + 2) c _ hjz hpcT hne
    refine Sem.jmp_append hjmpA ?_
    refine Sem.mono (Sem.seq (Q₁ := fun k s' => k = c.code.length + 1 ∧
        s' = { runBlock c.code E s with pc := a + c.code.length + 1 })
      (Q₂ := fun k₁ k₂ s' => k₁ = (c.code.length + 1) ∧
        Q ((c.code.length + 1) + k₂ + 1) { s' with pc := a + c.code.length + sa.len + sb.len + 3 })
      (Sem.trans htest hstep) ?_) ?_
    · intro k₁ s₁ hQ₁
      obtain ⟨rfl, rfl⟩ : k₁ = c.code.length + 1 ∧
          s₁ = { runBlock c.code E s with pc := a + c.code.length + 1 } := hQ₁
      exact Sem.mono (htrue hgo) (fun k s' h => ⟨rfl, h⟩)
    · intro k s' h
      obtain ⟨k₁, k₂, hk, hQ⟩ := h
      have he : (c.code.length + 1) + k₂ + 1 = k + 1 := by omega
      rw [he] at hQ
      exact hQ.2
  · have h0 : (runBlock c.code E s).regs c.test = 0 := by
      by_contra hne
      exact hgo ((Cond.eval_iff c E s hW).mpr hne)
    have hstep : Sem P E (a + c.code.length) (a + c.code.length + sa.len + 2) (runBlock c.code E s)
        (fun k s' => k = 1 ∧ s' = { runBlock c.code E s with pc := a + c.code.length + sa.len + 2 }) :=
      Sem.jz_taken P E (a + c.code.length) (a + c.code.length + sa.len + 2) c _ hjz hpcT h0
    refine Sem.jmp_append hjmpB ?_
    refine Sem.mono (Sem.seq (Q₁ := fun k s' => k = c.code.length + 1 ∧
        s' = { runBlock c.code E s with pc := a + c.code.length + sa.len + 2 })
      (Q₂ := fun k₁ k₂ s' => k₁ = (c.code.length + 1) ∧
        Q ((c.code.length + 1) + k₂ + 1) { s' with pc := a + c.code.length + sa.len + sb.len + 3 })
      (Sem.trans htest hstep) ?_) ?_
    · intro k₁ s₁ hQ₁
      obtain ⟨rfl, rfl⟩ : k₁ = c.code.length + 1 ∧
          s₁ = { runBlock c.code E s with pc := a + c.code.length + sa.len + 2 } := hQ₁
      exact Sem.mono (hfalse hgo) (fun k s' h => ⟨rfl, h⟩)
    · intro k s' h
      obtain ⟨k₁, k₂, hk, hQ⟩ := h
      have he : (c.code.length + 1) + k₂ + 1 = k + 1 := by omega
      rw [he] at hQ
      exact hQ.2

section Enc

variable {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}

end Enc

section Tables

variable {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}

@[simp] theorem hdrTab_eight (t N w : ℕ) : hdrTab t N w 8 = detInvBase w := rfl

end Tables

section ReadInt

end ReadInt

section ReadLoop

end ReadLoop

section ProgramAt

end ProgramAt

section ReadSpec

end ReadSpec

section ReadStmt

end ReadStmt

section Bounds

end Bounds

section Prologue

end Prologue

section ReadAssembly

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end ReadAssembly

section Expand

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end Expand

section ExpandStd

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end ExpandStd

theorem enc_injective {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) : Function.Injective (enc b) := by
  intro x y h
  have hd := congrArg (dec b) h
  simpa only [dec_enc] using hd

theorem enc_testBit {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (z : F) (k : ℕ) (hk : k < w) :
    (enc b z).testBit k = decide (b.repr z ⟨k, hk⟩ = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, enc_bit b z ⟨k, hk⟩]
  rcases zmod2_eq_zero_or_one (b.repr z ⟨k, hk⟩) with h | h <;> norm_num [h] <;> decide

/-- Machine XOR is addition in the supplied basis. -/
theorem enc_add_xor {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (x y : F) :
    enc b (x + y) = enc b x ^^^ enc b y := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor]
  by_cases hk : k < w
  · rw [enc_testBit b (x + y) k hk, enc_testBit b x k hk, enc_testBit b y k hk]
    simp only [map_add, Finsupp.add_apply]
    rcases zmod2_eq_zero_or_one (b.repr x ⟨k, hk⟩) with hx | hx <;>
      rcases zmod2_eq_zero_or_one (b.repr y ⟨k, hk⟩) with hy | hy <;>
      norm_num [hx, hy] <;> decide
  · have hpow : (2 : ℕ) ^ w ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h0 := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (enc_lt b (x + y)) hpow)
    have hx := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (enc_lt b x) hpow)
    have hy := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (enc_lt b y) hpow)
    rw [h0, hx, hy]
    rfl

theorem pairIdx_lt (w a c : ℕ) (ha : a < 2 ^ w) (hc : c < 2 ^ w) :
    pairIdx w a c < 2 ^ (2 * w) := by
  have hexp : 2 ^ (2 * w) = (2 : ℕ) ^ w * 2 ^ w := by
    rw [show 2 * w = w + w by omega, Nat.pow_add]
  rw [hexp, pairIdx]
  calc
    a * 2 ^ w + c < a * 2 ^ w + 2 ^ w := Nat.add_lt_add_left hc _
    _ = (a + 1) * 2 ^ w := by ring
    _ ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_right _ (by omega)

theorem detEnd_lt {w : ℕ} (hw : 1 ≤ w) : detEnd w < 2 ^ (8 * w) := by
  by_cases hs : w ≤ 3
  · unfold detEnd detImgBase detPosBase detInvBase detSqBase detMulBase
    interval_cases w <;> norm_num
  · have h64 : (64 : ℕ) ≤ 2 ^ (2 * w) := by
      have h := Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : 6 ≤ 2 * w)
      exact h
    have hq : (2 : ℕ) ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have heq : detEnd w = 64 + 2 * 2 ^ (2 * w) + 3 * 2 ^ w := by
      unfold detEnd detImgBase detPosBase detInvBase detSqBase detMulBase
      ring
    have hsum : detEnd w ≤ 6 * 2 ^ (2 * w) := by rw [heq]; omega
    have hpos := Nat.two_pow_pos (2 * w)
    have hstrict : 6 * 2 ^ (2 * w) < 8 * 2 ^ (2 * w) := by omega
    have hp : (8 : ℕ) * 2 ^ (2 * w) = 2 ^ (2 * w + 3) := by
      rw [Nat.pow_add]
      norm_num <;> ring
    have hupper : (2 : ℕ) ^ (2 * w + 3) ≤ 2 ^ (8 * w) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem detStd_mul {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (t N : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    {a c : ℕ} (ha : a < 2 ^ w) (hc : c < 2 ^ w) :
    detStd t N b ι (detMulBase w + pairIdx w a c) = mulTab b a c := by
  have hi := pairIdx_lt w a c ha hc
  have h0 : ¬ detMulBase w + pairIdx w a c < 13 := by unfold detMulBase; omega
  have h1 : ¬ detMulBase w + pairIdx w a c < detMulBase w := by omega
  have h2 : detMulBase w + pairIdx w a c < detSqBase w := by unfold detSqBase; omega
  have hdiv : pairIdx w a c / 2 ^ w = a := by
    rw [pairIdx, Nat.mul_comm a (2 ^ w), Nat.mul_add_div (Nat.two_pow_pos w),
      Nat.div_eq_of_lt hc, Nat.add_zero]
  have hmod : pairIdx w a c % 2 ^ w = c := by
    rw [pairIdx, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  unfold detStd
  rw [if_neg h0, if_neg h1, if_pos h2, Nat.add_sub_cancel_left, hdiv, hmod]

theorem detStd_inv {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (t N : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    {a : ℕ} (ha : a < 2 ^ w) :
    detStd t N b ι (detInvBase w + a) = invTab b a := by
  have hpos : 0 < (2 : ℕ) ^ (2 * w) := Nat.two_pow_pos _
  have hinv : detInvBase w = 64 + 2 ^ (2 * w) + 2 ^ (2 * w) := rfl
  have hsq : detSqBase w = 64 + 2 ^ (2 * w) := rfl
  have hmul : detMulBase w = 64 := rfl
  have h0 : ¬ detInvBase w + a < 13 := by omega
  have h1 : ¬ detInvBase w + a < detMulBase w := by omega
  have h2 : ¬ detInvBase w + a < detSqBase w := by omega
  have h3 : ¬ detInvBase w + a < detInvBase w := by omega
  have h4 : detInvBase w + a < detPosBase w := by unfold detPosBase; omega
  unfold detStd
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, Nat.add_sub_cancel_left]

/-- Exact result and scratch-register contents of a multiplication. -/
theorem fieldMulCode_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (E : RAMEnv) (s : RAMState) (x y : F) (hw : 1 ≤ w)
    (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (hwreg : s.regs r3 = w) (hx : s.regs r10 = enc b x) (hy : s.regs r11 = enc b y) :
    runBlock fieldMulCode E s =
      { s with pc := s.pc + 7, regs := Function.update (Function.update (Function.update s.regs r15 64) r14 (pairIdx w (enc b x) (enc b y) + 64)) r10 (enc b (x * y)) } := by
  have hpow : (2 : ℕ) ^ w ≤ 2 ^ E.W := by
    rw [hW]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hi := pairIdx_lt w (enc b x) (enc b y) (enc_lt b x) (enc_lt b y)
  have hbase := detSqBase_lt hw
  have h64 : (64 : ℕ) < 2 ^ E.W := by rw [hW]; unfold detSqBase detMulBase at hbase; omega
  have h1 : (1 : ℕ) < 2 ^ E.W := by omega
  have hq : (2 : ℕ) ^ w < 2 ^ E.W := by
    rw [hW]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have ha : enc b x * 2 ^ w < 2 ^ E.W := by
    unfold pairIdx at hi
    rw [hW]
    unfold detSqBase detMulBase at hbase
    omega
  have hib : pairIdx w (enc b x) (enc b y) < 2 ^ E.W := by
    rw [hW]
    unfold detSqBase detMulBase at hbase
    omega
  have haddr : pairIdx w (enc b x) (enc b y) + 64 < 2 ^ E.W := by
    rw [hW]
    unfold detSqBase detMulBase at hbase
    omega
  have htab : E.det (pairIdx w (enc b x) (enc b y) + 64) = enc b (x * y) := by
    rw [hdet.2 _ (by unfold detMulBase; omega)]
    have haeq : pairIdx w (enc b x) (enc b y) + 64 =
        detMulBase w + pairIdx w (enc b x) (enc b y) := by unfold detMulBase; omega
    rw [haeq, detStd_mul t N b ι (enc_lt b x) (enc_lt b y), mulTab, dec_enc, dec_enc]
  have hv : enc b (x * y) < 2 ^ E.W := lt_of_lt_of_le (enc_lt b _) hpow
  unfold pairIdx at hi hib haddr htab ⊢
  apply ramState_eq_of
  ·     simp only [fieldMulCode, Fin.isValue, runBlock_cons, execInstr, Function.update_self, ne_eq,
      Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Nat.mod_mul_mod, one_mul, Function.update_idem,
      Nat.mul_mod_mod, Nat.mod_add_mod, Nat.add_mod_mod, runBlock_nil, Nat.add_right_cancel_iff,
      Nat.add_left_cancel_iff] <;> omega
  · rfl
  · intro d
    fin_cases d <;>
      simp only [fieldMulCode, Fin.isValue, runBlock_cons, execInstr, Nat.mod_eq_of_lt h1,
        Function.update_self, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, hwreg, one_mul,
        Nat.mod_eq_of_lt hq, Function.update_idem, hx, Nat.mod_eq_of_lt ha, hy, Nat.mod_eq_of_lt hib,
        Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt haddr, htab, Nat.mod_eq_of_lt hv, runBlock_nil, Fin.zero_eta,
        Fin.mk_one, Fin.reduceFinMk, Nat.add_left_cancel_iff]

/-- Exact result and scratch-register contents of inversion. -/
theorem fieldInvCode_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (E : RAMEnv) (s : RAMState) (x : F) (hw : 1 ≤ w)
    (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι) (hx : s.regs r10 = enc b x) :
    runBlock fieldInvCode E s =
      { s with pc := s.pc + 4, regs := Function.update (Function.update (Function.update s.regs r15 (detInvBase w)) r14 (detInvBase w + enc b x)) r10 (enc b x⁻¹) } := by
  have hpow : (2 : ℕ) ^ w ≤ 2 ^ E.W := by
    rw [hW]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbase : detInvBase w < 2 ^ E.W := by rw [hW]; exact detInvBase_lt hw
  have hend : detEnd w < 2 ^ E.W := by rw [hW]; exact detEnd_lt hw
  have haddr : detInvBase w + enc b x < 2 ^ E.W := by
    have hxlt := enc_lt b x
    have hp := Nat.two_pow_pos w
    unfold detEnd detImgBase detPosBase at hend
    omega
  have h8 : (8 : ℕ) < 2 ^ E.W := by
    have hbound : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (8 : ℕ) < 2 ^ 8) hbound
  have hhdr : E.det 8 = detInvBase w := by
    rw [hdet.1 8 (by decide), detStd_hdr t N w b ι (by norm_num : (8 : ℕ) < 13), hdrTab_eight]
  have htab : E.det (detInvBase w + enc b x) = enc b x⁻¹ := by
    rw [hdet.2 _ (by have h := detMulBase_le_detInvBase w; omega), detStd_inv t N b ι (enc_lt b x), invTab, dec_enc]
  have hv : enc b x⁻¹ < 2 ^ E.W := lt_of_lt_of_le (enc_lt b _) hpow
  apply ramState_eq_of
  · simp [fieldInvCode, runBlock_cons, runBlock_nil, execInstr] <;> omega
  · rfl
  · intro d
    fin_cases d <;>
      simp [fieldInvCode, runBlock_cons, runBlock_nil, execInstr, hx, hhdr, htab,
        Nat.mod_eq_of_lt h8, Nat.mod_eq_of_lt hbase, Nat.mod_eq_of_lt haddr,
        Nat.mod_eq_of_lt hv]

/-- Exact result of one XOR instruction, interpreted as field addition. -/
theorem fieldAddCode_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (E : RAMEnv) (s : RAMState) (x y : F)
    (hW : w ≤ E.W) (hx : s.regs r10 = enc b x) (hy : s.regs r11 = enc b y) :
    runBlock fieldAddCode E s =
      { s with pc := s.pc + 1, regs := Function.update s.regs r10 (enc b (x + y)) } := by
  have hpow : (2 : ℕ) ^ w ≤ 2 ^ E.W := Nat.pow_le_pow_right (by norm_num) hW
  have hv : enc b (x + y) < 2 ^ E.W := lt_of_lt_of_le (enc_lt b _) hpow
  have hresult : (enc b x ^^^ enc b y) % 2 ^ E.W = enc b (x + y) := by
    rw [← enc_add_xor]
    exact Nat.mod_eq_of_lt hv
  change execInstr (.bxor r10 r10 r11) E s = _
  simp only [execInstr, hx, hy, hresult]

/-- One coefficient update, including all machine scratch registers. -/
theorem axpyBody_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (E : RAMEnv) (pc dst src L : ℕ) (a : F) (x y : ℕ → F)
    (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ)
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (hj : j < L) (hL : L < 2 ^ E.W)
    (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src)
    (hx : ∀ i < L, m (src + i) = enc b (x i))
    (hy : ∀ i < L, m (dst + i) = enc b (y i)) :
    runBlock axpyBody E { runBlock axpyCond.code E (axpyState b pc dst src L a x y m r j) with pc := pc + 2 } =
      { axpyState b pc dst src L a x y m r (j + 1) with pc := pc + 23 } := by
  have hpow : (2 : ℕ) ^ w ≤ 2 ^ E.W := by
    rw [hW]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have henc (z : F) : enc b z % 2 ^ E.W = enc b z :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le (enc_lt b z) hpow)
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := by
    apply Nat.mod_eq_of_lt
    have hp : (2 : ℕ) ^ 1 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsrcj : (src + j) % 2 ^ E.W = src + j := Nat.mod_eq_of_lt (by omega)
  have hdstj : (dst + j) % 2 ^ E.W = dst + j := Nat.mod_eq_of_lt (by omega)
  have hj1 : (j + 1) % 2 ^ E.W = j + 1 := Nat.mod_eq_of_lt (by omega)
  let f := fun i => enc b (a * x i + y i)
  have hmSrc : writeArray dst m f j (src + j) = enc b (x j) := by
    rw [writeArray_frame dst m f j (src + j) (by omega), hx j hj]
  have hmDst : writeArray dst m f j (dst + j) = enc b (y j) := by
    rw [writeArray_frame dst m f j (dst + j) (Or.inr (le_refl _)), hy j hj]
  dsimp only [f] at hmSrc hmDst
  let entry : RAMState := { runBlock axpyCond.code E (axpyState b pc dst src L a x y m r j) with pc := pc + 2 }
  let sA := runBlock axpyPrefix E entry
  have hA3 : sA.regs r3 = w := by
    simp [sA, entry, axpyPrefix, axpyCond, Cond.code, axpyState,
      runBlock_cons, runBlock_nil, execInstr]
  have hA10 : sA.regs r10 = enc b a := by
    simp [sA, entry, axpyPrefix, axpyCond, Cond.code, axpyState,
      runBlock_cons, runBlock_nil, execInstr, henc]
  have hA11 : sA.regs r11 = enc b (x j) := by
    simp [sA, entry, axpyPrefix, axpyCond, Cond.code, axpyState,
      runBlock_cons, runBlock_nil, execInstr, hsrcj, hmSrc, f, henc]
  have hMul := fieldMulCode_spec b ι t N E sA a (x j) hw hW hdet hA3 hA10 hA11
  let sB := runBlock axpyAfterMul E (runBlock fieldMulCode E sA)
  have hB10 : sB.regs r10 = enc b (a * x j) := by
    dsimp only [sB]
    rw [hMul]
    simp only [axpyAfterMul, Fin.isValue, runBlock_cons, execInstr, ne_eq, Fin.reduceEq, not_false_eq_true,
      Function.update_of_ne, Function.update_self, runBlock_nil]
  have hB11 : sB.regs r11 = enc b (y j) := by
    dsimp only [sB]
    rw [hMul]
    simp [axpyAfterMul, sA, entry, axpyPrefix, axpyCond, Cond.code, axpyState,
      runBlock_cons, runBlock_nil, execInstr, hdstj, hmDst, f, henc]
  have hAdd := fieldAddCode_spec b E sB (a * x j) (y j) (by omega : w ≤ E.W) hB10 hB11
  have hfinish : runBlock axpyBody E entry =
      runBlock axpyTail E { sB with pc := sB.pc + 1, regs := Function.update sB.regs r10 (enc b (a * x j + y j)) } := by
    calc
      runBlock axpyBody E entry = runBlock axpyTail E (runBlock fieldAddCode E sB) := by
        simp only [axpyBody, runBlock_append] <;> rfl
      _ = _ := by rw [hAdd]
  change runBlock axpyBody E entry = _
  rw [hfinish]
  dsimp only [sB]
  simp only [hMul]
  apply ramState_eq_of
  · simp [axpyTail, axpyAfterMul, sA, entry, axpyPrefix, axpyCond, Cond.code,
      axpyState, runBlock_cons, runBlock_nil, execInstr] <;> omega
  · simp [axpyTail, axpyAfterMul, sA, entry, axpyPrefix, axpyCond, Cond.code,
      axpyState, runBlock_cons, runBlock_nil, execInstr, hdstj, writeArray]
  · intro d
    simp only [axpyTail, axpyAfterMul, sA, entry, axpyPrefix, axpyCond, Cond.code,
      axpyState, runBlock_cons, runBlock_nil, execInstr, hj1, Function.update_idem]
    fin_cases d <;>
      simp [axpyTail, axpyAfterMul, sA, entry, axpyPrefix, axpyCond, Cond.code,
        axpyState, runBlock_cons, runBlock_nil, execInstr, hj1]

theorem axpyCond_eval {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (pc dst src L : ℕ) (a : F)
    (x y : ℕ → F) (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ) :
    axpyCond.eval (axpyState b pc dst src L a x y m r j) ↔ j < L := by
  simp [axpyCond, Cond.eval, axpyState]

theorem axpyBodyIter {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (pc dst src L : ℕ) (a : F) (x y : ℕ → F)
    (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ)
    (hAt : At P pc (Stmt.compile axpyStmt pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (hj : j < L) (hL : L < 2 ^ E.W)
    (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src)
    (hx : ∀ i < L, m (src + i) = enc b (x i))
    (hy : ∀ i < L, m (dst + i) = enc b (y i)) :
    Sem P E (pc + axpyCond.code.length + 1) pc
      { runBlock axpyCond.code E (axpyState b pc dst src L a x y m r j) with pc := pc + axpyCond.code.length + 1 }
      (fun k s' => k = 22 ∧ s' = axpyState b pc dst src L a x y m r (j + 1)) := by
  obtain ⟨_, _, hbody, hjmp⟩ := at_loop hAt
  have hbodyAt : At P (pc + 2) axpyBody := hbody
  have hjmpAt : P[pc + 23]? = some (iJmp pc) := hjmp
  have hrun : Sem P E (pc + 2) (pc + 23)
      { runBlock axpyCond.code E (axpyState b pc dst src L a x y m r j) with pc := pc + 2 }
      (fun k s' => k = 21 ∧ s' = { axpyState b pc dst src L a x y m r (j + 1) with pc := pc + 23 }) := by
    refine Sem.mono (Sem.block P E (pc + 2) axpyBody _ hbodyAt
      (by simp [axpyBody, axpyPrefix, axpyAfterMul, fieldMulCode, fieldAddCode, axpyTail]) rfl) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    refine ⟨hk, ?_⟩
    rw [hs]
    exact axpyBody_spec b ι t N E pc dst src L a x y m r j hw hW hdet hj hL hdst hsrc hdisj hx hy
  refine Sem.jmp_append (hAt := hjmpAt) (Sem.mono hrun ?_)
  intro k s' h
  obtain ⟨hk, hs⟩ := h
  refine ⟨by omega, ?_⟩
  rw [hs]
  rfl

theorem axpyCond_exit {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (E : RAMEnv) (pc dst src L : ℕ)
    (a : F) (x y : ℕ → F) (m : ℕ → ℕ) (r : Fin 16 → ℕ) :
    ({ runBlock axpyCond.code E (axpyState b pc dst src L a x y m r L) with pc := pc + 24 } : RAMState) =
      { axpyState b pc dst src L a x y m r L with pc := pc + 24 } := by
  apply ramState_eq_of
  · rfl
  · rfl
  · intro d
    fin_cases d <;> simp [axpyCond, Cond.code, runBlock_cons, runBlock_nil, execInstr, axpyState]

/-- The coefficient loop `dst[i] += a * src[i]`, with an explicit linear
step bound, valid inside any surrounding compiled program. -/
theorem axpyArray_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (pc dst src L : ℕ) (a : F) (x y : ℕ → F)
    (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (hAt : At P pc (Stmt.compile axpyStmt pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (hL : L < 2 ^ E.W) (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src)
    (hx : ∀ i < L, m (src + i) = enc b (x i))
    (hy : ∀ i < L, m (dst + i) = enc b (y i)) :
    Sem P E pc (pc + 24) (axpyState b pc dst src L a x y m r 0)
      (fun k s' => k ≤ 24 * L + 2 ∧ s' = { axpyState b pc dst src L a x y m r L with pc := pc + 24 }) := by
  have hW1 : 1 < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 1 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h := Sem.loop P E pc axpyCond (.code axpyBody) hAt hW1 L
    (fun j => axpyState b pc dst src L a x y m r j) (fun _ => 22)
    (fun _ => rfl)
    (fun j hj => (axpyCond_eval b pc dst src L a x y m r j).mpr hj)
    (fun hf => (Nat.lt_irrefl L) ((axpyCond_eval b pc dst src L a x y m r L).mp hf))
    (fun j hj => axpyBodyIter b ι t N P E pc dst src L a x y m r j hAt
      hw hW hdet hj hL hdst hsrc hdisj hx hy)
  refine Sem.mono h ?_
  intro k s' hQ
  obtain ⟨hcost, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · have hsum : (∑ j ∈ Finset.range L, (axpyCond.code.length + 1 + 22)) = 24 * L := by
      change (∑ j ∈ Finset.range L, (24 : ℕ)) = 24 * L
      exact sum_range_const_mul L 24
    rw [hsum] at hcost
    change k ≤ 2 + 24 * L at hcost
    omega
  · rw [hs]
    exact axpyCond_exit b E pc dst src L a x y m r

theorem degreeScan_le {F : Type} [Field F] [DecidableEq F] (p : F[X]) (n : ℕ) :
    degreeScan p n ≤ n := by
  induction n with
  | zero => simp [degreeScan]
  | succ n ih =>
      rw [degreeScan]
      split <;> omega

@[simp] theorem degreeScan_zero {F : Type} [Field F] [DecidableEq F] (n : ℕ) :
    degreeScan (0 : F[X]) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [degreeScan, ih]

theorem degreeScan_eq {F : Type} [Field F] [DecidableEq F] (p : F[X]) (hp : p ≠ 0)
    (n : ℕ) (hn : p.natDegree < n) : degreeScan p n = p.natDegree + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : p.natDegree = n
      · have hcoeff : p.coeff n ≠ 0 := by
          simpa only [Polynomial.leadingCoeff, h] using (Polynomial.leadingCoeff_ne_zero.mpr hp)
        rw [degreeScan, if_neg hcoeff, h]
      · have hlt : p.natDegree < n := by omega
        rw [degreeScan, if_pos (Polynomial.coeff_eq_zero_of_natDegree_lt hlt), ih hlt]

theorem enc_eq_zero_iff {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (z : F) : enc b z = 0 ↔ z = 0 := by
  constructor
  · intro h
    apply enc_injective b
    simpa only [enc_zero] using h
  · intro h
    simp [h]

theorem scanBody_spec {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (E : RAMEnv) (pc B L : ℕ)
    (p : F[X]) (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ)
    (hj : j < L) (hW : 1 < 2 ^ E.W) (hwe : w ≤ E.W)
    (hL : L < 2 ^ E.W) (hB : B + L ≤ 2 ^ E.W) (hp : PolynomialStored b m B L p) :
    runBlock scanBody E { runBlock scanCond.code E (scanState b pc B L p m r j) with pc := pc + 2 } =
      { scanState b pc B L p m r (j + 1) with pc := pc + 16 } := by
  have haddr : (B + j) % 2 ^ E.W = B + j := Nat.mod_eq_of_lt (by omega)
  have hnext : (j + 1) % 2 ^ E.W = j + 1 := Nat.mod_eq_of_lt (by omega)
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hacc : degreeScan p j % 2 ^ E.W = degreeScan p j := by
    apply Nat.mod_eq_of_lt
    have h := degreeScan_le p j
    omega
  have hval : enc b (p.coeff j) % 2 ^ E.W = enc b (p.coeff j) :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le (enc_lt b _) (Nat.pow_le_pow_right (by norm_num) hwe))
  have hsub0 : (1 + 2 ^ E.W - 0) % 2 ^ E.W = 1 := by
    simp [Nat.add_mod, h1]
  have hsub1 : (1 + 2 ^ E.W - 1) % 2 ^ E.W = 0 := by simp
  have hm := hp j hj
  by_cases hz : p.coeff j = 0
  · apply ramState_eq_of
    ·       simp only [scanBody, Fin.isValue, Cond.code, scanCond, scanState, runBlock_cons, execInstr, ↓reduceIte,
        one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
        Function.update_self, Nat.mul_mod_mod, mul_ite, mul_one, mul_zero, Function.update_idem,
        Nat.add_mod_mod, Nat.mod_add_mod, Nat.zero_mod, Nat.add_right_cancel_iff, Nat.add_left_cancel_iff] <;> omega
    · rfl
    · intro d
      simp only [scanBody, Fin.isValue, Cond.code, scanCond, scanState, runBlock_cons, execInstr,
        ↓reduceIte, one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true,
        Function.update_of_ne, haddr, Function.update_self, hm, hz, enc_zero, Nat.zero_mod,
        lt_self_iff_false, hnext, mul_zero, Function.update_idem, tsub_zero, Nat.add_mod_right, h1,
        mul_one, hacc, add_zero, degreeScan]
      fin_cases d <;>
        simp only [scanBody, Fin.isValue, Cond.code, scanCond, scanState, runBlock_cons, execInstr,
          ↓reduceIte, one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true,
          Function.update_of_ne, haddr, Function.update_self, hm, hz, enc_zero, Nat.zero_mod,
          lt_self_iff_false, hnext, mul_zero, Function.update_idem, tsub_zero, Nat.add_mod_right, h1,
          mul_one, hacc, add_zero, Fin.zero_eta, degreeScan, Nat.add_left_cancel_iff, Fin.mk_one,
          Fin.reduceFinMk]
  · have hpos : 0 < enc b (p.coeff j) := Nat.pos_of_ne_zero (fun h => hz ((enc_eq_zero_iff b _).mp h))
    apply ramState_eq_of
    ·       simp only [scanBody, Fin.isValue, Cond.code, scanCond, scanState, runBlock_cons, execInstr, ↓reduceIte,
        one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
        Function.update_self, Nat.mul_mod_mod, mul_ite, mul_one, mul_zero, Function.update_idem,
        Nat.add_mod_mod, Nat.mod_add_mod, Nat.zero_mod, Nat.add_right_cancel_iff, Nat.add_left_cancel_iff] <;> omega
    · rfl
    · intro d
      simp only [scanBody, Fin.isValue, Cond.code, scanCond, scanState, runBlock_cons, execInstr,
        ↓reduceIte, one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true,
        Function.update_of_ne, haddr, Function.update_self, hm, hval, hpos, h1, hnext, mul_one,
        Function.update_idem, add_tsub_cancel_left, Nat.mod_self, mul_zero, Nat.zero_mod, zero_add,
        degreeScan, hz]
      fin_cases d <;>
        simp only [scanBody, Fin.isValue, Cond.code, scanCond, scanState, runBlock_cons, execInstr,
          ↓reduceIte, one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true,
          Function.update_of_ne, haddr, Function.update_self, hm, hval, hpos, h1, hnext, mul_one,
          Function.update_idem, add_tsub_cancel_left, Nat.mod_self, mul_zero, Nat.zero_mod, zero_add,
          Fin.zero_eta, degreeScan, hz, Nat.add_left_cancel_iff, Fin.mk_one, Fin.reduceFinMk]

theorem scanCond_eval {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (pc B L : ℕ) (p : F[X])
    (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ) :
    scanCond.eval (scanState b pc B L p m r j) ↔ j < L := by
  simp [scanCond, Cond.eval, scanState]

theorem scanBodyIter {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (P : Program) (E : RAMEnv) (pc B L : ℕ)
    (p : F[X]) (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ)
    (hAt : At P pc (Stmt.compile scanStmt pc)) (hj : j < L)
    (hW : 1 < 2 ^ E.W) (hwe : w ≤ E.W) (hL : L < 2 ^ E.W)
    (hB : B + L ≤ 2 ^ E.W) (hp : PolynomialStored b m B L p) :
    Sem P E (pc + scanCond.code.length + 1) pc
      { runBlock scanCond.code E (scanState b pc B L p m r j) with pc := pc + scanCond.code.length + 1 }
      (fun k s' => k = 15 ∧ s' = scanState b pc B L p m r (j + 1)) := by
  obtain ⟨_, _, hbody, hjmp⟩ := at_loop hAt
  have hbodyAt : At P (pc + 2) scanBody := hbody
  have hjmpAt : P[pc + 16]? = some (iJmp pc) := hjmp
  have hrun : Sem P E (pc + 2) (pc + 16)
      { runBlock scanCond.code E (scanState b pc B L p m r j) with pc := pc + 2 }
      (fun k s' => k = 14 ∧ s' = { scanState b pc B L p m r (j + 1) with pc := pc + 16 }) := by
    refine Sem.mono (Sem.block P E (pc + 2) scanBody _ hbodyAt
      (by simp [scanBody]) rfl) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    refine ⟨hk, ?_⟩
    rw [hs]
    exact scanBody_spec b E pc B L p m r j hj hW hwe hL hB hp
  refine Sem.jmp_append (hAt := hjmpAt) (Sem.mono hrun ?_)
  intro k s' h
  obtain ⟨hk, hs⟩ := h
  refine ⟨by omega, ?_⟩
  rw [hs]
  rfl

theorem scanCond_exit {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (E : RAMEnv) (pc B L : ℕ) (p : F[X])
    (m : ℕ → ℕ) (r : Fin 16 → ℕ) :
    ({ runBlock scanCond.code E (scanState b pc B L p m r L) with pc := pc + 17 } : RAMState) =
      { scanState b pc B L p m r L with pc := pc + 17 } := by
  apply ramState_eq_of
  · rfl
  · rfl
  · intro d
    fin_cases d <;> simp [scanCond, Cond.code, runBlock_cons, runBlock_nil, execInstr, scanState]

theorem scanArray_spec {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (P : Program) (E : RAMEnv) (pc B L : ℕ)
    (p : F[X]) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (hAt : At P pc (Stmt.compile scanStmt pc))
    (hW : 1 < 2 ^ E.W) (hwe : w ≤ E.W) (hL : L < 2 ^ E.W)
    (hB : B + L ≤ 2 ^ E.W) (hp : PolynomialStored b m B L p) :
    Sem P E pc (pc + 17) (scanState b pc B L p m r 0)
      (fun k s' => k ≤ 17 * L + 2 ∧ s' = { scanState b pc B L p m r L with pc := pc + 17 }) := by
  have h := Sem.loop P E pc scanCond (.code scanBody) hAt hW L
    (fun j => scanState b pc B L p m r j) (fun _ => 15)
    (fun _ => rfl)
    (fun j hj => (scanCond_eval b pc B L p m r j).mpr hj)
    (fun hf => (Nat.lt_irrefl L) ((scanCond_eval b pc B L p m r L).mp hf))
    (fun j hj => scanBodyIter b P E pc B L p m r j hAt hj hW hwe hL hB hp)
  refine Sem.mono h ?_
  intro k s' hQ
  obtain ⟨hcost, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · have hsum : (∑ j ∈ Finset.range L, (scanCond.code.length + 1 + 15)) = 17 * L := by
      change (∑ j ∈ Finset.range L, (17 : ℕ)) = 17 * L
      exact sum_range_const_mul L 17
    rw [hsum] at hcost
    change k ≤ 2 + 17 * L at hcost
    omega
  · rw [hs]
    exact scanCond_exit b E pc B L p m r

theorem leadingCancel_degree {F : Type} [Field F] (D R : F[X]) (n : ℕ)
    (hD : 0 < D.natDegree) (hR : R.natDegree < D.natDegree + (n + 1)) :
    (R - leadingCancel D R n * D).natDegree < D.natDegree + n := by
  have hDne : D ≠ 0 := by intro hz; simp [hz] at hD
  have hT : (leadingCancel D R n).natDegree ≤ n :=
    Polynomial.natDegree_C_mul_X_pow_le _ _
  have hTD : (leadingCancel D R n * D).natDegree ≤ D.natDegree + n := by
    have hm := Polynomial.natDegree_mul_le (p := leadingCancel D R n) (q := D)
    omega
  have hle : (R - leadingCancel D R n * D).natDegree ≤ D.natDegree + n := by
    have hs := Polynomial.natDegree_sub_le R (leadingCancel D R n * D)
    omega
  have hc : (leadingCancel D R n * D).coeff (D.natDegree + n) = R.coeff (D.natDegree + n) := by
    rw [leadingCancel, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul]
    change (R.coeff (D.natDegree + n) / D.leadingCoeff) * D.leadingCoeff = _
    exact div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hDne)
  have hz : (R - leadingCancel D R n * D).coeff (D.natDegree + n) = 0 := by
    rw [Polynomial.coeff_sub, hc, sub_self]
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · have hzero : R - leadingCancel D R n * D = 0 := by
      apply Polynomial.leadingCoeff_eq_zero.mp
      change (R - leadingCancel D R n * D).coeff (R - leadingCancel D R n * D).natDegree = 0
      rw [h]
      exact hz
    rw [hzero, Polynomial.natDegree_zero] at h
    omega

theorem longReduceRows_degree {F : Type} [Field F] (D C : F[X]) (n : ℕ)
    (R U : F[X]) (hD : 0 < D.natDegree) (hR : R.natDegree < D.natDegree + n) :
    (longReduceRows D C n R U).1.natDegree < D.natDegree := by
  induction n generalizing R U with
  | zero => simpa only [longReduceRows, Nat.add_zero] using hR
  | succ n ih =>
      exact ih _ _ (leadingCancel_degree D R n hD hR)

theorem longReduceRows_relation {F : Type} [Field F] (D C : F[X]) (n : ℕ) (R U : F[X]) :
    ∃ q : F[X], R = D * q + (longReduceRows D C n R U).1 ∧
      U = C * q + (longReduceRows D C n R U).2 := by
  induction n generalizing R U with
  | zero => exact ⟨0, by simp [longReduceRows], by simp [longReduceRows]⟩
  | succ n ih =>
      let T := leadingCancel D R n
      obtain ⟨q, hR, hU⟩ := ih (R - T * D) (U - T * C)
      refine ⟨T + q, ?_, ?_⟩
      · change R = D * (T + q) + (longReduceRows D C n (R - T * D) (U - T * C)).1
        linear_combination hR
      · change U = C * (T + q) + (longReduceRows D C n (R - T * D) (U - T * C)).2
        linear_combination hU

/-- The coefficient loop computes exactly the quotient/remainder update
used by the already-verified key-equation solver. -/
theorem longReduceRows_eq {F : Type} [Field F] (D C : F[X]) (n : ℕ)
    (R U : F[X]) (hD : 0 < D.natDegree) (hR : R.natDegree < D.natDegree + n) :
    longReduceRows D C n R U = (R % D, U - (R / D) * C) := by
  have hDne : D ≠ 0 := by intro hz; simp [hz] at hD
  have hsmall := longReduceRows_degree D C n R U hD hR
  obtain ⟨q, hrelR, hrelU⟩ := longReduceRows_relation D C n R U
  have hdiv : D ∣ R - (longReduceRows D C n R U).1 := by
    refine ⟨q, ?_⟩
    linear_combination hrelR
  have hmod := Polynomial.mod_eq_of_dvd_sub hdiv
  have hself : (longReduceRows D C n R U).1 % D = (longReduceRows D C n R U).1 :=
    (Polynomial.mod_eq_self_iff hDne).mpr (Polynomial.degree_lt_degree hsmall)
  have hrem : R % D = (longReduceRows D C n R U).1 := hmod.trans hself
  have hq : q = R / D := by
    apply mul_left_cancel₀ hDne
    have he := EuclideanDomain.div_add_mod R D
    rw [hrem] at he
    linear_combination -hrelR - he
  apply Prod.ext
  · exact hrem.symm
  · rw [hq] at hrelU
    linear_combination -hrelU

theorem shifted_coeff_inside {F : Type} [Field F] (q : F[X]) (a : F) (k i : ℕ) :
    (C a * X ^ k * q).coeff (k + i) = a * q.coeff i := by
  rw [mul_assoc, Polynomial.coeff_C_mul, show k + i = i + k by omega,
    Polynomial.coeff_X_pow_mul]

theorem shifted_coeff_outside {F : Type} [Field F] (q : F[X]) (a : F) (k L j : ℕ)
    (hq : q.natDegree < L) (hj : j < k ∨ k + L ≤ j) :
    (C a * X ^ k * q).coeff j = 0 := by
  rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  split_ifs with hkj
  · have hdeg : q.natDegree < j - k := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
  · exact mul_zero a

/-- A counted-loop rule for mathematical invariants instead of explicit
families of full machine states.  The body returns to the head and decreases
the counter in register 9.  This is a derived rule for the existing `Sem`. -/
theorem Sem.loop_invariant (P : Program) (E : RAMEnv) (base : ℕ) (body : Stmt)
    (hAt : At P base (Stmt.compile (.loop (.neqz r9) body) base))
    (hW : 1 < 2 ^ E.W) (I : ℕ → RAMState → Prop) (B : ℕ)
    (hframe : ∀ n s pc, I n s → I n { s with pc := pc })
    (hcounter : ∀ n s, I n s → s.regs r9 = n)
    (hbody : ∀ n s, I (n + 1) s → s.pc = base →
      Sem P E (base + 1) base { s with pc := base + 1 }
        (fun k s' => k ≤ B ∧ I n s')) :
    ∀ n s, I n s → s.pc = base →
      Sem P E base (base + body.len + 2) s
        (fun k s' => k ≤ (B + 1) * n + 1 ∧ I 0 s') := by
  intro n
  induction n with
  | zero =>
      intro s hI hpc
      have hstop : ¬ Cond.eval (.neqz r9) s := by
        change ¬ s.regs r9 ≠ 0
        rw [hcounter 0 s hI]
        simp
      have he := Sem.loopExit P E base (.neqz r9) body s hAt hW hpc hstop
      refine Sem.mono he ?_
      intro k s' hQ
      obtain ⟨hk, hs⟩ := hQ
      refine ⟨?_, ?_⟩
      · change k = 1 at hk
        omega
      · rw [hs]
        exact hframe 0 s _ hI
  | succ n ih =>
      intro s hI hpc
      have hgo : Cond.eval (.neqz r9) s := by
        change s.regs r9 ≠ 0
        rw [hcounter (n + 1) s hI]
        omega
      obtain ⟨hentry, k, s', hrun, hreturn, hcost, hI'⟩ := hbody n s hI hpc
      have hbodyExact : Sem P E (base + 1) base { s with pc := base + 1 }
          (fun c z => c = k ∧ z = s') :=
        ⟨hentry, k, s', hrun, hreturn, rfl, rfl⟩
      have hstep := Sem.loopStep P E base (.neqz r9) body s s' k hAt hW hpc hgo hbodyExact
      have hrest := ih s' hI' hreturn
      have hseq := Sem.seq (Q₁ := fun c z => c = 1 + k ∧ z = s')
        (Q₂ := fun c₁ c₂ z => c₁ = 1 + k ∧ c₂ ≤ (B + 1) * n + 1 ∧ I 0 z) hstep
        (fun c₁ z hQ => by
          obtain ⟨hc, hz⟩ := hQ
          subst z
          exact Sem.mono hrest (fun _ _ h => ⟨hc, h⟩))
      refine Sem.mono hseq ?_
      intro c z hQ
      obtain ⟨c₁, c₂, hc, hc₁, hc₂, hz⟩ := hQ
      refine ⟨?_, hz⟩
      rw [Nat.mul_succ]
      omega

theorem axpyArgs_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (E : RAMEnv) (pc dst src L : ℕ)
    (a : F) (x y : ℕ → F) (m : ℕ → ℕ)
    (hwidth : (68 : ℕ) < 2 ^ E.W) (hdst : dst < 2 ^ E.W) (hsrc : src < 2 ^ E.W)
    (hL : L < 2 ^ E.W) (hw : w < 2 ^ E.W) (ha : enc b a < 2 ^ E.W)
    (hm64 : m 64 = dst) (hm65 : m 65 = src) (hm66 : m 66 = L)
    (hm67 : m 67 = w) (hm68 : m 68 = enc b a) :
    runBlock axpyArgsCode E (boundaryState pc m) =
      axpyState b (pc + 12) dst src L a x y m (fun _ => 0) 0 := by
  have hmeta : ∀ k ≤ 68, k % 2 ^ E.W = k := by
    intro k hk
    exact Nat.mod_eq_of_lt (by omega)
  apply ramState_eq_of
  ·     simp only [axpyArgsCode, Fin.isValue, boundaryState, runBlock_cons, execInstr, Function.update_self,
      Nat.zero_mod, runBlock_nil, axpyState, ite_self, Nat.add_right_cancel_iff, Nat.add_left_cancel_iff] <;> omega
  · rfl
  · intro d
    fin_cases d <;>
      simp only [axpyArgsCode, Fin.isValue, boundaryState, runBlock_cons, execInstr, Nat.reduceLeDiff, hmeta,
        Function.update_self, hm64, Nat.mod_eq_of_lt hdst, hm65, Nat.mod_eq_of_lt hsrc, hm66,
        Nat.mod_eq_of_lt hL, hm67, Nat.mod_eq_of_lt hw, Std.le_refl, hm68, Nat.mod_eq_of_lt ha,
        Nat.one_le_ofNat, zero_le, runBlock_nil, Fin.zero_eta, ne_eq, Fin.reduceEq, not_false_eq_true,
        Function.update_of_ne, zero_ne_one, axpyState, ite_self, ↓reduceIte, Fin.mk_one, one_ne_zero,
        Fin.reduceFinMk]

/-- Calling convention for the row-operation procedure.  Registers are zero
at both boundaries; the mathematical memory update is the entire effect. -/
theorem axpyProcedure_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (pc dst src L : ℕ) (a : F) (x y : ℕ → F) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile axpyProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (hdstWord : dst < 2 ^ E.W) (hsrcWord : src < 2 ^ E.W)
    (hL : L < 2 ^ E.W) (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src)
    (hx : ∀ i < L, m (src + i) = enc b (x i))
    (hy : ∀ i < L, m (dst + i) = enc b (y i))
    (hm64 : m 64 = dst) (hm65 : m 65 = src) (hm66 : m 66 = L)
    (hm67 : m 67 = w) (hm68 : m 68 = enc b a) :
    Sem P E pc (pc + 52) (boundaryState pc m)
      (fun k s' => k ≤ 24 * L + 30 ∧
        s' = boundaryState (pc + 52) (writeArray dst m (fun i => enc b (a * x i + y i)) L)) := by
  obtain ⟨hArgsAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hLoopAt, hZeroAt⟩ := At.seqStmt hRestAt
  have hpow : (2 : ℕ) ^ w ≤ 2 ^ E.W := by
    rw [hW]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hwidth : (68 : ℕ) < 2 ^ E.W := by
    have hb : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (68 : ℕ) < 2 ^ 8) hb
  have hwWord : w < 2 ^ E.W := lt_of_lt_of_le (Nat.lt_two_pow_self (n := w)) hpow
  have haWord : enc b a < 2 ^ E.W := lt_of_lt_of_le (enc_lt b a) hpow
  have hArgs := Sem.block P E pc axpyArgsCode (boundaryState pc m) hArgsAt
    (by simp [axpyArgsCode]) rfl
  have hArgs' : Sem P E pc (pc + 12) (boundaryState pc m)
      (fun k s' => k = 12 ∧ s' = axpyState b (pc + 12) dst src L a x y m (fun _ => 0) 0) := by
    refine Sem.mono hArgs ?_
    intro k s' hQ
    obtain ⟨hk, hs⟩ := hQ
    refine ⟨hk, ?_⟩
    rw [hs]
    exact axpyArgs_spec b E pc dst src L a x y m hwidth hdstWord hsrcWord hL hwWord haWord
      hm64 hm65 hm66 hm67 hm68
  have hLoop := axpyArray_spec b ι t N P E (pc + 12) dst src L a x y m (fun _ => 0) hLoopAt
    hw hW hdet hL hdst hsrc hdisj hx hy
  have hCombined := Sem.seq (Q₂ := fun k₁ k₂ s' => k₁ = 12 ∧ k₂ ≤ 24 * L + 2 ∧
      s' = { axpyState b (pc + 12) dst src L a x y m (fun _ => 0) L with pc := pc + 36 })
    hArgs' (fun k₁ s₁ hQ => by
      obtain ⟨hk, hs⟩ := hQ
      rw [hs]
      exact Sem.mono hLoop (fun _ _ h => ⟨hk, h⟩))
  have hFull := Sem.seq (Q₁ := fun k s' => k ≤ 24 * L + 14 ∧
      s' = { axpyState b (pc + 12) dst src L a x y m (fun _ => 0) L with pc := pc + 36 })
    (Q₂ := fun k₁ k₂ s' => k₁ ≤ 24 * L + 14 ∧ k₂ = 16 ∧
      s' = boundaryState (pc + 52) (writeArray dst m (fun i => enc b (a * x i + y i)) L))
    (Sem.mono hCombined (fun k s' hQ => by
      obtain ⟨k₁, k₂, hk, h₁, h₂, hs⟩ := hQ
      exact ⟨by omega, hs⟩))
    (fun k₁ s₁ hQ => by
      obtain ⟨hk, hs⟩ := hQ
      have hz := Sem.block P E (pc + 36) zeroRegsCode s₁ hZeroAt
        (by simp [zeroRegsCode]) (by rw [hs])
      refine Sem.mono hz ?_
      intro k₂ s₂ hQ₂
      obtain ⟨hk₂, hs₂⟩ := hQ₂
      refine ⟨hk, hk₂, ?_⟩
      rw [hs₂, zeroRegs_spec, hs]
      rfl)
  refine Sem.mono hFull ?_
  intro k s' hQ
  obtain ⟨k₁, k₂, hk, h₁, h₂, hs⟩ := hQ
  exact ⟨by omega, hs⟩

/-- Unconditional instruction semantics; bounds are discharged by callers. -/
theorem metaRead_spec (E : RAMEnv) (s : RAMState) (d : Fin 16) (addr : ℕ) (hd : d ≠ r15) :
    runBlock (metaReadCode d addr) E s =
      { s with pc := s.pc + 3, regs := Function.update (Function.update s.regs d (s.mem (addr % 2 ^ E.W) % 2 ^ E.W)) r15 0 } := by
  apply ramState_eq_of
  · simp [metaReadCode, runBlock_cons, runBlock_nil, execInstr] <;> omega
  · rfl
  · intro k
    by_cases hk : k = r15
    · subst k
      simp [metaReadCode, runBlock_cons, runBlock_nil, execInstr]
    · by_cases hkd : k = d
      · subst k
        simp [metaReadCode, runBlock_cons, runBlock_nil, execInstr, hd]
      · simp [metaReadCode, runBlock_cons, runBlock_nil, execInstr, hk, hkd]

theorem metaStore_spec (E : RAMEnv) (s : RAMState) (d : Fin 16) (addr : ℕ) (hd : d ≠ r15) :
    runBlock (metaStoreCode d addr) E s =
      { s with pc := s.pc + 3, regs := Function.update s.regs r15 0, mem := Function.update s.mem (addr % 2 ^ E.W) (s.regs d) } := by
  apply ramState_eq_of
  · simp [metaStoreCode, runBlock_cons, runBlock_nil, execInstr] <;> omega
  · simp [metaStoreCode, runBlock_cons, runBlock_nil, execInstr, hd]
  · intro k
    by_cases hk : k = r15
    · subst k
      simp [metaStoreCode, runBlock_cons, runBlock_nil, execInstr]
    · simp [metaStoreCode, runBlock_cons, runBlock_nil, execInstr, hk]

/-- Compute the cancellation scalar and prepare the first row operation.
The inverse leading coefficient is cached once per polynomial division. -/
theorem longDivPrepare_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) (E : RAMEnv)
    (s : RAMState) (R D : F[X]) (Rbase Dbase d n L cap : ℕ)
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (hAddr : Rbase + n + d < 2 ^ E.W) (hDbase : Dbase < 2 ^ E.W)
    (hStep : n + 1 < 2 ^ E.W) (hL : L < 2 ^ E.W) (hcap : d + n < cap)
    (hR : PolynomialStored b s.mem Rbase cap R)
    (hm72 : s.mem 72 = Rbase) (hm74 : s.mem 74 = Dbase)
    (hm71 : s.mem 71 = n + 1) (hm69 : s.mem 69 = d)
    (hm70 : s.mem 70 = enc b D.leadingCoeff⁻¹)
    (hm77 : s.mem 77 = w) (hm76 : s.mem 76 = L) :
    runBlock longDivPrepareCode E s = boundaryState (s.pc + 64)
      (rowArguments s.mem (Rbase + n) Dbase L w (enc b (R.coeff (d + n) * D.leadingCoeff⁻¹))) := by
  have hpow : (2 : ℕ) ^ w ≤ 2 ^ E.W := by
    rw [hW]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hwidth : (77 : ℕ) < 2 ^ E.W := by
    have hb : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (77 : ℕ) < 2 ^ 8) hb
  have hmeta : ∀ k ≤ 77, k % 2 ^ E.W = k := by
    intro k hk
    exact Nat.mod_eq_of_lt (by omega)
  have hRword : Rbase % 2 ^ E.W = Rbase := Nat.mod_eq_of_lt (by omega)
  have hDword : Dbase % 2 ^ E.W = Dbase := Nat.mod_eq_of_lt hDbase
  have hdword : d % 2 ^ E.W = d := Nat.mod_eq_of_lt (by omega)
  have hnword : (n + 1) % 2 ^ E.W = n + 1 := Nat.mod_eq_of_lt hStep
  have hDstword : (Rbase + n) % 2 ^ E.W = Rbase + n := Nat.mod_eq_of_lt (by omega)
  have hAddrword : (Rbase + n + d) % 2 ^ E.W = Rbase + n + d := Nat.mod_eq_of_lt hAddr
  have hWword : w % 2 ^ E.W = w :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.lt_two_pow_self (n := w)) hpow)
  have hLword : L % 2 ^ E.W = L := Nat.mod_eq_of_lt hL
  have hEnc (z : F) : enc b z % 2 ^ E.W = enc b z :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le (enc_lt b z) hpow)
  have hSub : (n + 1 + 2 ^ E.W - 1) % 2 ^ E.W = n := by
    have heq : n + 1 + 2 ^ E.W - 1 = n + 2 ^ E.W := by omega
    rw [heq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (show n < 2 ^ E.W by omega)]
  have hmR : s.mem (Rbase + n + d) = enc b (R.coeff (d + n)) := by
    rw [show Rbase + n + d = Rbase + (d + n) by omega]
    exact hR (d + n) hcap
  let sA := runBlock longDivReadCode E s
  have hA3 : sA.regs r3 = w := by
    simp only [longDivReadCode, Fin.isValue, List.append_assoc, runBlock_append, ne_eq, Fin.reduceEq,
      not_false_eq_true, metaRead_spec, Nat.reduceLeDiff, hmeta, Std.le_refl, hm77, hWword, runBlock_cons,
      execInstr, Nat.one_le_ofNat, Function.update_of_ne, Function.update_self, Nat.add_mod_mod,
      Nat.mod_add_mod, runBlock_nil, sA]
  have hA10 : sA.regs r10 = enc b (R.coeff (d + n)) := by
    simp only [longDivReadCode, Fin.isValue, List.append_assoc, runBlock_append, ne_eq, Fin.reduceEq,
      not_false_eq_true, metaRead_spec, Nat.reduceLeDiff, hmeta, hm72, hRword, hm74, hDword, hm71, hnword,
      hm69, hdword, hm70, hEnc, Std.le_refl, hm77, hWword, runBlock_cons, execInstr, Nat.one_le_ofNat,
      Function.update_of_ne, Function.update_self, Nat.succ_add_sub_one, Nat.add_mod_right, Nat.add_mod_mod,
      hDstword, hAddrword, hmR, runBlock_nil, sA]
  have hA11 : sA.regs r11 = enc b D.leadingCoeff⁻¹ := by
    simp only [longDivReadCode, Fin.isValue, List.append_assoc, runBlock_append, ne_eq, Fin.reduceEq,
      not_false_eq_true, metaRead_spec, Nat.reduceLeDiff, hmeta, hm70, hEnc, Std.le_refl, runBlock_cons,
      execInstr, Nat.one_le_ofNat, Function.update_of_ne, Function.update_self, Nat.add_mod_mod,
      Nat.mod_add_mod, runBlock_nil, sA]
  have hA2 : sA.regs r2 = Rbase + n := by
    simp only [longDivReadCode, Fin.isValue, List.append_assoc, runBlock_append, ne_eq, Fin.reduceEq,
      not_false_eq_true, metaRead_spec, Nat.reduceLeDiff, hmeta, hm72, hRword, hm71, hnword, Std.le_refl,
      runBlock_cons, execInstr, Nat.one_le_ofNat, Function.update_of_ne, Function.update_self,
      Nat.succ_add_sub_one, Nat.add_mod_right, Nat.add_mod_mod, hDstword, runBlock_nil,
      Nat.add_left_cancel_iff, sA]
  have hA4 : sA.regs r4 = Dbase := by
    simp only [longDivReadCode, Fin.isValue, List.append_assoc, runBlock_append, ne_eq, Fin.reduceEq,
      not_false_eq_true, metaRead_spec, Nat.reduceLeDiff, hmeta, hm74, hDword, Std.le_refl, runBlock_cons,
      execInstr, Nat.one_le_ofNat, Function.update_of_ne, Function.update_self, Nat.add_mod_mod,
      Nat.mod_add_mod, runBlock_nil, sA]
  have hmA : sA.mem = s.mem := rfl
  have hMul := fieldMulCode_spec b ι t N E sA (R.coeff (d + n)) D.leadingCoeff⁻¹
    hw hW hdet hA3 hA10 hA11
  let sB := runBlock longDivWriteCode E (runBlock fieldMulCode E sA)
  have hfinish : runBlock longDivPrepareCode E s = boundaryState (sB.pc + 16) sB.mem := by
    calc
      runBlock longDivPrepareCode E s = runBlock zeroRegsCode E sB := by
        simp only [longDivPrepareCode, runBlock_append] <;> rfl
      _ = _ := zeroRegs_spec E sB
  have hpc : sB.pc + 16 = s.pc + 64 := by
    have hp := runBlock_pc longDivPrepareCode E s (by
      simp [longDivPrepareCode, longDivReadCode, longDivWriteCode, metaReadCode,
        metaStoreCode, fieldMulCode, zeroRegsCode])
    rw [hfinish] at hp
    exact hp
  have hmem : sB.mem = rowArguments s.mem (Rbase + n) Dbase L w
      (enc b (R.coeff (d + n) * D.leadingCoeff⁻¹)) := by
    dsimp only [sB]
    rw [hMul]
    simp only [longDivWriteCode, Fin.isValue, List.append_assoc, hmA, runBlock_append, ne_eq, Fin.reduceEq,
      not_false_eq_true, metaStore_spec, Nat.reduceLeDiff, hmeta, Function.update_self, Function.update_idem,
      Function.update_of_ne, hA2, hA4, metaRead_spec, Nat.reduceEqDiff, hm76, hLword, hA3, rowArguments]
  rw [hfinish, hpc, hmem]

theorem shiftedArguments_spec (E : RAMEnv) (s : RAMState) (dstSlot srcSlot dst src n : ℕ)
    (hwidth : (71 : ℕ) < 2 ^ E.W) (hdstSlot : dstSlot < 2 ^ E.W)
    (hsrcSlot : srcSlot < 2 ^ E.W) (hdst : dst + n < 2 ^ E.W)
    (hsrc : src < 2 ^ E.W) (hn : n + 1 < 2 ^ E.W)
    (hmDst : s.mem dstSlot = dst) (hmSrc : s.mem srcSlot = src)
    (hmN : s.mem 71 = n + 1) :
    runBlock (shiftedArgumentsCode dstSlot srcSlot) E s = boundaryState (s.pc + 34)
      (Function.update (Function.update s.mem 64 (dst + n)) 65 src) := by
  have hmeta : ∀ k ≤ 71, k % 2 ^ E.W = k := by
    intro k hk
    exact Nat.mod_eq_of_lt (by omega)
  have hdst0 : dst % 2 ^ E.W = dst := Nat.mod_eq_of_lt (by omega)
  have hdstn : (dst + n) % 2 ^ E.W = dst + n := Nat.mod_eq_of_lt hdst
  have hsrc0 : src % 2 ^ E.W = src := Nat.mod_eq_of_lt hsrc
  have hn0 : (n + 1) % 2 ^ E.W = n + 1 := Nat.mod_eq_of_lt hn
  have hpred : (n + 1 + 2 ^ E.W - 1) % 2 ^ E.W = n := by
    have heq : n + 1 + 2 ^ E.W - 1 = n + 2 ^ E.W := by omega
    rw [heq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (show n < 2 ^ E.W by omega)]
  have hdstSlot0 : dstSlot % 2 ^ E.W = dstSlot := Nat.mod_eq_of_lt hdstSlot
  have hsrcSlot0 : srcSlot % 2 ^ E.W = srcSlot := Nat.mod_eq_of_lt hsrcSlot
  have hrun : runBlock (shiftedArgumentsCode dstSlot srcSlot) E s =
      runBlock zeroRegsCode E (runBlock (metaStoreCode r4 65) E
        (runBlock (metaStoreCode r2 64) E (runBlock
          (metaReadCode r2 dstSlot ++ metaReadCode r4 srcSlot ++ metaReadCode r9 71 ++
            [iImm r6 1, iSub r9 r9 r6, iAdd r2 r2 r9]) E s))) := by
    simp only [shiftedArgumentsCode, runBlock_append] <;> rfl
  rw [hrun, zeroRegs_spec]
  have hlen : (shiftedArgumentsCode dstSlot srcSlot).length = 34 := rfl
  apply ramState_eq_of
  · have hp := runBlock_pc (shiftedArgumentsCode dstSlot srcSlot) E s (by
      simp [shiftedArgumentsCode, metaReadCode, metaStoreCode, zeroRegsCode])
    rw [hrun, zeroRegs_spec] at hp
    simpa only [hlen, boundaryState] using hp
  · simp [runBlock_append, metaRead_spec, metaStore_spec, runBlock_cons, runBlock_nil,
      execInstr, hmeta, hdstSlot0, hsrcSlot0, hmDst, hmSrc, hmN,
      hdst0, hdstn, hsrc0, hn0, hpred, boundaryState]
  · intro _; rfl

theorem longDivTail_spec (E : RAMEnv) (s : RAMState) (n : ℕ)
    (hwidth : (71 : ℕ) < 2 ^ E.W) (hn : n + 1 < 2 ^ E.W) (hm : s.mem 71 = n + 1) :
    runBlock longDivTailCode E s = rankState (s.pc + 27) (Function.update s.mem 71 n) n := by
  have hmeta : ∀ k ≤ 71, k % 2 ^ E.W = k := by
    intro k hk
    exact Nat.mod_eq_of_lt (by omega)
  have hn0 : (n + 1) % 2 ^ E.W = n + 1 := Nat.mod_eq_of_lt hn
  have hn1 : n % 2 ^ E.W = n := Nat.mod_eq_of_lt (by omega)
  have hpred : (n + 1 + 2 ^ E.W - 1) % 2 ^ E.W = n := by
    have heq : n + 1 + 2 ^ E.W - 1 = n + 2 ^ E.W := by omega
    rw [heq]
    simp [Nat.add_mod, hn1]
  apply ramState_eq_of
  · have hp := runBlock_pc longDivTailCode E s (by
      simp [longDivTailCode, metaReadCode, metaStoreCode, zeroRegsCode])
    exact hp
  ·     simp only [longDivTailCode, Fin.isValue, List.append_assoc, List.cons_append, List.nil_append,
      runBlock_append, ne_eq, Fin.reduceEq, not_false_eq_true, metaRead_spec, Std.le_refl, hmeta, hm, hn0,
      runBlock_cons, execInstr, Nat.one_le_ofNat, Function.update_of_ne, Function.update_self,
      Nat.succ_add_sub_one, Nat.add_mod_right, hn1, metaStore_spec, zeroRegs_spec, boundaryState, rankState]
  · intro d
    fin_cases d <;>                     simp only [longDivTailCode, Fin.isValue, List.append_assoc, List.cons_append,
                      List.nil_append, runBlock_append, ne_eq, Fin.reduceEq, not_false_eq_true,
                      metaRead_spec, Std.le_refl, hmeta, hm, hn0, runBlock_cons, execInstr, Nat.one_le_ofNat,
                      Function.update_of_ne, Function.update_self, Nat.succ_add_sub_one, Nat.add_mod_right,
                      hn1, metaStore_spec, zeroRegs_spec, boundaryState, Fin.zero_eta, rankState, Fin.mk_one,
                      Fin.reduceFinMk]

theorem rowArguments_frame (m : ℕ → ℕ) (dst src L w scalar addr : ℕ)
    (ha : addr < 64 ∨ 69 ≤ addr) : rowArguments m dst src L w scalar addr = m addr := by
  have h64 : addr ≠ 64 := by omega
  have h65 : addr ≠ 65 := by omega
  have h66 : addr ≠ 66 := by omega
  have h67 : addr ≠ 67 := by omega
  have h68 : addr ≠ 68 := by omega
  simp [rowArguments, h64, h65, h66, h67, h68]

theorem PolynomialStored.rowArguments {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {m : ℕ → ℕ} {B cap : ℕ} {p : F[X]}
    (hp : PolynomialStored b m B cap p) (hB : 128 ≤ B) (dst src L dim scalar : ℕ) :
    PolynomialStored b (rowArguments m dst src L dim scalar) B cap p := by
  intro i hi
  rw [rowArguments_frame _ _ _ _ _ _ _ (Or.inr (by omega))]
  exact hp i hi

theorem PolynomialStored.meta_update {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {m : ℕ → ℕ} {B cap : ℕ} {p : F[X]}
    (hp : PolynomialStored b m B cap p) (hB : 128 ≤ B) (slot value : ℕ) (hslot : slot < 128) :
    PolynomialStored b (Function.update m slot value) B cap p := by
  intro i hi
  rw [Function.update_of_ne (by omega : B + i ≠ slot)]
  exact hp i hi

theorem PolynomialStored.write_disjoint {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {m : ℕ → ℕ} {B cap : ℕ} {p : F[X]}
    (hp : PolynomialStored b m B cap p) (dst L : ℕ) (f : ℕ → ℕ)
    (hdisj : dst + L ≤ B ∨ B + cap ≤ dst) :
    PolynomialStored b (writeArray dst m f L) B cap p := by
  intro i hi
  rw [writeArray_frame dst m f L (B + i) (by omega)]
  exact hp i hi

theorem writeArray_meta (dst : ℕ) (m f : ℕ → ℕ) (L slot : ℕ)
    (hdst : 128 ≤ dst) (hslot : slot < 128) : writeArray dst m f L slot = m slot :=
  writeArray_frame dst m f L slot (Or.inl (by omega))

/-- Pure memory effect of the shifted coefficient loop. -/
theorem PolynomialStored.shift_write {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {m : ℕ → ℕ} {B cap : ℕ} {p : F[X]}
    (hp : PolynomialStored b m B cap p) (a : F) (q : F[X]) (k L : ℕ)
    (hcap : k + L ≤ cap) (hq : q.natDegree < L) :
    PolynomialStored b
      (writeArray (B + k) m (fun i => enc b (a * q.coeff i + p.coeff (k + i))) L)
      B cap (p + C a * X ^ k * q) := by
  intro j hj
  by_cases hout : j < k ∨ k + L ≤ j
  · rw [writeArray_frame _ _ _ _ (B + j) (by omega), hp j hj]
    rw [Polynomial.coeff_add, shifted_coeff_outside q a k L j hq hout, add_zero]
  · have hkj : k ≤ j := by omega
    have hi : j - k < L := by omega
    have haddr : B + j = B + k + (j - k) := by omega
    rw [haddr, writeArray_get _ _ _ L (j - k) hi]
    congr 1
    have hcoeff : (p + C a * X ^ k * q).coeff j =
        p.coeff (k + (j - k)) + a * q.coeff (j - k) := by
      conv_lhs => rw [show j = k + (j - k) by omega]
      rw [Polynomial.coeff_add, shifted_coeff_inside]
    rw [hcoeff]
    ring

/-- The two destination arrays represent exactly the coupled long-division
step; both divisor arrays remain unchanged. -/
theorem rowIterationMemory_stored {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (m : ℕ → ℕ) (RB UB DB CB n L cap : ℕ)
    (R U D C : F[X]) (hl : RowsLayout RB UB DB CB cap) (hcap : n + L ≤ cap)
    (hD : D.natDegree < L) (hC : C.natDegree < L)
    (hRmem : PolynomialStored b m RB cap R) (hUmem : PolynomialStored b m UB cap U)
    (hDmem : PolynomialStored b m DB cap D) (hCmem : PolynomialStored b m CB cap C) :
    let m' := rowIterationMemory b m RB UB DB CB n L R U D C
    PolynomialStored b m' RB cap (R - leadingCancel D R n * D) ∧
      PolynomialStored b m' UB cap (U - leadingCancel D R n * C) ∧
      PolynomialStored b m' DB cap D ∧ PolynomialStored b m' CB cap C := by
  let a := R.coeff (D.natDegree + n) * D.leadingCoeff⁻¹
  let m1 := rowArguments m (RB + n) DB L w (enc b a)
  let fR := fun i => enc b (a * D.coeff i + R.coeff (n + i))
  let m2 := writeArray (RB + n) m1 fR L
  let m3 := Function.update (Function.update m2 64 (UB + n)) 65 CB
  let fU := fun i => enc b (a * C.coeff i + U.coeff (n + i))
  let m4 := writeArray (UB + n) m3 fU L
  change PolynomialStored b (Function.update m4 71 n) RB cap (R - leadingCancel D R n * D) ∧
    PolynomialStored b (Function.update m4 71 n) UB cap (U - leadingCancel D R n * C) ∧
    PolynomialStored b (Function.update m4 71 n) DB cap D ∧ PolynomialStored b (Function.update m4 71 n) CB cap C
  have hR1 := hRmem.rowArguments hl.Rlow (RB + n) DB L w (enc b a)
  have hU1 := hUmem.rowArguments hl.Ulow (RB + n) DB L w (enc b a)
  have hD1 := hDmem.rowArguments hl.Dlow (RB + n) DB L w (enc b a)
  have hC1 := hCmem.rowArguments hl.Clow (RB + n) DB L w (enc b a)
  have hR2 : PolynomialStored b m2 RB cap (R + Polynomial.C a * X ^ n * D) :=
    hR1.shift_write a D n L hcap hD
  have hU2 : PolynomialStored b m2 UB cap U :=
    hU1.write_disjoint (RB + n) L fR (by have h := hl.RU; omega)
  have hD2 : PolynomialStored b m2 DB cap D :=
    hD1.write_disjoint (RB + n) L fR (by have h := hl.RD; omega)
  have hC2 : PolynomialStored b m2 CB cap C :=
    hC1.write_disjoint (RB + n) L fR (by have h := hl.RC; omega)
  have hR3 := (hR2.meta_update hl.Rlow 64 (UB + n) (by norm_num)).meta_update hl.Rlow 65 CB (by norm_num)
  have hU3 := (hU2.meta_update hl.Ulow 64 (UB + n) (by norm_num)).meta_update hl.Ulow 65 CB (by norm_num)
  have hD3 := (hD2.meta_update hl.Dlow 64 (UB + n) (by norm_num)).meta_update hl.Dlow 65 CB (by norm_num)
  have hC3 := (hC2.meta_update hl.Clow 64 (UB + n) (by norm_num)).meta_update hl.Clow 65 CB (by norm_num)
  have hR4 : PolynomialStored b m4 RB cap (R + Polynomial.C a * X ^ n * D) :=
    hR3.write_disjoint (UB + n) L fU (by have h := hl.RU; omega)
  have hU4 : PolynomialStored b m4 UB cap (U + Polynomial.C a * X ^ n * C) :=
    hU3.shift_write a C n L hcap hC
  have hD4 : PolynomialStored b m4 DB cap D :=
    hD3.write_disjoint (UB + n) L fU (by have h := hl.UD; omega)
  have hC4 : PolynomialStored b m4 CB cap C :=
    hC3.write_disjoint (UB + n) L fU (by have h := hl.UC; omega)
  have hR5 := hR4.meta_update hl.Rlow 71 n (by norm_num)
  have hU5 := hU4.meta_update hl.Ulow 71 n (by norm_num)
  have hD5 := hD4.meta_update hl.Dlow 71 n (by norm_num)
  have hC5 := hC4.meta_update hl.Clow 71 n (by norm_num)
  haveI : CharP F 2 := pinsketch_charP
  haveI : CharP F[X] 2 := inferInstance
  refine ⟨?_, ?_, hD5, hC5⟩
  · simpa only [leadingCancel, div_eq_mul_inv, CharTwo.sub_eq_add, a] using hR5
  · simpa only [leadingCancel, div_eq_mul_inv, CharTwo.sub_eq_add, a] using hU5

theorem RowsLayout.swap {R U D C cap : ℕ} (h : RowsLayout R U D C cap) :
    RowsLayout D C R U cap :=
  ⟨h.Dlow, h.Clow, h.Rlow, h.Ulow, h.DC, h.RD.elim Or.inr Or.inl,
    h.UD.elim Or.inr Or.inl, h.RC.elim Or.inr Or.inl, h.UC.elim Or.inr Or.inl, h.RU⟩

theorem rowIterationMemory_counter {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (m : ℕ → ℕ) (RB UB DB CB n L : ℕ)
    (R U D C : F[X]) : rowIterationMemory b m RB UB DB CB n L R U D C 71 = n := by
  simp [rowIterationMemory]

theorem rowIterationMemory_meta {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (m : ℕ → ℕ) (RB UB DB CB n L : ℕ)
    (R U D C : F[X]) (hR : 128 ≤ RB) (hU : 128 ≤ UB) (slot : ℕ)
    (hslot : slot < 128) (hlarge : 69 ≤ slot) (hne : slot ≠ 71) :
    rowIterationMemory b m RB UB DB CB n L R U D C slot = m slot := by
  have hRm (m' f : ℕ → ℕ) : writeArray (RB + n) m' f L slot = m' slot :=
    writeArray_meta _ _ _ _ _ (by omega) hslot
  have hUm (m' f : ℕ → ℕ) : writeArray (UB + n) m' f L slot = m' slot :=
    writeArray_meta _ _ _ _ _ (by omega) hslot
  have h64 : slot ≠ 64 := by omega
  have h65 : slot ≠ 65 := by omega
  have h66 : slot ≠ 66 := by omega
  have h67 : slot ≠ 67 := by omega
  have h68 : slot ≠ 68 := by omega
  simp [rowIterationMemory, rowArguments, Function.update_apply,
    hRm, hUm, h64, h65, h66, h67, h68, hne]

/-- The complete machine body performs the two shifted row updates and
returns a canonical state with the decreased loop counter. -/
theorem longDivBody_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (pc RB UB DB CB n L cap : ℕ)
    (R U D C : F[X]) (s : RAMState)
    (hAt : At P pc (Stmt.compile longDivBodyStmt pc)) (hpc : s.pc = pc)
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (hl : RowsLayout RB UB DB CB cap) (hcap : n + L ≤ cap)
    (hRword : RB + cap ≤ 2 ^ E.W) (hUword : UB + cap ≤ 2 ^ E.W)
    (hDword : DB + cap ≤ 2 ^ E.W) (hCword : CB + cap ≤ 2 ^ E.W)
    (hD : D.natDegree < L) (hC : C.natDegree < L)
    (hRW : RB + cap ≤ 2 ^ E.W) (hUW : UB + cap ≤ 2 ^ E.W)
    (hDW : DB + cap ≤ 2 ^ E.W) (hCW : CB + cap ≤ 2 ^ E.W)
    (hRm : PolynomialStored b s.mem RB cap R) (hUm : PolynomialStored b s.mem UB cap U)
    (hDm : PolynomialStored b s.mem DB cap D) (hCm : PolynomialStored b s.mem CB cap C)
    (hm69 : s.mem 69 = D.natDegree) (hm70 : s.mem 70 = enc b D.leadingCoeff⁻¹)
    (hm71 : s.mem 71 = n + 1) (hm72 : s.mem 72 = RB) (hm73 : s.mem 73 = UB)
    (hm74 : s.mem 74 = DB) (hm75 : s.mem 75 = CB) (hm76 : s.mem 76 = L)
    (hm77 : s.mem 77 = w) :
    Sem P E pc (pc + 229) s
      (fun k s' => k ≤ 48 * L + 185 ∧
        s' = rankState (pc + 229) (rowIterationMemory b s.mem RB UB DB CB n L R U D C) n) := by
  let m := s.mem
  let a := R.coeff (D.natDegree + n) * D.leadingCoeff⁻¹
  let m1 := rowArguments m (RB + n) DB L w (enc b a)
  let fR := fun i => enc b (a * D.coeff i + R.coeff (n + i))
  let m2 := writeArray (RB + n) m1 fR L
  let m3 := Function.update (Function.update m2 64 (UB + n)) 65 CB
  let fU := fun i => enc b (a * C.coeff i + U.coeff (n + i))
  let m4 := writeArray (UB + n) m3 fU L
  have hLcap : L ≤ cap := by omega
  have hLpos : 1 ≤ L := by omega
  have hLword : L < 2 ^ E.W := by have h := hl.Rlow; omega
  have hnword : n + 1 < 2 ^ E.W := by have h := hl.Rlow; omega
  have hAddr : RB + n + D.natDegree < 2 ^ E.W := by omega
  have hRB : RB + n < 2 ^ E.W := by omega
  have hUB : UB + n < 2 ^ E.W := by omega
  have hDB : DB < 2 ^ E.W := by omega
  have hCB : CB < 2 ^ E.W := by omega
  have hWidth : (77 : ℕ) < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (77 : ℕ) < 2 ^ 8) hp
  have hSmall (i : ℕ) (hi : i ≤ 77) : i < 2 ^ E.W := by omega
  obtain ⟨hPrepareAt, hRest1⟩ := At.seqStmt hAt
  obtain ⟨hAxpy1At, hRest2⟩ := At.seqStmt hRest1
  obtain ⟨hSecondAt, hRest3⟩ := At.seqStmt hRest2
  obtain ⟨hAxpy2At, hTailAt⟩ := At.seqStmt hRest3
  have hPrepareRun : runBlock longDivPrepareCode E s = boundaryState (pc + 64) m1 := by
    simpa only [hpc, m1, m, a] using longDivPrepare_spec b ι t N E s R D RB DB D.natDegree n L cap
      hw hW hdet hAddr hDB hnword hLword (by omega) hRm hm72 hm74 hm71 hm69 hm70 hm77 hm76
  have hPrepare : Sem P E pc (pc + 64) s
      (fun k z => k ≤ 64 ∧ z = boundaryState (pc + 64) m1) := by
    refine Sem.mono (Sem.block P E pc longDivPrepareCode s hPrepareAt
      (by simp [longDivPrepareCode, longDivReadCode, longDivWriteCode, metaReadCode,
        metaStoreCode, fieldMulCode, zeroRegsCode]) hpc) ?_
    intro k z hQ
    obtain ⟨hk, hz⟩ := hQ
    refine ⟨by change k = 64 at hk; omega, ?_⟩
    rw [hz, hPrepareRun]
  have hR1 : PolynomialStored b m1 RB cap R := hRm.rowArguments hl.Rlow _ _ _ _ _
  have hU1 : PolynomialStored b m1 UB cap U := hUm.rowArguments hl.Ulow _ _ _ _ _
  have hD1 : PolynomialStored b m1 DB cap D := hDm.rowArguments hl.Dlow _ _ _ _ _
  have hC1 : PolynomialStored b m1 CB cap C := hCm.rowArguments hl.Clow _ _ _ _ _
  have hAxpy1 : Sem P E (pc + 64) (pc + 116) (boundaryState (pc + 64) m1)
      (fun k z => k ≤ 24 * L + 30 ∧ z = boundaryState (pc + 116) m2) := by
    exact axpyProcedure_spec b ι t N P E (pc + 64) (RB + n) DB L a D.coeff
      (fun i => R.coeff (n + i)) m1 hAxpy1At hw hW hdet hRB hDB hLword
      (by omega) (by omega) (by have h := hl.RD; omega)
      (fun i hi => hD1 i (by omega))
      (fun i hi => by simpa only [Nat.add_assoc] using hR1 (n + i) (by omega))
      (by simp [m1, rowArguments]) (by simp [m1, rowArguments])
      (by simp [m1, rowArguments]) (by simp [m1, rowArguments]) (by simp [m1, rowArguments])
  have hMeta2 (slot : ℕ) (hs : slot < 128) : m2 slot = m1 slot :=
    writeArray_meta _ _ _ _ _ (by have h := hl.Rlow; omega) hs
  have hGlobal2 (slot : ℕ) (hs : slot < 128) (hg : 69 ≤ slot) : m2 slot = m slot := by
    rw [hMeta2 slot hs]
    exact rowArguments_frame _ _ _ _ _ _ _ (Or.inr hg)
  have hSecondRun : runBlock (shiftedArgumentsCode 73 75) E (boundaryState (pc + 116) m2) =
      boundaryState (pc + 150) m3 := by
    exact shiftedArguments_spec E (boundaryState (pc + 116) m2) 73 75 UB CB n
      (hSmall 71 (by norm_num)) (hSmall 73 (by norm_num)) (hSmall 75 (by norm_num))
      hUB hCB hnword
      (by change m2 73 = UB; rw [hGlobal2 73 (by norm_num) (by norm_num)]; exact hm73)
      (by change m2 75 = CB; rw [hGlobal2 75 (by norm_num) (by norm_num)]; exact hm75)
      (by change m2 71 = n + 1; rw [hGlobal2 71 (by norm_num) (by norm_num)]; exact hm71)
  have hSecond : Sem P E (pc + 116) (pc + 150) (boundaryState (pc + 116) m2)
      (fun k z => k ≤ 34 ∧ z = boundaryState (pc + 150) m3) := by
    refine Sem.mono (Sem.block P E (pc + 116) (shiftedArgumentsCode 73 75) _ hSecondAt
      (by simp [shiftedArgumentsCode, metaReadCode, metaStoreCode, zeroRegsCode]) rfl) ?_
    intro k z hQ
    obtain ⟨hk, hz⟩ := hQ
    refine ⟨by change k = 34 at hk; omega, ?_⟩
    rw [hz, hSecondRun]
  have hU2 : PolynomialStored b m2 UB cap U :=
    hU1.write_disjoint (RB + n) L fR (by have h := hl.RU; omega)
  have hC2 : PolynomialStored b m2 CB cap C :=
    hC1.write_disjoint (RB + n) L fR (by have h := hl.RC; omega)
  have hU3 : PolynomialStored b m3 UB cap U :=
    (hU2.meta_update hl.Ulow 64 (UB + n) (by norm_num)).meta_update hl.Ulow 65 CB (by norm_num)
  have hC3 : PolynomialStored b m3 CB cap C :=
    (hC2.meta_update hl.Clow 64 (UB + n) (by norm_num)).meta_update hl.Clow 65 CB (by norm_num)
  have hArg3 (slot : ℕ) (hslot : slot ≠ 64) (hslot' : slot ≠ 65) : m3 slot = m2 slot := by
    simp [m3, hslot, hslot']
  have hAxpy2 : Sem P E (pc + 150) (pc + 202) (boundaryState (pc + 150) m3)
      (fun k z => k ≤ 24 * L + 30 ∧ z = boundaryState (pc + 202) m4) := by
    exact axpyProcedure_spec b ι t N P E (pc + 150) (UB + n) CB L a C.coeff
      (fun i => U.coeff (n + i)) m3 hAxpy2At hw hW hdet hUB hCB hLword
      (by omega) (by omega) (by have h := hl.UC; omega)
      (fun i hi => hC3 i (by omega))
      (fun i hi => by simpa only [Nat.add_assoc] using hU3 (n + i) (by omega))
      (by simp [m3]) (by simp [m3])
      (by rw [hArg3 66 (by norm_num) (by norm_num), hMeta2 66 (by norm_num)]; simp [m1, rowArguments])
      (by rw [hArg3 67 (by norm_num) (by norm_num), hMeta2 67 (by norm_num)]; simp [m1, rowArguments])
      (by rw [hArg3 68 (by norm_num) (by norm_num), hMeta2 68 (by norm_num)]; simp [m1, rowArguments])
  have hTailCounter : m4 71 = n + 1 := by
    change writeArray (UB + n) m3 fU L 71 = n + 1
    rw [writeArray_meta _ _ _ _ _ (by have h := hl.Ulow; omega) (by norm_num),
      hArg3 71 (by norm_num) (by norm_num), hGlobal2 71 (by norm_num) (by norm_num)]
    exact hm71
  have hTailRun : runBlock longDivTailCode E (boundaryState (pc + 202) m4) =
      rankState (pc + 229) (rowIterationMemory b m RB UB DB CB n L R U D C) n := by
    exact longDivTail_spec E _ n (hSmall 71 (by norm_num)) hnword hTailCounter
  have hTail : Sem P E (pc + 202) (pc + 229) (boundaryState (pc + 202) m4)
      (fun k z => k ≤ 27 ∧ z = rankState (pc + 229) (rowIterationMemory b m RB UB DB CB n L R U D C) n) := by
    refine Sem.mono (Sem.block P E (pc + 202) longDivTailCode _ hTailAt
      (by simp [longDivTailCode, metaReadCode, metaStoreCode, zeroRegsCode]) rfl) ?_
    intro k z hQ
    obtain ⟨hk, hz⟩ := hQ
    refine ⟨by change k = 27 at hk; omega, ?_⟩
    rw [hz, hTailRun]
  have h12 := Sem.seq_bound hPrepare (fun z _ hz => by subst z; exact hAxpy1)
  have h123 := Sem.seq_bound h12 (fun z _ hz => by subst z; exact hSecond)
  have h1234 := Sem.seq_bound h123 (fun z _ hz => by subst z; exact hAxpy2)
  have hFull := Sem.seq_bound h1234 (fun z _ hz => by subst z; exact hTail)
  refine Sem.mono hFull ?_
  intro k z hQ
  exact ⟨by have h := hQ.1; omega, hQ.2⟩

theorem MemoryFrame.trans {allowed : ℕ → Prop} {a b c : ℕ → ℕ}
    (h₁ : MemoryFrame allowed a b) (h₂ : MemoryFrame allowed b c) : MemoryFrame allowed a c :=
  fun addr ha => (h₂ addr ha).trans (h₁ addr ha)

theorem rowIterationMemory_frame {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (m : ℕ → ℕ) (RB UB DB CB n L cap : ℕ)
    (R U D C : F[X]) (hcap : n + L ≤ cap) :
    MemoryFrame (divisionWritable RB UB cap) m (rowIterationMemory b m RB UB DB CB n L R U D C) := by
  intro addr ha
  change ¬ ((64 ≤ addr ∧ addr ≤ 68) ∨ addr = 71 ∨
    (RB ≤ addr ∧ addr < RB + cap) ∨ (UB ≤ addr ∧ addr < UB + cap)) at ha
  have harg : addr < 64 ∨ 69 ≤ addr := by omega
  have h71 : addr ≠ 71 := by omega
  have h64 : addr ≠ 64 := by omega
  have h65 : addr ≠ 65 := by omega
  have hR : addr < RB + n ∨ RB + n + L ≤ addr := by omega
  have hU : addr < UB + n ∨ UB + n + L ≤ addr := by omega
  dsimp only [rowIterationMemory]
  rw [Function.update_of_ne h71, writeArray_frame _ _ _ _ addr hU,
    Function.update_of_ne h65, Function.update_of_ne h64,
    writeArray_frame _ _ _ _ addr hR]
  exact rowArguments_frame _ _ _ _ _ _ _ harg

theorem RowCache.of_frame {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {D : F[X]} {RB UB DB CB L n n' : ℕ}
    {m m' : ℕ → ℕ} (h : RowCache b D RB UB DB CB L m n)
    (hf : ∀ slot, 69 ≤ slot → slot < 128 → slot ≠ 71 → m' slot = m slot)
    (hc : m' 71 = n') : RowCache b D RB UB DB CB L m' n' :=
  ⟨(hf 69 (by norm_num) (by norm_num) (by norm_num)).trans h.degree,
    (hf 70 (by norm_num) (by norm_num) (by norm_num)).trans h.inverse, hc,
    (hf 72 (by norm_num) (by norm_num) (by norm_num)).trans h.prevR,
    (hf 73 (by norm_num) (by norm_num) (by norm_num)).trans h.prevC,
    (hf 74 (by norm_num) (by norm_num) (by norm_num)).trans h.curR,
    (hf 75 (by norm_num) (by norm_num) (by norm_num)).trans h.curC,
    (hf 76 (by norm_num) (by norm_num) (by norm_num)).trans h.length,
    (hf 77 (by norm_num) (by norm_num) (by norm_num)).trans h.dim⟩

theorem RowCache.iteration {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {D : F[X]} {RB UB DB CB L n : ℕ}
    {m : ℕ → ℕ} (h : RowCache b D RB UB DB CB L m (n + 1))
    (R U C : F[X]) (hR : 128 ≤ RB) (hU : 128 ≤ UB) :
    RowCache b D RB UB DB CB L (rowIterationMemory b m RB UB DB CB n L R U D C) n := by
  exact h.of_frame
    (fun slot hlo hhi hne => rowIterationMemory_meta b m RB UB DB CB n L R U D C hR hU slot hhi hlo hne)
    (rowIterationMemory_counter b m RB UB DB CB n L R U D C)

/-- Complete counted RAM division of two polynomial rows.  The output is
exactly the abstract quotient/remainder update, and all unrelated memory is
preserved for later decoder stages. -/
theorem longDivLoop_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (base RB UB DB CB L cap n0 : ℕ)
    (R0 U0 D C : F[X]) (m : ℕ → ℕ)
    (hAt : At P base (Stmt.compile longDivStmt base))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (hl : RowsLayout RB UB DB CB cap) (hcap : n0 + L ≤ cap)
    (hRW : RB + cap ≤ 2 ^ E.W) (hUW : UB + cap ≤ 2 ^ E.W)
    (hDW : DB + cap ≤ 2 ^ E.W) (hCW : CB + cap ≤ 2 ^ E.W)
    (hDpos : 0 < D.natDegree) (hD : D.natDegree < L) (hC : C.natDegree < L)
    (hRm : PolynomialStored b m RB cap R0) (hUm : PolynomialStored b m UB cap U0)
    (hDm : PolynomialStored b m DB cap D) (hCm : PolynomialStored b m CB cap C)
    (hc : RowCache b D RB UB DB CB L m n0) (hBound : R0.natDegree < D.natDegree + n0) :
    Sem P E base (base + 231) (rankState base m n0)
      (fun k s' => k ≤ (48 * L + 187) * n0 + 1 ∧
        s'.regs = (fun _ => 0) ∧ RowCache b D RB UB DB CB L s'.mem 0 ∧
        MemoryFrame (divisionWritable RB UB cap) m s'.mem ∧
        PolynomialStored b s'.mem RB cap (R0 % D) ∧
        PolynomialStored b s'.mem UB cap (U0 - (R0 / D) * C) ∧
        PolynomialStored b s'.mem DB cap D ∧ PolynomialStored b s'.mem CB cap C) := by
  let I := longDivInvariant b RB UB DB CB L cap n0 R0 U0 D C m
  have hW1 : 1 < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 1 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2 ^ 1) hp
  have hframe : ∀ n s pc, I n s → I n { s with pc := pc } := by
    intro n s pc h
    simpa only [I, longDivInvariant] using h
  have hcounter : ∀ n s, I n s → s.regs r9 = n := by
    intro n s h
    rw [h.1, Function.update_self]
  obtain ⟨_, _, hBodyAt, hJumpAt⟩ := at_loop hAt
  have hbody : ∀ n s, I (n + 1) s → s.pc = base →
      Sem P E (base + 1) base { s with pc := base + 1 }
        (fun k s' => k ≤ 48 * L + 186 ∧ I n s') := by
    intro n s hI hpc
    obtain ⟨hregs, hcache, hn, hmemFrame, R, U, hRmem, hUmem, hDmem, hCmem, hRbound, hCont⟩ := hI
    have hncap : n + L ≤ cap := by omega
    have hrun := longDivBody_spec b ι t N P E (base + 1) RB UB DB CB n L cap R U D C
      { s with pc := base + 1 } hBodyAt rfl hw hW hdet hl hncap hRW hUW hDW hCW hD hC
      hRW hUW hDW hCW hRmem hUmem hDmem hCmem hcache.degree hcache.inverse hcache.count
      hcache.prevR hcache.prevC hcache.curR hcache.curC hcache.length hcache.dim
    refine Sem.jmp_append (hAt := hJumpAt) (Sem.mono hrun ?_)
    intro k s' hQ
    obtain ⟨hcost, hs⟩ := hQ
    refine ⟨by omega, ?_⟩
    rw [hs]
    change longDivInvariant b RB UB DB CB L cap n0 R0 U0 D C m n _
    obtain ⟨hRnew, hUnew, hDnew, hCnew⟩ := rowIterationMemory_stored b s.mem RB UB DB CB n L cap
      R U D C hl hncap hD hC hRmem hUmem hDmem hCmem
    have hcache' := hcache.iteration R U C hl.Rlow hl.Ulow
    have hframe' := MemoryFrame.trans hmemFrame
      (rowIterationMemory_frame b s.mem RB UB DB CB n L cap R U D C hncap)
    refine ⟨rfl, hcache', by omega, hframe',
      R - leadingCancel D R n * D, U - leadingCancel D R n * C,
      hRnew, hUnew, hDnew, hCnew, leadingCancel_degree D R n hDpos hRbound, ?_⟩
    simpa only [longReduceRows] using hCont
  have hinit : I n0 (rankState base m n0) := by
    refine ⟨rfl, hc, le_rfl, ?_, R0, U0, hRm, hUm, hDm, hCm, hBound, rfl⟩
    intro addr _
    rfl
  have hloop := Sem.loop_invariant P E base longDivBodyStmt hAt hW1 I (48 * L + 186)
    hframe hcounter hbody n0 (rankState base m n0) hinit rfl
  refine Sem.mono hloop ?_
  intro k s' hQ
  obtain ⟨hcost, hI⟩ := hQ
  obtain ⟨hregs, hcache, _, hmemFrame, R, U, hRmem, hUmem, hDmem, hCmem, _, hCont⟩ := hI
  have hrows : (R, U) = (R0 % D, U0 - (R0 / D) * C) := by
    rw [longReduceRows_eq D C n0 R0 U0 hDpos hBound] at hCont
    exact hCont
  have hReq : R = R0 % D := congrArg Prod.fst hrows
  have hUeq : U = U0 - (R0 / D) * C := congrArg Prod.snd hrows
  rw [hReq] at hRmem
  rw [hUeq] at hUmem
  refine ⟨hcost, ?_, hcache, hmemFrame, hRmem, hUmem, hDmem, hCmem⟩
  rw [hregs]
  funext d
  simp [Function.update_apply]

/-- Load the counter at a procedure boundary. -/
theorem rankRead_spec (E : RAMEnv) (pc : ℕ) (m : ℕ → ℕ) (n : ℕ)
    (haddr : (71 : ℕ) < 2 ^ E.W) (hn : n < 2 ^ E.W) (hm : m 71 = n) :
    runBlock (metaReadCode r9 71) E (boundaryState pc m) = rankState (pc + 3) m n := by
  rw [metaRead_spec E _ _ _ (by decide)]
  apply ramState_eq_of
  · rfl
  · rfl
  · intro d
    fin_cases d <;> simp [boundaryState, rankState, hm, Nat.mod_eq_of_lt haddr, Nat.mod_eq_of_lt hn]

/-- Callable RAM quotient/remainder row procedure, returning zero registers.
Its footprint is the two destination buffers and the designated metadata. -/
theorem longDivProcedure_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (base RB UB DB CB L cap n0 : ℕ)
    (R0 U0 D C : F[X]) (m : ℕ → ℕ)
    (hAt : At P base (Stmt.compile longDivProcedure base))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (hl : RowsLayout RB UB DB CB cap) (hcap : n0 + L ≤ cap)
    (hRW : RB + cap ≤ 2 ^ E.W) (hUW : UB + cap ≤ 2 ^ E.W)
    (hDW : DB + cap ≤ 2 ^ E.W) (hCW : CB + cap ≤ 2 ^ E.W)
    (hDpos : 0 < D.natDegree) (hD : D.natDegree < L) (hC : C.natDegree < L)
    (hRm : PolynomialStored b m RB cap R0) (hUm : PolynomialStored b m UB cap U0)
    (hDm : PolynomialStored b m DB cap D) (hCm : PolynomialStored b m CB cap C)
    (hc : RowCache b D RB UB DB CB L m n0) (hBound : R0.natDegree < D.natDegree + n0) :
    Sem P E base (base + 234) (boundaryState base m)
      (fun k s' => k ≤ (48 * L + 187) * n0 + 4 ∧ ∃ m' : ℕ → ℕ,
        s' = boundaryState (base + 234) m' ∧ RowCache b D RB UB DB CB L m' 0 ∧
        MemoryFrame (divisionWritable RB UB cap) m m' ∧
        PolynomialStored b m' RB cap (R0 % D) ∧
        PolynomialStored b m' UB cap (U0 - (R0 / D) * C) ∧
        PolynomialStored b m' DB cap D ∧ PolynomialStored b m' CB cap C) := by
  obtain ⟨hReadAt, hLoopAt⟩ := At.seqStmt hAt
  have hnWord : n0 < 2 ^ E.W := by have h := hl.Rlow; omega
  have hAddr : (71 : ℕ) < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (71 : ℕ) < 2 ^ 8) hp
  have hReadRun := rankRead_spec E base m n0 hAddr hnWord hc.count
  have hRead : Sem P E base (base + 3) (boundaryState base m)
      (fun k s' => k ≤ 3 ∧ s' = rankState (base + 3) m n0) := by
    refine Sem.mono (Sem.block P E base (metaReadCode r9 71) _ hReadAt
      (by simp [metaReadCode]) rfl) ?_
    intro k s' hQ
    obtain ⟨hk, hs⟩ := hQ
    refine ⟨by change k = 3 at hk; omega, ?_⟩
    rw [hs, hReadRun]
  have hLoop := longDivLoop_spec b ι t N P E (base + 3) RB UB DB CB L cap n0 R0 U0 D C m
    hLoopAt hw hW hdet hl hcap hRW hUW hDW hCW hDpos hD hC hRm hUm hDm hCm hc hBound
  have hFull := Sem.seq_bound hRead (fun z _ hz => by subst z; exact hLoop)
  obtain ⟨hpc, k, z, hrun, hreturn, hcost, hregs, hcache, hframe, hRout, hUout, hDout, hCout⟩ := hFull
  refine ⟨hpc, k, z, hrun, hreturn, ?_, z.mem, ?_, hcache, hframe, hRout, hUout, hDout, hCout⟩
  · omega
  · apply ramState_eq_of
    · exact hreturn
    · rfl
    · intro d
      simpa only [boundaryState] using congrFun hregs d

/-- A straight-line procedure with zero registers at both boundaries. -/
theorem Sem.boundary_block (P : Program) (E : RAMEnv) (base : ℕ)
    (code : List Instr) (m m' : ℕ → ℕ) (hAt : At P base code)
    (hno : NoBranch code)
    (hrun : runBlock code E (boundaryState base m) = boundaryState (base + code.length) m') :
    Sem P E base (base + code.length) (boundaryState base m)
      (fun k s' => k ≤ code.length ∧ s' = boundaryState (base + code.length) m') := by
  refine Sem.mono (Sem.block P E base code _ hAt hno rfl) ?_
  intro k s' hQ
  obtain ⟨hk, hs⟩ := hQ
  exact ⟨by omega, hs.trans hrun⟩

theorem scanArgs_spec {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (E : RAMEnv) (pc B L : ℕ)
    (p : F[X]) (m : ℕ → ℕ) (hmeta : (66 : ℕ) < 2 ^ E.W)
    (hB : B < 2 ^ E.W) (hL : L < 2 ^ E.W) (hm64 : m 64 = B) (hm66 : m 66 = L) :
    runBlock scanArgsCode E (boundaryState pc m) =
      scanState b (pc + 6) B L p m (fun _ => 0) 0 := by
  have h64 : (64 : ℕ) % 2 ^ E.W = 64 := Nat.mod_eq_of_lt (by omega)
  have h66 : (66 : ℕ) % 2 ^ E.W = 66 := Nat.mod_eq_of_lt hmeta
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt (by omega)
  apply ramState_eq_of
  ·     simp only [scanArgsCode, Fin.isValue, boundaryState, runBlock_cons, execInstr, Function.update_self,
      Nat.zero_mod, runBlock_nil, scanState, ite_self, Nat.add_right_cancel_iff, Nat.add_left_cancel_iff] <;> omega
  · rfl
  · intro d
    fin_cases d <;>                     simp only [scanArgsCode, Fin.isValue, boundaryState, runBlock_cons, execInstr, h64,
                      Function.update_self, hm64, Nat.mod_eq_of_lt hB, h66, hm66, Nat.mod_eq_of_lt hL, h1,
                      Nat.zero_mod, runBlock_nil, Fin.zero_eta, ne_eq, Fin.reduceEq, not_false_eq_true,
                      Function.update_of_ne, zero_ne_one, scanState, degreeScan, ite_self, ↓reduceIte,
                      Fin.mk_one, one_ne_zero, Fin.reduceFinMk]

theorem scanProcedure_spec {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (P : Program) (E : RAMEnv) (pc B L : ℕ)
    (p : F[X]) (m : ℕ → ℕ) (hAt : At P pc (Stmt.compile scanProcedure pc))
    (hmeta : (95 : ℕ) < 2 ^ E.W) (hwe : w ≤ E.W)
    (hBword : B < 2 ^ E.W) (hL : L < 2 ^ E.W) (hB : B + L ≤ 2 ^ E.W)
    (hp : PolynomialStored b m B L p) (hm64 : m 64 = B) (hm66 : m 66 = L) :
    Sem P E pc (pc + 42) (boundaryState pc m)
      (fun k s' => k ≤ 17 * L + 27 ∧
        s' = boundaryState (pc + 42) (Function.update m 95 (degreeScan p L))) := by
  obtain ⟨hArgsAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hScanAt, hReturnAt⟩ := At.seqStmt hRestAt
  have hInit : Sem P E pc (pc + 6) (boundaryState pc m)
      (fun k z => k ≤ 6 ∧ z = scanState b (pc + 6) B L p m (fun _ => 0) 0) := by
    refine Sem.mono (Sem.block P E pc scanArgsCode _ hArgsAt (by simp [scanArgsCode]) rfl) ?_
    intro k z hQ
    obtain ⟨hk, hz⟩ := hQ
    refine ⟨by change k = 6 at hk; omega, ?_⟩
    rw [hz, scanArgs_spec b E pc B L p m (by omega) hBword hL hm64 hm66]
  have hScan := scanArray_spec b P E (pc + 6) B L p m (fun _ => 0) hScanAt
    (by omega) hwe hL hB hp
  have hReturnRun : runBlock scanReturnCode E
      { scanState b (pc + 6) B L p m (fun _ => 0) L with pc := pc + 6 + 17 } =
      boundaryState (pc + 42) (Function.update m 95 (degreeScan p L)) := by
    rw [scanReturnCode, runBlock_append, zeroRegs_spec, metaStore_spec E _ r2 95 (by decide)]
    simp only [scanState, Nat.mod_eq_of_lt hmeta, boundaryState]
    rfl
  have hReturn : Sem P E (pc + 6 + 17) (pc + 42)
      { scanState b (pc + 6) B L p m (fun _ => 0) L with pc := pc + 6 + 17 }
      (fun k z => k ≤ 19 ∧ z = boundaryState (pc + 42) (Function.update m 95 (degreeScan p L))) := by
    refine Sem.mono (Sem.block P E _ scanReturnCode _ hReturnAt
      (by simp [scanReturnCode, metaStoreCode, zeroRegsCode]) rfl) ?_
    intro k z hQ
    obtain ⟨hk, hz⟩ := hQ
    exact ⟨by change k = 19 at hk; omega, hz.trans hReturnRun⟩
  have hFull := Sem.seq_bound hInit (fun z _ hz => by
    subst z
    exact Sem.seq_bound hScan (fun z _ hz => by subst z; exact hReturn))
  exact Sem.mono hFull (fun k z hQ => ⟨by omega, hQ.2⟩)

theorem copyArgs_spec (E : RAMEnv) (pc dst src L : ℕ) (m : ℕ → ℕ)
    (hmeta : (66 : ℕ) < 2 ^ E.W) (hdst : dst < 2 ^ E.W) (hsrc : src < 2 ^ E.W)
    (hL : L < 2 ^ E.W) (hm64 : m 64 = dst) (hm65 : m 65 = src) (hm66 : m 66 = L) :
    runBlock copyArgsCode E (boundaryState pc m) = copyState (pc + 8) dst src L m (fun _ => 0) 0 := by
  have hsmall : ∀ i ≤ 66, i % 2 ^ E.W = i := by
    intro i hi
    exact Nat.mod_eq_of_lt (by omega)
  apply ramState_eq_of
  ·     simp only [copyArgsCode, Fin.isValue, boundaryState, runBlock_cons, execInstr, Function.update_self,
      Nat.zero_mod, runBlock_nil, copyState, ite_self, Nat.add_right_cancel_iff, Nat.add_left_cancel_iff] <;> omega
  · rfl
  · intro d
    fin_cases d <;>                     simp only [copyArgsCode, Fin.isValue, boundaryState, runBlock_cons, execInstr,
                      Nat.reduceLeDiff, hsmall, Function.update_self, hm64, Nat.mod_eq_of_lt hdst, hm65,
                      Nat.mod_eq_of_lt hsrc, Std.le_refl, hm66, Nat.mod_eq_of_lt hL, Nat.one_le_ofNat,
                      zero_le, runBlock_nil, Fin.zero_eta, ne_eq, Fin.reduceEq, not_false_eq_true,
                      Function.update_of_ne, zero_ne_one, copyState, ite_self, ↓reduceIte, Fin.mk_one,
                      one_ne_zero, Fin.reduceFinMk]

theorem copyProcedure_spec (P : Program) (E : RAMEnv) (pc dst src L : ℕ)
    (m : ℕ → ℕ) (hAt : At P pc (Stmt.compile copyProcedure pc))
    (hmeta : (66 : ℕ) < 2 ^ E.W) (hdstWord : dst < 2 ^ E.W) (hsrcWord : src < 2 ^ E.W)
    (hL : L < 2 ^ E.W) (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src) (hword : ∀ i < L, m (src + i) < 2 ^ E.W)
    (hm64 : m 64 = dst) (hm65 : m 65 = src) (hm66 : m 66 = L) :
    Sem P E pc (pc + 36) (boundaryState pc m)
      (fun k s' => k ≤ 12 * L + 26 ∧
        s' = boundaryState (pc + 36) (writeArray dst m (fun i => m (src + i)) L)) := by
  obtain ⟨hArgsAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hCopyAt, hReturnAt⟩ := At.seqStmt hRestAt
  have hInit : Sem P E pc (pc + 8) (boundaryState pc m)
      (fun k z => k ≤ 8 ∧ z = copyState (pc + 8) dst src L m (fun _ => 0) 0) := by
    refine Sem.mono (Sem.block P E pc copyArgsCode _ hArgsAt (by simp [copyArgsCode]) rfl) ?_
    intro k z hQ
    obtain ⟨hk, hz⟩ := hQ
    exact ⟨by change k = 8 at hk; omega,
      hz.trans (copyArgs_spec E pc dst src L m hmeta hdstWord hsrcWord hL hm64 hm65 hm66)⟩
  have hCopy := copyArray_spec P E (pc + 8) dst src L m (fun _ => 0) hCopyAt
    (by omega) hL hdst hsrc hdisj hword
  have hReturn : Sem P E (pc + 8 + 12) (pc + 36)
      { copyState (pc + 8) dst src L m (fun _ => 0) L with pc := pc + 8 + 12 }
      (fun k z => k ≤ 16 ∧
        z = boundaryState (pc + 36) (writeArray dst m (fun i => m (src + i)) L)) := by
    refine Sem.mono (Sem.block P E _ zeroRegsCode _ hReturnAt (by simp [zeroRegsCode]) rfl) ?_
    intro k z hQ
    obtain ⟨hk, hz⟩ := hQ
    refine ⟨by change k = 16 at hk; omega, ?_⟩
    rw [hz, zeroRegs_spec]
    rfl
  have hFull := Sem.seq_bound hInit (fun z _ hz => by
    subst z
    exact Sem.seq_bound hCopy (fun z _ hz => by subst z; exact hReturn))
  exact Sem.mono hFull (fun k z hQ => ⟨by omega, hQ.2⟩)

theorem scanSetup_spec (E : RAMEnv) (s : RAMState) (slot B cap : ℕ)
    (hmeta : (81 : ℕ) < 2 ^ E.W) (hslot : slot < 2 ^ E.W)
    (hB : B < 2 ^ E.W) (hcap : cap < 2 ^ E.W) (hmB : s.mem slot = B) (hmcap : s.mem 81 = cap) :
    runBlock (scanSetupCode slot) E s = boundaryState (s.pc + 28)
      (Function.update (Function.update s.mem 64 B) 66 cap) := by
  have hsmall : ∀ i ≤ 81, i % 2 ^ E.W = i := by
    intro i hi
    exact Nat.mod_eq_of_lt (by omega)
  rw [scanSetupCode, runBlock_append, zeroRegs_spec]
  apply ramState_eq_of
  · have hp := runBlock_pc (scanSetupCode slot) E s (by
      simp [scanSetupCode, metaReadCode, metaStoreCode, zeroRegsCode])
    rw [scanSetupCode, runBlock_append, zeroRegs_spec] at hp
    change _ = s.pc + 28 at hp
    exact hp
  ·     simp only [boundaryState, Fin.isValue, List.append_assoc, runBlock_append, ne_eq, Fin.reduceEq,
      not_false_eq_true, metaRead_spec, Nat.mod_eq_of_lt hslot, hmB, Nat.mod_eq_of_lt hB, Std.le_refl,
      hsmall, hmcap, Nat.mod_eq_of_lt hcap, metaStore_spec, Function.update_idem, Nat.reduceLeDiff,
      Function.update_of_ne, Function.update_self]
  · intro _; rfl

/-- Cache a divisor degree and inverse leading coefficient using the scan.
No field-unit encoding assumption is made. -/
theorem cacheDivisor_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) (E : RAMEnv)
    (s : RAMState) (D : F[X]) (DB cap : ℕ) (hDBlow : 128 ≤ DB)
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (hDB : DB + D.natDegree < 2 ^ E.W) (hd : D.natDegree + 1 < 2 ^ E.W)
    (hcap : D.natDegree < cap) (hD : PolynomialStored b s.mem DB cap D)
    (hm95 : s.mem 95 = D.natDegree + 1) (hm74 : s.mem 74 = DB) (hm77 : s.mem 77 = w) :
    runBlock cacheDivisorCode E s = boundaryState (s.pc + 39)
      (Function.update (Function.update s.mem 69 D.natDegree) 70 (enc b D.leadingCoeff⁻¹)) := by
  have hpow : (2 : ℕ) ^ w ≤ 2 ^ E.W := by
    rw [hW]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hwidth : (95 : ℕ) < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (95 : ℕ) < 2 ^ 8) hp
  have hsmall : ∀ i ≤ 95, i % 2 ^ E.W = i := by
    intro i hi
    exact Nat.mod_eq_of_lt (by omega)
  have hDB0 : DB % 2 ^ E.W = DB := Nat.mod_eq_of_lt (by omega)
  have hd1 : (D.natDegree + 1) % 2 ^ E.W = D.natDegree + 1 := Nat.mod_eq_of_lt hd
  have hpred : (D.natDegree + 1 + 2 ^ E.W - 1) % 2 ^ E.W = D.natDegree := by
    rw [show D.natDegree + 1 + 2 ^ E.W - 1 = D.natDegree + 2 ^ E.W by omega]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (show D.natDegree < 2 ^ E.W by omega)]
  have haddr : (DB + D.natDegree) % 2 ^ E.W = DB + D.natDegree := Nat.mod_eq_of_lt hDB
  have hw0 : w % 2 ^ E.W = w :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.lt_two_pow_self (n := w)) hpow)
  have hEnc (z : F) : enc b z % 2 ^ E.W = enc b z :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le (enc_lt b z) hpow)
  have hd0 : D.natDegree % 2 ^ E.W = D.natDegree := Nat.mod_eq_of_lt (by omega)
  have hmlead : s.mem (DB + D.natDegree) = enc b D.leadingCoeff := hD D.natDegree hcap
  have hreadne : DB + D.natDegree ≠ 69 := by omega
  let sA := runBlock cacheDivisorReadCode E s
  have hA10 : sA.regs r10 = enc b D.leadingCoeff := by
    simp only [cacheDivisorReadCode, Fin.isValue, List.append_assoc, List.cons_append, List.nil_append,
      runBlock_append, ne_eq, Fin.reduceEq, not_false_eq_true, metaRead_spec, Std.le_refl, hsmall, hm95, hd1,
      runBlock_cons, execInstr, Nat.one_le_ofNat, Function.update_of_ne, Function.update_self,
      Nat.succ_add_sub_one, Nat.add_mod_right, hd0, metaStore_spec, Nat.reduceLeDiff, Nat.reduceEqDiff, hm74,
      hDB0, haddr, hreadne, hmlead, hEnc, hm77, hw0, sA]
  have hAm : sA.mem = Function.update s.mem 69 D.natDegree := by
    simp only [cacheDivisorReadCode, Fin.isValue, List.append_assoc, List.cons_append, List.nil_append,
      runBlock_append, ne_eq, Fin.reduceEq, not_false_eq_true, metaRead_spec, Std.le_refl, hsmall, hm95, hd1,
      runBlock_cons, execInstr, Nat.one_le_ofNat, Function.update_of_ne, Function.update_self,
      Nat.succ_add_sub_one, Nat.add_mod_right, hd0, metaStore_spec, Nat.reduceLeDiff, Nat.reduceEqDiff,
      Nat.mod_add_mod, sA]
  have hInv := fieldInvCode_spec b ι t N E sA D.leadingCoeff hw hW hdet hA10
  have hfinish : runBlock cacheDivisorCode E s =
      runBlock zeroRegsCode E (runBlock (metaStoreCode r10 70) E (runBlock fieldInvCode E sA)) := by
    simp only [cacheDivisorCode, runBlock_append] <;> rfl
  have hmem : (runBlock (metaStoreCode r10 70) E (runBlock fieldInvCode E sA)).mem =
      Function.update (Function.update s.mem 69 D.natDegree) 70 (enc b D.leadingCoeff⁻¹) := by
    rw [hInv, metaStore_spec E _ r10 70 (by decide)]
    simp only [Nat.mod_eq_of_lt (show (70 : ℕ) < 2 ^ E.W by omega), Function.update_self]
    exact congrArg (fun m => Function.update m 70 (enc b D.leadingCoeff⁻¹)) hAm
  rw [hfinish, zeroRegs_spec]
  apply ramState_eq_of
  · have hp := runBlock_pc cacheDivisorCode E s (by
      simp [cacheDivisorCode, cacheDivisorReadCode, metaReadCode, metaStoreCode,
        fieldInvCode, zeroRegsCode])
    rw [hfinish, zeroRegs_spec] at hp
    exact hp
  · exact hmem
  · intro _; rfl

theorem divisionCount_spec (E : RAMEnv) (s : RAMState) (a d : ℕ)
    (hmeta : (95 : ℕ) < 2 ^ E.W) (ha : a < 2 ^ E.W) (hd : d ≤ a)
    (hm95 : s.mem 95 = a) (hm69 : s.mem 69 = d) :
    runBlock divisionCountCode E s = boundaryState (s.pc + 26) (Function.update s.mem 71 (a - d)) := by
  have hsmall : ∀ i ≤ 95, i % 2 ^ E.W = i := by
    intro i hi
    exact Nat.mod_eq_of_lt (by omega)
  have hsub : (a + 2 ^ E.W - d) % 2 ^ E.W = a - d := by
    rw [show a + 2 ^ E.W - d = (a - d) + 2 ^ E.W by omega]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (show a - d < 2 ^ E.W by omega)]
  rw [divisionCountCode, runBlock_append, zeroRegs_spec]
  apply ramState_eq_of
  · have hp := runBlock_pc divisionCountCode E s (by
      simp [divisionCountCode, metaReadCode, metaStoreCode, zeroRegsCode])
    rw [divisionCountCode, runBlock_append, zeroRegs_spec] at hp
    change _ = s.pc + 26 at hp
    exact hp
  · simp [runBlock_append, metaRead_spec, metaStore_spec, runBlock_cons, runBlock_nil,
      execInstr, hsmall, hm95, hm69, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt (show d < 2 ^ E.W by omega), hsub, boundaryState]
  · intro _; rfl

theorem swapRows_spec (E : RAMEnv) (s : RAMState) (RB UB DB CB : ℕ)
    (hmeta : (75 : ℕ) < 2 ^ E.W)
    (hR : RB < 2 ^ E.W) (hU : UB < 2 ^ E.W) (hD : DB < 2 ^ E.W) (hC : CB < 2 ^ E.W)
    (hm72 : s.mem 72 = RB) (hm73 : s.mem 73 = UB) (hm74 : s.mem 74 = DB) (hm75 : s.mem 75 = CB) :
    runBlock swapRowsCode E s = boundaryState (s.pc + 40) (swapRowMemory s.mem RB UB DB CB) := by
  have hsmall : ∀ i ≤ 75, i % 2 ^ E.W = i := by
    intro i hi
    exact Nat.mod_eq_of_lt (by omega)
  rw [swapRowsCode, runBlock_append, zeroRegs_spec]
  apply ramState_eq_of
  · have hp := runBlock_pc swapRowsCode E s (by
      simp [swapRowsCode, metaReadCode, metaStoreCode, zeroRegsCode])
    rw [swapRowsCode, runBlock_append, zeroRegs_spec] at hp
    change _ = s.pc + 40 at hp
    exact hp
  · simp [runBlock_append, metaRead_spec, metaStore_spec, swapRowMemory, hsmall,
      hm72, hm73, hm74, hm75, Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt hU,
      Nat.mod_eq_of_lt hD, Nat.mod_eq_of_lt hC, boundaryState]
  · intro _; rfl

theorem MemoryFrame.mono {A B : ℕ → Prop} {m m' : ℕ → ℕ}
    (hf : MemoryFrame A m m') (hab : ∀ addr, A addr → B addr) : MemoryFrame B m m' := by
  intro addr hB
  exact hf addr (fun hA => hB (hab addr hA))

theorem MemoryFrame.update (m : ℕ → ℕ) (slot value : ℕ) :
    MemoryFrame (fun addr => addr = slot) m (Function.update m slot value) := by
  intro addr hne
  exact Function.update_of_ne hne value m

theorem MemoryFrame.meta_update (m : ℕ → ℕ) (slot value : ℕ) (hslot : slot < 128) :
    MemoryFrame (fun addr => addr < 128) m (Function.update m slot value) :=
  (MemoryFrame.update m slot value).mono (by intro addr ha; subst addr; exact hslot)

theorem PolynomialStored.of_metaFrame {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {m m' : ℕ → ℕ} {B cap : ℕ} {p : F[X]}
    (hp : PolynomialStored b m B cap p) (hB : 128 ≤ B)
    (hf : MemoryFrame (fun addr => addr < 128) m m') : PolynomialStored b m' B cap p := by
  intro i hi
  rw [hf (B + i) (by omega)]
  exact hp i hi

/-- Arrays and persistent metadata survive a scratch-metadata preparation. -/
theorem PadeRows.of_scratchFrame {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {E : RAMEnv}
    {RB UB DB CB L cap : ℕ} {m m' : ℕ → ℕ} {s : PadeState F}
    (h : PadeRows b E RB UB DB CB L cap m s)
    (hf : MemoryFrame (fun addr => addr < 128) m m')
    (hp : ∀ slot, slot = 72 ∨ slot = 73 ∨ slot = 74 ∨ slot = 75 ∨ slot = 76 ∨ slot = 77 ∨ slot = 81 →
      m' slot = m slot) : PadeRows b E RB UB DB CB L cap m' s := by
  refine ⟨h.layout, h.Rword, h.Uword, h.Dword, h.Cword,
    h.prevR.of_metaFrame h.layout.Rlow hf, h.prevC.of_metaFrame h.layout.Ulow hf,
    h.rem.of_metaFrame h.layout.Dlow hf, h.curC.of_metaFrame h.layout.Clow hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hp 72 (by simp)).trans h.ptr72
  · exact (hp 73 (by simp)).trans h.ptr73
  · exact (hp 74 (by simp)).trans h.ptr74
  · exact (hp 75 (by simp)).trans h.ptr75
  · exact (hp 76 (by simp)).trans h.length
  · exact (hp 77 (by simp)).trans h.dimension
  · exact (hp 81 (by simp)).trans h.capacity

theorem MemoryFrame.update_allowed (A : ℕ → Prop) (m : ℕ → ℕ) (slot value : ℕ) (hslot : A slot) :
    MemoryFrame A m (Function.update m slot value) :=
  (MemoryFrame.update m slot value).mono (by intro addr ha; subst addr; exact hslot)

theorem PadeRows.of_scratch {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {E : RAMEnv}
    {RB UB DB CB L cap : ℕ} {m m' : ℕ → ℕ} {s : PadeState F}
    (h : PadeRows b E RB UB DB CB L cap m s)
    (hf : MemoryFrame padeScratch m m') : PadeRows b E RB UB DB CB L cap m' s := by
  apply h.of_scratchFrame (hf.mono (by intro addr ha; dsimp [padeScratch] at ha; omega))
  intro slot hs
  exact hf slot (by dsimp [padeScratch]; omega)

theorem divisionWritable_le_pade (RB UB DB CB cap addr : ℕ)
    (h : divisionWritable RB UB cap addr) : padeWritable RB UB DB CB cap addr := by
  rcases h with h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem padeWritable_swap (RB UB DB CB cap addr : ℕ) :
    padeWritable DB CB RB UB cap addr ↔ padeWritable RB UB DB CB cap addr := by
  simp only [padeWritable]
  constructor
  · rintro (h | h | h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rintro (h | h | h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- Refinement of one full extended-Euclidean step, including physical row
exchange and a frame suitable for the enclosing counted loop. -/
theorem padeQuotient_spec {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (pc RB UB DB CB L cap : ℕ)
    (e : ℕ → F) (s : PadeState F) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile padeQuotientProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (ht : 1 ≤ t) (hL : L = 2 * t + 1) (hcap : cap = 2 * L)
    (hrows : PadeRows b E RB UB DB CB L cap m s) (hinv : PadeInv e t s)
    (hgo : t ≤ s.rem.natDegree) (hscan : m 95 = s.rem.natDegree + 1) :
    Sem P E pc (pc + 409) (boundaryState pc m)
      (fun k z => k ≤ 17 * cap + (48 * L + 187) * L + 164 ∧
        ∃ m' : ℕ → ℕ, z = boundaryState (pc + 409) m' ∧
          PadeRows b E DB CB RB UB L cap m' (padeNext s) ∧
          MemoryFrame (padeWritable RB UB DB CB cap) m m') := by
  let n := s.prevR.natDegree + 1 - s.rem.natDegree
  let m1 := Function.update (Function.update m 69 s.rem.natDegree) 70 (enc b s.rem.leadingCoeff⁻¹)
  let m2 := Function.update (Function.update m1 64 RB) 66 cap
  let m3 := Function.update m2 95 (degreeScan s.prevR cap)
  let m4 := Function.update m3 71 n
  have hdegR : s.prevR.natDegree < L := by have h := hinv.balance; omega
  have hdegD : s.rem.natDegree < L := by have h := hinv.rem_small; omega
  have hdegC : s.curC.natDegree < L := by have h := hinv.balance; omega
  have hdegU : s.prevC.natDegree < L := by have h := hinv.prev_small; omega
  have hnL : n ≤ L := by dsimp [n]; omega
  have hncap : n + L ≤ cap := by omega
  have hRbound : s.prevR.natDegree < s.rem.natDegree + n := by
    dsimp [n]
    have h := hinv.rem_small
    omega
  have hwidth : (95 : ℕ) < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (95 : ℕ) < 2 ^ 8) hp
  have hcapWord : cap < 2 ^ E.W := by have h := hrows.layout.Rlow; have h' := hrows.Rword; omega
  have hBword : RB < 2 ^ E.W := by have h := hrows.Rword; omega
  have hmf1 : MemoryFrame padeScratch m m1 :=
    MemoryFrame.trans (MemoryFrame.update_allowed padeScratch m 69 _ (by simp [padeScratch]))
      (MemoryFrame.update_allowed padeScratch _ 70 _ (by simp [padeScratch]))
  have hmf2 : MemoryFrame padeScratch m1 m2 :=
    MemoryFrame.trans (MemoryFrame.update_allowed padeScratch m1 64 _ (by simp [padeScratch]))
      (MemoryFrame.update_allowed padeScratch _ 66 _ (by simp [padeScratch]))
  have hmf3 : MemoryFrame padeScratch m2 m3 :=
    MemoryFrame.update_allowed padeScratch m2 95 _ (by simp [padeScratch])
  have hmf4 : MemoryFrame padeScratch m3 m4 :=
    MemoryFrame.update_allowed padeScratch m3 71 _ (by simp [padeScratch])
  have hr1 := hrows.of_scratch hmf1
  have hr2 := hr1.of_scratch hmf2
  have hr3 := hr2.of_scratch hmf3
  have hr4 := hr3.of_scratch hmf4
  have hscanR : degreeScan s.prevR cap = s.prevR.natDegree + 1 :=
    degreeScan_eq s.prevR hinv.prev_ne cap (by omega)
  obtain ⟨hInvAt, hRest1⟩ := At.seqStmt hAt
  obtain ⟨hSetupAt, hRest2⟩ := At.seqStmt hRest1
  obtain ⟨hScanAt, hRest3⟩ := At.seqStmt hRest2
  obtain ⟨hCountAt, hRest4⟩ := At.seqStmt hRest3
  obtain ⟨hDivAt, hSwapAt⟩ := At.seqStmt hRest4
  have hInv : Sem P E pc (pc + 39) (boundaryState pc m)
      (fun k z => k ≤ 39 ∧ z = boundaryState (pc + 39) m1) := by
    exact Sem.boundary_block P E pc cacheDivisorCode m m1 hInvAt
      (by simp [cacheDivisorCode, cacheDivisorReadCode, metaReadCode, metaStoreCode, fieldInvCode, zeroRegsCode])
      (cacheDivisor_spec b ι t N E _ s.rem DB cap hrows.layout.Dlow hw hW hdet
        (by have h := hrows.Dword; omega) (by omega) (by omega) hrows.rem hscan hrows.ptr74 hrows.dimension)
  have hSetup : Sem P E (pc + 39) (pc + 67) (boundaryState (pc + 39) m1)
      (fun k z => k ≤ 28 ∧ z = boundaryState (pc + 67) m2) := by
    exact Sem.boundary_block P E _ (scanSetupCode 72) m1 m2 hSetupAt
      (by simp [scanSetupCode, metaReadCode, metaStoreCode, zeroRegsCode])
      (scanSetup_spec E _ 72 RB cap (by omega) (by omega) hBword hcapWord hr1.ptr72 hr1.capacity)
  have hwe : w ≤ E.W := by omega
  have hScan := scanProcedure_spec b P E (pc + 67) RB cap s.prevR m2 hScanAt hwidth hwe
    hBword hcapWord hrows.Rword hr2.prevR (by simp [m2]) (by simp [m2])
  have hCount : Sem P E (pc + 109) (pc + 135) (boundaryState (pc + 109) m3)
      (fun k z => k ≤ 26 ∧ z = boundaryState (pc + 135) m4) := by
    exact Sem.boundary_block P E _ divisionCountCode m3 m4 hCountAt
      (by simp [divisionCountCode, metaReadCode, metaStoreCode, zeroRegsCode])
      (divisionCount_spec E _ (s.prevR.natDegree + 1) s.rem.natDegree hwidth (by omega)
        (by have h := hinv.rem_small; omega) (by simp [boundaryState, m3, hscanR]) (by simp [boundaryState, m3, m2, m1]))
  have hc4 : RowCache b s.rem RB UB DB CB L m4 n :=
    ⟨by simp [m4, m3, m2, m1], by simp [m4, m3, m2, m1], by simp [m4],
      hr4.ptr72, hr4.ptr73, hr4.ptr74, hr4.ptr75, hr4.length, hr4.dimension⟩
  have hDiv := longDivProcedure_spec b ι t N P E (pc + 135) RB UB DB CB L cap n
    s.prevR s.prevC s.rem s.curC m4 hDivAt hw hW hdet hrows.layout hncap
    hrows.Rword hrows.Uword hrows.Dword hrows.Cword (by omega) hdegD hdegC
    hr4.prevR hr4.prevC hr4.rem hr4.curC hc4 hRbound
  obtain ⟨_, kd, zd, hrunD, hpcD, hcostD, m5, hzD, hc5, hf5, hRm5, hUm5, hDm5, hCm5⟩ := hDiv
  have hDivExact : Sem P E (pc + 135) (pc + 369) (boundaryState (pc + 135) m4)
      (fun k z => k ≤ (48 * L + 187) * L + 4 ∧ z = boundaryState (pc + 369) m5) := by
    refine ⟨rfl, kd, zd, hrunD, hpcD, ?_, hzD⟩
    exact le_trans hcostD (by
      have hmul := Nat.mul_le_mul_left (48 * L + 187) hnL
      first | omega | nlinarith)
  let m6 := swapRowMemory m5 RB UB DB CB
  have hSwap : Sem P E (pc + 369) (pc + 409) (boundaryState (pc + 369) m5)
      (fun k z => k ≤ 40 ∧ z = boundaryState (pc + 409) m6) := by
    exact Sem.boundary_block P E _ swapRowsCode m5 m6 hSwapAt
      (by simp [swapRowsCode, metaReadCode, metaStoreCode, zeroRegsCode])
      (swapRows_spec E _ RB UB DB CB (by omega)
        (by have h := hrows.Rword; omega) (by have h := hrows.Uword; omega)
        (by have h := hrows.Dword; omega) (by have h := hrows.Cword; omega)
        hc5.prevR hc5.prevC hc5.curR hc5.curC)
  have hm6f : MemoryFrame (fun addr => addr < 128) m5 m6 := by
    apply MemoryFrame.trans (MemoryFrame.trans (MemoryFrame.trans
      (MemoryFrame.meta_update m5 72 DB (by norm_num))
      (MemoryFrame.meta_update _ 73 CB (by norm_num)))
      (MemoryFrame.meta_update _ 74 RB (by norm_num)))
      (MemoryFrame.meta_update _ 75 UB (by norm_num))
  have hcap5 : m5 81 = cap := by
    rw [hf5 81 (by dsimp [divisionWritable]; have h := hrows.layout.Rlow; have h' := hrows.layout.Ulow; omega)]
    exact hr4.capacity
  have hr6 : PadeRows b E DB CB RB UB L cap m6 (padeNext s) := by
    refine ⟨hrows.layout.swap, hrows.Dword, hrows.Cword, hrows.Rword, hrows.Uword,
      hDm5.of_metaFrame hrows.layout.Dlow hm6f, hCm5.of_metaFrame hrows.layout.Clow hm6f,
      hRm5.of_metaFrame hrows.layout.Rlow hm6f, hUm5.of_metaFrame hrows.layout.Ulow hm6f,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [m6, swapRowMemory]
    · simp [m6, swapRowMemory]
    · simp [m6, swapRowMemory]
    · simp [m6, swapRowMemory]
    · simpa [m6, swapRowMemory] using hc5.length
    · simpa [m6, swapRowMemory] using hc5.dim
    · simpa [m6, swapRowMemory] using hcap5
  have hScratchIncl : ∀ addr, padeScratch addr → padeWritable RB UB DB CB cap addr := by
    intro addr ha
    dsimp [padeScratch] at ha
    dsimp [padeWritable]
    omega
  have hf04 : MemoryFrame (padeWritable RB UB DB CB cap) m m4 :=
    (MemoryFrame.trans (MemoryFrame.trans (MemoryFrame.trans hmf1 hmf2) hmf3) hmf4).mono hScratchIncl
  have hf45 := hf5.mono (divisionWritable_le_pade RB UB DB CB cap)
  have hf56 : MemoryFrame (padeWritable RB UB DB CB cap) m5 m6 := by
    apply MemoryFrame.trans (MemoryFrame.trans (MemoryFrame.trans
      (MemoryFrame.update_allowed _ m5 72 DB (by simp [padeWritable]))
      (MemoryFrame.update_allowed _ _ 73 CB (by simp [padeWritable])))
      (MemoryFrame.update_allowed _ _ 74 RB (by simp [padeWritable])))
      (MemoryFrame.update_allowed _ _ 75 UB (by simp [padeWritable]))
  have hFull := Sem.seq_bound hInv (fun z _ hz => by
    subst z
    exact Sem.seq_bound hSetup (fun z _ hz => by
      subst z
      exact Sem.seq_bound hScan (fun z _ hz => by
        subst z
        exact Sem.seq_bound hCount (fun z _ hz => by
          subst z
          exact Sem.seq_bound hDivExact (fun z _ hz => by subst z; exact hSwap)))))
  refine Sem.mono hFull ?_
  intro k z hQ
  exact ⟨by omega, m6, hQ.2, hr6, MemoryFrame.trans (MemoryFrame.trans hf04 hf45) hf56⟩

theorem padeRun_succ_tick {F : Type} [Field F] (t n : ℕ) (s : PadeState F) :
    padeRun t n (padeTick t s) = padeRun t (n + 1) s := by
  by_cases h : s.rem.natDegree < t
  · cases n <;> simp [padeTick, padeRun, h]
  · simp [padeTick, padeRun, h]

theorem padeInv_tick {F : Type} [Field F] [Algebra (ZMod 2) F]
    {e : ℕ → F} {t : ℕ} {s : PadeState F} (ht : 1 ≤ t) (h : PadeInv e t s) :
    PadeInv e t (padeTick t s) := by
  by_cases hs : s.rem.natDegree < t
  · simpa only [padeTick, if_pos hs] using h
  · simpa only [padeTick, if_neg hs] using padeInv_next ht h (by omega)

theorem padeTestLoad_spec (E : RAMEnv) (pc : ℕ) (m : ℕ → ℕ) (t d : ℕ)
    (hmeta : (95 : ℕ) < 2 ^ E.W) (ht : t < 2 ^ E.W) (hd : d < 2 ^ E.W)
    (hm80 : m 80 = t) (hm95 : m 95 = d) :
    runBlock padeTestLoadCode E (boundaryState pc m) = padeTestState (pc + 6) m t d := by
  rw [padeTestLoadCode, runBlock_append, metaRead_spec E _ r0 80 (by decide),
    metaRead_spec E _ r1 95 (by decide)]
  have h80 : (80 : ℕ) % 2 ^ E.W = 80 := Nat.mod_eq_of_lt (by omega)
  have h95 : (95 : ℕ) % 2 ^ E.W = 95 := Nat.mod_eq_of_lt hmeta
  apply ramState_eq_of
  · rfl
  · rfl
  · intro r
    fin_cases r <;> simp [boundaryState, padeTestState, h80, h95, hm80, hm95,
      Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hd]

/-- The scan test is exact even when the current remainder is zero. -/
theorem padeScan_go {F : Type} [Field F] [DecidableEq F] (t cap : ℕ) (D : F[X])
    (ht : 1 ≤ t) (hcap : D.natDegree < cap) :
    t < degreeScan D cap ↔ t ≤ D.natDegree := by
  by_cases hz : D = 0
  · simp [hz]; omega
  · rw [degreeScan_eq D hz cap hcap]
    omega

/-- Select either a real quotient step or an idle step, returning the exact
abstract padded transition and preserving all non-workspace memory. -/
theorem padeSelect_spec {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (pc RB UB DB CB L cap : ℕ)
    (e : ℕ → F) (s : PadeState F) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile padeSelectStmt pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (ht : 1 ≤ t) (hL : L = 2 * t + 1) (hcap : cap = 2 * L)
    (hrows : PadeRows b E RB UB DB CB L cap m s) (hinv : PadeInv e t s)
    (hm80 : m 80 = t) (hm95 : m 95 = degreeScan s.rem cap) :
    Sem P E pc (pc + 451) (boundaryState pc m)
      (fun k z => k ≤ 17 * cap + (48 * L + 187) * L + 189 ∧
        ∃ m', z = boundaryState (pc + 451) m' ∧
          PadeAdvance b E RB UB DB CB L cap m m' (padeTick t s)) := by
  have hwidth : (95 : ℕ) < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (95 : ℕ) < 2 ^ 8) hp
  have hcapWord : cap < 2 ^ E.W := by have h := hrows.layout.Rlow; have h' := hrows.Rword; omega
  have hdegR : s.prevR.natDegree < L := by have h := hinv.balance; omega
  have hdegD : s.rem.natDegree < cap := by have h := hinv.rem_small; omega
  have htWord : t < 2 ^ E.W := by omega
  have hdWord : degreeScan s.rem cap < 2 ^ E.W := lt_of_le_of_lt (degreeScan_le _ _) hcapWord
  obtain ⟨hLoadAt, hSelectAt⟩ := At.seqStmt hAt
  obtain ⟨_, _, hTrueAt, _, hFalseAt, _⟩ := at_ite hSelectAt
  obtain ⟨hZeroAt, hQuotAt⟩ := At.seqStmt hTrueAt
  have hLoad : Sem P E pc (pc + 6) (boundaryState pc m)
      (fun k z => k ≤ 6 ∧ z = padeTestState (pc + 6) m t (degreeScan s.rem cap)) := by
    refine Sem.mono (Sem.block P E pc padeTestLoadCode _ hLoadAt
      (by simp [padeTestLoadCode, metaReadCode]) rfl) ?_
    intro k z hQ
    obtain ⟨hk, hz⟩ := hQ
    exact ⟨by change k = 6 at hk; omega,
      hz.trans (padeTestLoad_spec E pc m t (degreeScan s.rem cap) hwidth htWord hdWord hm80 hm95)⟩
  let z0 := padeTestState (pc + 6) m t (degreeScan s.rem cap)
  let c : Cond := .lt r15 r0 r1
  have htest : c.eval z0 ↔ t ≤ s.rem.natDegree := by
    change (t < degreeScan s.rem cap) ↔ _
    exact padeScan_go t cap s.rem ht hdegD
  have hIf : Sem P E (pc + 6) (pc + 451) z0
      (fun k z => k ≤ 17 * cap + (48 * L + 187) * L + 183 ∧
        ∃ m', z = boundaryState (pc + 451) m' ∧
          PadeAdvance b E RB UB DB CB L cap m m' (padeTick t s)) := by
    apply Sem.ite P E (pc + 6) c (.seq (.code zeroRegsCode) padeQuotientProcedure) (.code zeroRegsCode)
      z0 _ hSelectAt (by omega) rfl
    · intro hgo
      have hg : t ≤ s.rem.natDegree := htest.mp hgo
      have hne : s.rem ≠ 0 := by intro hz; simp [hz] at hg; omega
      have hscan : m 95 = s.rem.natDegree + 1 := by
        rw [hm95, degreeScan_eq s.rem hne cap hdegD]
      have hZero : Sem P E (pc + 8) (pc + 24)
          { runBlock c.code E z0 with pc := pc + 8 }
          (fun k z => k ≤ 16 ∧ z = boundaryState (pc + 24) m) := by
        refine Sem.mono (Sem.block P E _ zeroRegsCode _ hZeroAt (by simp [zeroRegsCode]) rfl) ?_
        intro k z hQ
        obtain ⟨hk, hz⟩ := hQ
        refine ⟨by change k = 16 at hk; omega, ?_⟩
        rw [hz, zeroRegs_spec]
        rfl
      have hQuot := padeQuotient_spec b ι t N P E (pc + 24) RB UB DB CB L cap e s m hQuotAt
        hw hW hdet ht hL hcap hrows hinv hg hscan
      have hTrue := Sem.seq_bound hZero (fun z _ hz => by subst z; exact hQuot)
      refine Sem.mono hTrue ?_
      intro k z hQ
      obtain ⟨hk, m', hz, hr, hf⟩ := hQ
      refine ⟨by change 1 + 1 + k + 1 ≤ _; omega, m', ?_, DB, CB, RB, UB, ?_, hf, ?_⟩
      · rw [hz]; rfl
      · simpa only [padeTick, if_neg (by omega : ¬ s.rem.natDegree < t)] using hr
      · exact padeWritable_swap RB UB DB CB cap
    · intro hstop
      have hs : s.rem.natDegree < t := by have h := (not_congr htest).mp hstop; omega
      have hZero : Sem P E (pc + 434) (pc + 450)
          { runBlock c.code E z0 with pc := pc + 434 }
          (fun k z => k ≤ 16 ∧ z = boundaryState (pc + 450) m) := by
        refine Sem.mono (Sem.block P E _ zeroRegsCode _ hFalseAt (by simp [zeroRegsCode]) rfl) ?_
        intro k z hQ
        obtain ⟨hk, hz⟩ := hQ
        refine ⟨by change k = 16 at hk; omega, ?_⟩
        rw [hz, zeroRegs_spec]
        rfl
      refine Sem.mono hZero ?_
      intro k z hQ
      obtain ⟨hk, hz⟩ := hQ
      refine ⟨by change 1 + 1 + k + 1 ≤ _; omega, m, ?_, RB, UB, DB, CB, ?_, ?_, ?_⟩
      · rw [hz]; rfl
      · simpa only [padeTick, if_pos hs] using hrows
      · intro addr _; rfl
      · intro addr; rfl
  have hFull := Sem.seq_bound hLoad (fun z _ hz => by subst z; exact hIf)
  exact Sem.mono hFull (fun k z hQ => ⟨by omega, hQ.2⟩)

theorem padeStep_spec {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (pc RB UB DB CB L cap : ℕ)
    (e : ℕ → F) (s : PadeState F) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile padeStepProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (ht : 1 ≤ t) (hL : L = 2 * t + 1) (hcap : cap = 2 * L)
    (hrows : PadeRows b E RB UB DB CB L cap m s) (hinv : PadeInv e t s) (hm80 : m 80 = t) :
    Sem P E pc (pc + 521) (boundaryState pc m)
      (fun k z => k ≤ 34 * cap + (48 * L + 187) * L + 244 ∧
        ∃ m', z = boundaryState (pc + 521) m' ∧
          PadeAdvance b E RB UB DB CB L cap m m' (padeTick t s)) := by
  let m1 := Function.update (Function.update m 64 DB) 66 cap
  let m2 := Function.update m1 95 (degreeScan s.rem cap)
  have hf1 : MemoryFrame padeScratch m m1 :=
    MemoryFrame.trans (MemoryFrame.update_allowed padeScratch m 64 _ (by simp [padeScratch]))
      (MemoryFrame.update_allowed padeScratch _ 66 _ (by simp [padeScratch]))
  have hf2 : MemoryFrame padeScratch m1 m2 :=
    MemoryFrame.update_allowed padeScratch m1 95 _ (by simp [padeScratch])
  have hr1 := hrows.of_scratch hf1
  have hr2 := hr1.of_scratch hf2
  have hwidth : (95 : ℕ) < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (95 : ℕ) < 2 ^ 8) hp
  have hcapWord : cap < 2 ^ E.W := by have h := hrows.layout.Rlow; have h' := hrows.Rword; omega
  have hDBword : DB < 2 ^ E.W := by have h := hrows.Dword; omega
  obtain ⟨hSetupAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hScanAt, hSelectAt⟩ := At.seqStmt hRestAt
  have hSetup : Sem P E pc (pc + 28) (boundaryState pc m)
      (fun k z => k ≤ 28 ∧ z = boundaryState (pc + 28) m1) := by
    exact Sem.boundary_block P E _ (scanSetupCode 74) m m1 hSetupAt
      (by simp [scanSetupCode, metaReadCode, metaStoreCode, zeroRegsCode])
      (scanSetup_spec E _ 74 DB cap (by omega) (by omega) hDBword hcapWord hrows.ptr74 hrows.capacity)
  have hScan := scanProcedure_spec b P E (pc + 28) DB cap s.rem m1 hScanAt hwidth (by omega)
    hDBword hcapWord hrows.Dword hr1.rem (by simp [m1]) (by simp [m1])
  have hSelect := padeSelect_spec b ι t N P E (pc + 70) RB UB DB CB L cap e s m2 hSelectAt
    hw hW hdet ht hL hcap hr2 hinv (by simpa [m2, m1] using hm80) (by simp [m2])
  have hFull := Sem.seq_bound hSetup (fun z _ hz => by
    subst z
    exact Sem.seq_bound hScan (fun z _ hz => by subst z; exact hSelect))
  refine Sem.mono hFull ?_
  intro k z hQ
  obtain ⟨hk, m', hz, RB', UB', DB', CB', hr', hf', hfoot⟩ := hQ
  refine ⟨by omega, m', hz, RB', UB', DB', CB', hr', ?_, hfoot⟩
  apply MemoryFrame.trans ((MemoryFrame.trans hf1 hf2).mono ?_) hf'
  intro addr ha
  dsimp [padeScratch] at ha
  dsimp [padeWritable]
  omega

theorem countdown_spec (E : RAMEnv) (s : RAMState) (slot n : ℕ)
    (hslot : slot < 2 ^ E.W) (hn : n + 1 < 2 ^ E.W) (hm : s.mem slot = n + 1) :
    runBlock (countdownCode slot) E s = rankState (s.pc + 27) (Function.update s.mem slot n) n := by
  have hs : slot % 2 ^ E.W = slot := Nat.mod_eq_of_lt hslot
  have hn0 : (n + 1) % 2 ^ E.W = n + 1 := Nat.mod_eq_of_lt hn
  have hn1 : n % 2 ^ E.W = n := Nat.mod_eq_of_lt (by omega)
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt (by omega)
  have hpred : (n + 1 + 2 ^ E.W - 1) % 2 ^ E.W = n := by
    rw [show n + 1 + 2 ^ E.W - 1 = n + 2 ^ E.W by omega]
    simp [Nat.add_mod, hn1]
  apply ramState_eq_of
  · exact runBlock_pc (countdownCode slot) E s (by
      simp [countdownCode, metaReadCode, metaStoreCode, zeroRegsCode])
  ·     simp only [countdownCode, Fin.isValue, List.append_assoc, List.cons_append, List.nil_append,
      runBlock_append, ne_eq, Fin.reduceEq, not_false_eq_true, metaRead_spec, hs, hm, hn0, runBlock_cons,
      execInstr, h1, Function.update_of_ne, Function.update_self, Nat.succ_add_sub_one, Nat.add_mod_right,
      hn1, metaStore_spec, zeroRegs_spec, boundaryState, rankState]
  · intro d
    fin_cases d <;>                     simp only [countdownCode, Fin.isValue, List.append_assoc, List.cons_append,
                      List.nil_append, runBlock_append, ne_eq, Fin.reduceEq, not_false_eq_true,
                      metaRead_spec, hs, hm, hn0, runBlock_cons, execInstr, h1, Function.update_of_ne,
                      Function.update_self, Nat.succ_add_sub_one, Nat.add_mod_right, hn1, metaStore_spec,
                      zeroRegs_spec, boundaryState, Fin.zero_eta, rankState, Fin.mk_one, Fin.reduceFinMk]

theorem PadeRows.counter_update {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {E : RAMEnv} {RB UB DB CB L cap : ℕ}
    {m : ℕ → ℕ} {s : PadeState F} (h : PadeRows b E RB UB DB CB L cap m s) (n : ℕ) :
    PadeRows b E RB UB DB CB L cap (Function.update m 94 n) s := by
  apply h.of_scratchFrame (MemoryFrame.meta_update m 94 n (by norm_num))
  intro slot hs
  rw [Function.update_of_ne (by omega : slot ≠ 94)]

theorem padeLoopBody_spec {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (pc RB UB DB CB L cap n : ℕ)
    (e : ℕ → F) (s : PadeState F) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile padeLoopBody pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (ht : 1 ≤ t) (hL : L = 2 * t + 1) (hcap : cap = 2 * L)
    (hrows : PadeRows b E RB UB DB CB L cap m s) (hinv : PadeInv e t s)
    (hn : n + 1 < 2 ^ E.W) (hm80 : m 80 = t) (hm94 : m 94 = n + 1) :
    Sem P E pc (pc + 564) (rankState pc m (n + 1))
      (fun k z => k ≤ 34 * cap + (48 * L + 187) * L + 287 ∧
        ∃ m' RB' UB' DB' CB', z = rankState (pc + 564) m' n ∧ m' 94 = n ∧
          PadeRows b E RB' UB' DB' CB' L cap m' (padeTick t s) ∧
          MemoryFrame (padeLoopWritable RB UB DB CB cap) m m' ∧
          ∀ addr, padeWritable RB' UB' DB' CB' cap addr ↔ padeWritable RB UB DB CB cap addr) := by
  obtain ⟨hZeroAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hStepAt, hTailAt⟩ := At.seqStmt hRestAt
  have hwidth : (94 : ℕ) < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (94 : ℕ) < 2 ^ 8) hp
  have hZero : Sem P E pc (pc + 16) (rankState pc m (n + 1))
      (fun k z => k ≤ 16 ∧ z = boundaryState (pc + 16) m) := by
    refine Sem.mono (Sem.block P E _ zeroRegsCode _ hZeroAt (by simp [zeroRegsCode]) rfl) ?_
    intro k z hQ
    obtain ⟨hk, hz⟩ := hQ
    refine ⟨by change k = 16 at hk; omega, ?_⟩
    rw [hz, zeroRegs_spec]
    rfl
  have hStep := padeStep_spec b ι t N P E (pc + 16) RB UB DB CB L cap e s m hStepAt
    hw hW hdet ht hL hcap hrows hinv hm80
  have hRest : Sem P E (pc + 16) (pc + 564) (boundaryState (pc + 16) m)
      (fun k z => k ≤ (34 * cap + (48 * L + 187) * L + 244) + 27 ∧
        ∃ m' RB' UB' DB' CB', z = rankState (pc + 564) m' n ∧ m' 94 = n ∧
          PadeRows b E RB' UB' DB' CB' L cap m' (padeTick t s) ∧
          MemoryFrame (padeLoopWritable RB UB DB CB cap) m m' ∧
          ∀ addr, padeWritable RB' UB' DB' CB' cap addr ↔ padeWritable RB UB DB CB cap addr) := by
    refine Sem.seq_bound hStep ?_
    intro z hzpc hQ
    obtain ⟨m1, hz, RB', UB', DB', CB', hr, hf, hfoot⟩ := hQ
    subst z
    have h94 : m1 94 = n + 1 := by
      rw [hf 94 (by dsimp [padeWritable]; have h := hrows.layout.Rlow; have h' := hrows.layout.Ulow
                    have h'' := hrows.layout.Dlow; have h''' := hrows.layout.Clow; omega)]
      exact hm94
    have hTailRun := countdown_spec E (boundaryState (pc + 537) m1) 94 n hwidth hn h94
    refine Sem.mono (Sem.block P E (pc + 537) (countdownCode 94) _ hTailAt
      (by simp [countdownCode, metaReadCode, metaStoreCode, zeroRegsCode]) rfl) ?_
    intro k z hQ
    obtain ⟨hk, hz⟩ := hQ
    refine ⟨by change k = 27 at hk; omega,
      Function.update m1 94 n, RB', UB', DB', CB', ?_, by simp, hr.counter_update n, ?_, hfoot⟩
    · rw [hz, hTailRun]
      rfl
    · exact MemoryFrame.trans (hf.mono (by intro addr ha; exact Or.inr ha))
        (MemoryFrame.update_allowed _ m1 94 n (Or.inl rfl))
  have hFull := Sem.seq_bound hZero (fun z _ hz => by subst z; exact hRest)
  exact Sem.mono hFull (fun k z hQ => ⟨by omega, hQ.2⟩)

theorem rankReadSlot_spec (E : RAMEnv) (pc : ℕ) (m : ℕ → ℕ) (slot n : ℕ)
    (haddr : slot < 2 ^ E.W) (hn : n < 2 ^ E.W) (hm : m slot = n) :
    runBlock (metaReadCode r9 slot) E (boundaryState pc m) = rankState (pc + 3) m n := by
  rw [metaRead_spec E _ _ _ (by decide)]
  apply ramState_eq_of
  · rfl
  · rfl
  · intro d
    fin_cases d <;> simp [boundaryState, rankState, hm, Nat.mod_eq_of_lt haddr, Nat.mod_eq_of_lt hn]

theorem arraySetup_spec (E : RAMEnv) (s : RAMState) (dstSlot srcSlot dst src len : ℕ)
    (hmeta : (81 : ℕ) < 2 ^ E.W) (hds : dstSlot < 2 ^ E.W) (hss : srcSlot < 2 ^ E.W)
    (hdst : dst < 2 ^ E.W) (hsrc : src < 2 ^ E.W) (hlen : len < 2 ^ E.W)
    (hmD : s.mem dstSlot = dst) (hmS : s.mem srcSlot = src) (hm81 : s.mem 81 = len) :
    runBlock (arraySetupCode dstSlot srcSlot) E s =
      boundaryState (s.pc + 34) (arrayArguments s.mem dst src len) := by
  have hsmall : ∀ i ≤ 81, i % 2 ^ E.W = i := by
    intro i hi
    exact Nat.mod_eq_of_lt (by omega)
  rw [arraySetupCode, runBlock_append, zeroRegs_spec]
  apply ramState_eq_of
  · have hp := runBlock_pc (arraySetupCode dstSlot srcSlot) E s (by
      simp [arraySetupCode, metaReadCode, metaStoreCode, zeroRegsCode])
    rw [arraySetupCode, runBlock_append, zeroRegs_spec] at hp
    change _ = s.pc + 34 at hp
    exact hp
  · simp [runBlock_append, metaRead_spec, metaStore_spec, arrayArguments,
      hsmall, Nat.mod_eq_of_lt hds, Nat.mod_eq_of_lt hss, hmD, hmS, hm81,
      Nat.mod_eq_of_lt hdst, Nat.mod_eq_of_lt hsrc, Nat.mod_eq_of_lt hlen, boundaryState]
  · intro _; rfl

theorem arrayArguments_frame (m : ℕ → ℕ) (dst src len : ℕ) :
    MemoryFrame (fun addr => addr = 64 ∨ addr = 65 ∨ addr = 66) m (arrayArguments m dst src len) := by
  apply MemoryFrame.trans (MemoryFrame.trans
    (MemoryFrame.update_allowed _ m 64 dst (by simp))
    (MemoryFrame.update_allowed _ _ 65 src (by simp)))
    (MemoryFrame.update_allowed _ _ 66 len (by simp))

theorem PolynomialStored.of_frame {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {m m' : ℕ → ℕ} {B cap : ℕ} {p : F[X]} {A : ℕ → Prop}
    (h : PolynomialStored b m B cap p) (hf : MemoryFrame A m m')
    (hout : ∀ i < cap, ¬ A (B + i)) : PolynomialStored b m' B cap p := by
  intro i hi
  rw [hf (B + i) (hout i hi)]
  exact h i hi

theorem detStd_img {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (t N : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) {i : ℕ} (hi : i < 2 ^ w) :
    detStd t N b ι (detImgBase w + i) = enc b (ι i) := by
  have hm : detMulBase w = 64 := rfl
  have hs : detSqBase w = 64 + 2 ^ (2 * w) := rfl
  have hv : detInvBase w = 64 + 2 ^ (2 * w) + 2 ^ (2 * w) := rfl
  have hp : detPosBase w = detInvBase w + 2 ^ w := rfl
  have hg : detImgBase w = detPosBase w + 2 ^ w := rfl
  have he : detEnd w = detImgBase w + 2 ^ w := rfl
  have hpow := Nat.two_pow_pos (2 * w)
  have h0 : ¬ detImgBase w + i < 13 := by omega
  have h1 : ¬ detImgBase w + i < detMulBase w := by omega
  have h2 : ¬ detImgBase w + i < detSqBase w := by omega
  have h3 : ¬ detImgBase w + i < detInvBase w := by omega
  have h4 : ¬ detImgBase w + i < detPosBase w := by omega
  have h5 : ¬ detImgBase w + i < detImgBase w := by omega
  have h6 : detImgBase w + i < detEnd w := by omega
  unfold detStd
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, Nat.add_sub_cancel_left]
  rfl

theorem imageZero_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) (E : RAMEnv) (s : RAMState)
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι) :
    runBlock imageZeroCode E s =
      { s with pc := s.pc + 3, regs := Function.update (Function.update (Function.update s.regs r15 10) r14 (detImgBase w)) r10 (enc b (ι 0)) } := by
  have hpow : (2 : ℕ) ^ w ≤ 2 ^ E.W := by
    rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hend : detEnd w < 2 ^ E.W := by rw [hW]; exact detEnd_lt hw
  have hbase : detImgBase w < 2 ^ E.W := by
    have hpos := Nat.two_pow_pos w
    unfold detEnd at hend
    omega
  have hsmall : (10 : ℕ) < 2 ^ E.W := by
    have hp8 : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (10 : ℕ) < 2 ^ 8) hp8
  have hheader : E.det 10 = detImgBase w := by
    rw [hdet.1 10 (by decide), detStd_hdr t N w b ι (by decide : 10 < 13)]
    rfl
  have himage : E.det (detImgBase w) = enc b (ι 0) := by
    rw [hdet.2 _ (by have h := detMulBase_le_detImgBase w; omega)]
    simpa only [Nat.add_zero] using detStd_img t N b ι (Nat.two_pow_pos w)
  have hv : enc b (ι 0) < 2 ^ E.W := lt_of_lt_of_le (enc_lt b _) hpow
  apply ramState_eq_of
  · simp [imageZeroCode, runBlock_cons, runBlock_nil, execInstr] <;> omega
  · rfl
  · intro r
    fin_cases r <;> simp [imageZeroCode, runBlock_cons, runBlock_nil, execInstr,
      Nat.mod_eq_of_lt hsmall, hheader, Nat.mod_eq_of_lt hbase, himage, Nat.mod_eq_of_lt hv]

theorem cacheUnit_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) (E : RAMEnv) (s : RAMState)
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (h0 : ι 0 ≠ 0) (hm77 : s.mem 77 = w) :
    runBlock cacheUnitCode E s = boundaryState (s.pc + 40) (Function.update s.mem 78 (enc b 1)) := by
  have hwidth : (78 : ℕ) < 2 ^ E.W := by
    have hp8 : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (78 : ℕ) < 2 ^ 8) hp8
  have hwWord : w % 2 ^ E.W = w := Nat.mod_eq_of_lt
    (lt_of_lt_of_le (Nat.lt_two_pow_self (n := w)) (by rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)))
  let sM := runBlock (metaReadCode r3 77) E s
  have hM3 : sM.regs r3 = w := by
    simp [sM, metaRead_spec, Nat.mod_eq_of_lt (show (77 : ℕ) < 2 ^ E.W by omega), hm77, hwWord]
  let sA := runBlock imageZeroCode E sM
  have hA := imageZero_spec b ι t N E sM hw hW hdet
  have hA3 : sA.regs r3 = w := by
    dsimp only [sA]
    rw [hA]
    simpa using hM3
  have hA10 : sA.regs r10 = enc b (ι 0) := by dsimp only [sA]; rw [hA]; simp
  let sB := runBlock fieldInvCode E sA
  have hInv := fieldInvCode_spec b ι t N E sA (ι 0) hw hW hdet hA10
  have hB3 : sB.regs r3 = w := by
    dsimp only [sB]
    rw [hInv]
    simpa using hA3
  have hB10 : sB.regs r10 = enc b ((ι 0)⁻¹) := by dsimp only [sB]; rw [hInv]; simp
  let sCopy := runBlock [iBor r11 r10 r10] E sB
  have hCopy3 : sCopy.regs r3 = w := by simp [sCopy, runBlock_cons, runBlock_nil, execInstr, hB3]
  have hCopy11 : sCopy.regs r11 = enc b ((ι 0)⁻¹) := by
    have hpow : (2 : ℕ) ^ w ≤ 2 ^ E.W := by rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [sCopy, runBlock_cons, runBlock_nil, execInstr, hB10,
      Nat.mod_eq_of_lt (lt_of_lt_of_le (enc_lt b ((ι 0)⁻¹)) hpow)]
  let sC := runBlock imageZeroCode E sCopy
  have hC := imageZero_spec b ι t N E sCopy hw hW hdet
  have hC3 : sC.regs r3 = w := by dsimp only [sC]; rw [hC]; simpa using hCopy3
  have hC10 : sC.regs r10 = enc b (ι 0) := by dsimp only [sC]; rw [hC]; simp
  have hC11 : sC.regs r11 = enc b ((ι 0)⁻¹) := by dsimp only [sC]; rw [hC]; simpa using hCopy11
  let sD := runBlock fieldMulCode E sC
  have hMul := fieldMulCode_spec b ι t N E sC (ι 0) (ι 0)⁻¹ hw hW hdet hC3 hC10 hC11
  have hD10 : sD.regs r10 = enc b 1 := by
    dsimp only [sD]
    rw [hMul]
    simp [mul_inv_cancel₀ h0]
  let sE := runBlock (metaStoreCode r10 78) E sD
  have hmD : sD.mem = s.mem := rfl
  have hmE : sE.mem = Function.update s.mem 78 (enc b 1) := by
    dsimp only [sE]
    rw [metaStore_spec E _ r10 78 (by decide)]
    change Function.update sD.mem (78 % 2 ^ E.W) (sD.regs r10) = Function.update s.mem 78 (enc b 1)
    rw [Nat.mod_eq_of_lt hwidth, hD10, hmD]
  have hfinish : runBlock cacheUnitCode E s = boundaryState (sE.pc + 16) sE.mem := by
    have he : runBlock cacheUnitCode E s = runBlock zeroRegsCode E sE := by
      simp only [cacheUnitCode, runBlock_append] <;> rfl
    rw [he, zeroRegs_spec]
  have hpc : sE.pc + 16 = s.pc + 40 := by
    have hp := runBlock_pc cacheUnitCode E s (by
      simp [cacheUnitCode, metaReadCode, imageZeroCode, fieldInvCode, fieldMulCode, metaStoreCode, zeroRegsCode])
    rw [hfinish] at hp
    exact hp
  rw [hfinish, hpc, hmE]

/-- Coefficient-array copy with dynamic pointers held in fixed metadata. -/
theorem copyFromSlots_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (P : Program) (E : RAMEnv)
    (pc dstSlot srcSlot dst src cap : ℕ) (f : F[X]) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile (copyFromSlotsProcedure dstSlot srcSlot) pc))
    (hmeta : (81 : ℕ) < 2 ^ E.W) (hds : dstSlot < 2 ^ E.W) (hss : srcSlot < 2 ^ E.W)
    (hwe : w ≤ E.W) (hcap : 1 ≤ cap) (hdst : 128 ≤ dst) (hsrc : 128 ≤ src)
    (hDstWord : dst + cap ≤ 2 ^ E.W) (hSrcWord : src + cap ≤ 2 ^ E.W)
    (hdisj : src + cap ≤ dst ∨ dst + cap ≤ src) (hf : PolynomialStored b m src cap f)
    (hmd : m dstSlot = dst) (hms : m srcSlot = src) (hm81 : m 81 = cap) :
    Sem P E pc (pc + 70) (boundaryState pc m)
      (fun k z => k ≤ 12 * cap + 60 ∧ ∃ m', z = boundaryState (pc + 70) m' ∧
        PolynomialStored b m' dst cap f ∧ MemoryFrame (copyFromSlotsWritable dst cap) m m') := by
  let m1 := arrayArguments m dst src cap
  let m2 := writeArray dst m1 (fun i => m1 (src + i)) cap
  have hcapWord : cap < 2 ^ E.W :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_left (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 128) hdst))
      hDstWord
  have hdstWord : dst < 2 ^ E.W :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hcap))
      hDstWord
  have hsrcWord : src < 2 ^ E.W :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hcap))
      hSrcWord
  have hf1 : PolynomialStored b m1 src cap f := by
    intro i hi
    change arrayArguments m dst src cap (src + i) = enc b (f.coeff i)
    rw [arrayArguments_frame m dst src cap (src + i) (by
      have hge : 66 < src + i :=
        lt_of_lt_of_le (by norm_num : 66 < 128) (le_trans hsrc (Nat.le_add_right src i))
      exact fun h => h.elim (Nat.ne_of_gt (lt_trans (by norm_num : 64 < 66) hge))
        (fun h => h.elim (Nat.ne_of_gt (lt_trans (by norm_num : 65 < 66) hge)) (Nat.ne_of_gt hge)))]
    exact hf i hi
  obtain ⟨hSetupAt, hCopyAt⟩ := At.seqStmt hAt
  have hSetup : Sem P E pc (pc + 34) (boundaryState pc m)
      (fun k z => k ≤ 34 ∧ z = boundaryState (pc + 34) m1) := by
    exact Sem.boundary_block P E _ (arraySetupCode dstSlot srcSlot) m m1 hSetupAt
      (by simp [arraySetupCode, metaReadCode, metaStoreCode, zeroRegsCode])
      (arraySetup_spec E _ dstSlot srcSlot dst src cap hmeta hds hss hdstWord hsrcWord hcapWord hmd hms hm81)
  have hCopy := copyProcedure_spec P E (pc + 34) dst src cap m1 hCopyAt
    (lt_trans (by norm_num : (66 : ℕ) < 81) hmeta) hdstWord hsrcWord hcapWord
    hDstWord hSrcWord hdisj (fun i hi => by
      have hv : m1 (src + i) = enc b (f.coeff i) := hf1 i hi
      rw [hv]
      exact lt_of_lt_of_le (enc_lt b _) (Nat.pow_le_pow_right (by norm_num) hwe))
    (by simp [m1, arrayArguments]) (by simp [m1, arrayArguments]) (by simp [m1, arrayArguments])
  have hFull := Sem.seq_bound hSetup (fun z _ hz => by subst z; exact hCopy)
  have hf12 : MemoryFrame (fun addr => dst ≤ addr ∧ addr < dst + cap) m1 m2 := by
    intro addr ha
    exact writeArray_frame dst m1 _ cap addr
      (Or.elim (not_and_or.mp ha) (fun h => Or.inl (not_le.mp h)) (fun h => Or.inr (le_of_not_gt h)))
  refine Sem.mono hFull ?_
  intro k z hQ
  refine ⟨le_trans hQ.1 (le_of_eq (by ring)), m2, hQ.2, ?_, ?_⟩
  · intro i hi
    change writeArray dst m1 (fun j => m1 (src + j)) cap (dst + i) = enc b (f.coeff i)
    rw [writeArray_get _ _ _ cap i hi]
    exact hf1 i hi
  · refine MemoryFrame.trans ((arrayArguments_frame m dst src cap).mono ?_)
      (hf12.mono (by intro addr ha; exact Or.inr (Or.inr (Or.inr ha))))
    intro addr ha
    dsimp [copyFromSlotsWritable]
    rcases ha with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

theorem PolynomialStored.after_root_copy {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {m m' : ℕ → ℕ} {B dst cap : ℕ} {f : F[X]}
    (h : PolynomialStored b m B cap f) (hB : 128 ≤ B) (hdisj : dst + cap ≤ B ∨ B + cap ≤ dst)
    (hf : MemoryFrame (copyFromSlotsWritable dst cap) m m') : PolynomialStored b m' B cap f := by
  apply h.of_frame hf
  intro i hi
  dsimp [copyFromSlotsWritable]
  omega

theorem root_copy_meta {m m' : ℕ → ℕ} {dst cap slot : ℕ}
    (hf : MemoryFrame (copyFromSlotsWritable dst cap) m m') (hdst : 128 ≤ dst)
    (hlo : 67 ≤ slot) (hhi : slot < 128) : m' slot = m slot := by
  exact hf slot (by dsimp [copyFromSlotsWritable]; omega)

theorem QueueWorkspaceSeparated.readonly {R U D C TB ZB cap QB T : ℕ}
    (h : QueueWorkspaceSeparated R U D C TB ZB cap QB T) (hQB : 128 ≤ QB)
    (addr : ℕ) (hlo : QB ≤ addr) (hhi : addr < QB + T * cap) :
    ¬ rootComputeWritable R U D C TB cap addr := by
  have hR := h.QR
  have hU := h.QU
  have hD := h.QD
  have hC := h.QC
  have hT := h.QT
  dsimp [rootComputeWritable, rootComputeMeta]
  omega

/-- Nonempty disjoint integer intervals admit one of the two address orders. -/
theorem interval_disjoint_of_readonly (A n B len : ℕ) (hn : 1 ≤ n) (hlen : 1 ≤ len)
    (h : ∀ i < n, ¬ (B ≤ A + i ∧ A + i < B + len)) :
    A + n ≤ B ∨ B + len ≤ A := by
  by_contra hc
  have hleft : B < A + n := by omega
  have hright : A < B + len := by omega
  by_cases hab : A < B
  · have hi : B - A < n := by omega
    have he : A + (B - A) = B := by omega
    exact h (B - A) hi ⟨by omega, by omega⟩
  · exact h 0 (by omega) ⟨by omega, by omega⟩

/-- The gcd result stays in the original Euclidean workspace, hence it can
be copied into a separate queue even after an arbitrary number of row swaps. -/
theorem QueueWorkspaceSeparated.gcd_output_disjoint {R U D C TB ZB cap QB T out : ℕ}
    (h : QueueWorkspaceSeparated R U D C TB ZB cap QB T) (hQB : 128 ≤ QB)
    (hcap : 1 ≤ cap) (hT : 1 ≤ T) (hrange : ∀ i < cap, padeWritable R U D C cap (out + i)) :
    out + cap ≤ QB ∨ QB + T * cap ≤ out := by
  apply interval_disjoint_of_readonly out cap QB (T * cap) hcap (by
    have hm := Nat.mul_le_mul hT hcap
    simpa using hm)
  intro i hi hIn
  have hcomp : rootComputeWritable R U D C TB cap (out + i) := by
    have hrow := hrange i hi
    dsimp [padeWritable] at hrow
    dsimp [rootComputeWritable, rootComputeMeta]
    omega
  exact h.readonly hQB _ hIn.1 hIn.2 hcomp

theorem position_index_word (p M : ℕ) (hM : 1 < M) (hp : p < M) :
    (p + M - positionValidBit p) % M = p - 1 := by
  by_cases hz : p = 0
  · subst p
    simp [positionValidBit]
  · have hp0 : 0 < p := by omega
    rw [positionValidBit, if_pos hp0]
    have he : p + M - 1 = p - 1 + M := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem FieldArrayStored.of_frame {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {m m' : ℕ → ℕ} {B len : ℕ} {v : ℕ → F} {A : ℕ → Prop}
    (h : FieldArrayStored b m B len v) (hf : MemoryFrame A m m') (hr : ∀ j < len, ¬ A (B + j)) :
    FieldArrayStored b m' B len v := by
  intro j hj
  rw [hf (B + j) (hr j hj)]
  exact h j hj

theorem decoderCapacity_pos (t : ℕ) : 2 ≤ decoderCapacity t := by unfold decoderCapacity decoderLength; omega

theorem decoderRow_low (t k : ℕ) : 128 ≤ decoderRowBase t k := by
  unfold decoderRowBase decoderSavedBase
  omega

theorem decoderRow_end_le_queue (t k : ℕ) (hk : k < 8) :
    decoderRowBase t k + decoderCapacity t ≤ decoderQueue0 t := by
  have hm := Nat.mul_le_mul_right (decoderCapacity t) (show k + 1 ≤ 8 by omega)
  have he : (k + 1) * decoderCapacity t = k * decoderCapacity t + decoderCapacity t := by ring
  unfold decoderQueue0 decoderRowBase
  omega

theorem decoderRows_pade (t : ℕ) :
    RowsLayout (decoderRowBase t 0) (decoderRowBase t 1) (decoderRowBase t 2) (decoderRowBase t 3) (decoderCapacity t) := by
  have hc := decoderCapacity_pos t
  constructor <;> dsimp [decoderRowBase, decoderSavedBase] <;> omega

theorem decoderRow_word (E : RAMEnv) (t k : ℕ) (hk : k < 8) (hword : decoderAllocEnd t ≤ 2 ^ E.W) :
    decoderRowBase t k + decoderCapacity t ≤ 2 ^ E.W := by
  have hr := decoderRow_end_le_queue t k hk
  have hQ : decoderQueue0 t ≤ decoderAllocEnd t := by
    unfold decoderAllocEnd decoderVerifyBase decoderOutputBase decoderQueue1
    omega
  omega

theorem decoderQueue0_pade_separated (t : ℕ) :
    QueueWorkspaceSeparated (decoderRowBase t 0) (decoderRowBase t 1) (decoderRowBase t 2) (decoderRowBase t 3)
      (decoderRowBase t 4) (decoderRowBase t 5) (decoderCapacity t) (decoderQueue0 t) t :=
  ⟨Or.inr (decoderRow_end_le_queue t 0 (by norm_num)), Or.inr (decoderRow_end_le_queue t 1 (by norm_num)),
   Or.inr (decoderRow_end_le_queue t 2 (by norm_num)), Or.inr (decoderRow_end_le_queue t 3 (by norm_num)),
   Or.inr (decoderRow_end_le_queue t 4 (by norm_num)), Or.inr (decoderRow_end_le_queue t 5 (by norm_num))⟩

theorem saved_rows_zero {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (t : ℕ) (m : ℕ → ℕ)
    (htail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → m addr = 0) (k : ℕ) :
    PolynomialStored b m (decoderRowBase t k) (decoderCapacity t) 0 := by
  intro j hj
  rw [Polynomial.coeff_zero, enc_zero]
  apply htail
  unfold decoderRowBase
  omega

theorem NoBranch.append_blocks {a b : List Instr} (ha : NoBranch a) (hb : NoBranch b) : NoBranch (a ++ b) := by
  exact (noBranch_append a b).mpr ⟨ha, hb⟩

theorem MetadataExpr.noBranch (expr : MetadataExpr) : NoBranch expr.code := by
  cases expr <;> simp [MetadataExpr.code]

theorem metadata_poly_intermediates (a b c t M : ℕ) (hM : 0 < M) (h : a * t * t + b * t + c < M) :
    a * t < M ∧ a * t * t < M ∧ b * t < M ∧ a * t * t + b * t < M := by
  have hm : a * t ≤ a * t * t := by
    by_cases ht : t = 0
    · simp [ht]
    · simpa only [Nat.mul_one] using Nat.mul_le_mul_left (a * t) (show 1 ≤ t by omega)
  omega

theorem MetadataExpr.spec (expr : MetadataExpr) (E : RAMEnv) (s : RAMState) (t : ℕ)
    (hf : expr.fits E t) (ht : s.regs r0 = t) :
    ∃ z, runBlock expr.code E s = z ∧ z.pc = s.pc + expr.code.length ∧ z.mem = s.mem ∧
      z.regs r10 = expr.value E t ∧ z.regs r0 = t := by
  cases expr with
  | poly a b c =>
    obtain ⟨ha, hb, hc, hv⟩ := hf
    have hInt := metadata_poly_intermediates a b c t (2 ^ E.W) (Nat.two_pow_pos _) hv
    let z := runBlock (MetadataExpr.poly a b c).code E s
    refine ⟨z, rfl, runBlock_pc _ E s (by simp [MetadataExpr.code]), rfl, ?_, ?_⟩
    · simp [z, MetadataExpr.code, MetadataExpr.value, runBlock_cons, runBlock_nil, execInstr, ht,
        Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hv,
        Nat.mod_eq_of_lt hInt.1, Nat.mod_eq_of_lt hInt.2.1, Nat.mod_eq_of_lt hInt.2.2.1, Nat.mod_eq_of_lt hInt.2.2.2]
    · simp [z, MetadataExpr.code, runBlock_cons, runBlock_nil, execInstr, ht]
  | header slot =>
    let z := runBlock (MetadataExpr.header slot).code E s
    refine ⟨z, rfl, runBlock_pc _ E s (by simp [MetadataExpr.code]), rfl, ?_, ?_⟩
    · simp [z, MetadataExpr.code, MetadataExpr.value, runBlock_cons, runBlock_nil, execInstr, Nat.mod_eq_of_lt hf]
    · simp [z, MetadataExpr.code, runBlock_cons, runBlock_nil, execInstr, ht]

theorem metadataAssignment_spec (a : ℕ × MetadataExpr) (E : RAMEnv) (s : RAMState) (t : ℕ)
    (hslot : a.1 < 2 ^ E.W) (hf : a.2.fits E t) (ht : s.regs r0 = t) :
    ∃ z, runBlock (metadataAssignmentCode a) E s = z ∧ z.pc = s.pc + (metadataAssignmentCode a).length ∧
      z.mem = Function.update s.mem a.1 (a.2.value E t) ∧ z.regs r0 = t := by
  obtain ⟨z1, hz1, hpc1, hmem1, h10, h0⟩ := a.2.spec E s t hf ht
  let z2 := runBlock (metaStoreCode r10 a.1) E z1
  have hm : z2.mem = Function.update s.mem a.1 (a.2.value E t) := by
    dsimp only [z2]
    rw [metaStore_spec E _ r10 a.1 (by decide)]
    change Function.update z1.mem (a.1 % 2 ^ E.W) (z1.regs r10) = _
    rw [Nat.mod_eq_of_lt hslot, h10, hmem1]
  have he : runBlock (metadataAssignmentCode a) E s = z2 := by rw [metadataAssignmentCode, runBlock_append, hz1]
  refine ⟨z2, he, ?_, hm, ?_⟩
  · have hp := runBlock_pc (metadataAssignmentCode a) E s (by
      exact a.2.noBranch.append_blocks (by simp [metaStoreCode]))
    rw [he] at hp
    exact hp
  · simp [z2, metaStore_spec, h0]

theorem metadataAssignments_spec (as : List (ℕ × MetadataExpr)) (E : RAMEnv) (s : RAMState) (t : ℕ)
    (hf : ∀ a ∈ as, a.1 < 2 ^ E.W ∧ a.2.fits E t) (ht : s.regs r0 = t) :
    ∃ z, runBlock (metadataAssignmentsCode as) E s = z ∧ z.pc = s.pc + (metadataAssignmentsCode as).length ∧
      z.mem = metadataAssignmentsMemory E t s.mem as ∧ z.regs r0 = t := by
  induction as generalizing s with
  | nil => exact ⟨s, rfl, rfl, rfl, ht⟩
  | cons a as ih =>
    have ha := hf a (by simp)
    obtain ⟨z1, hz1, hpc1, hmem1, h0⟩ := metadataAssignment_spec a E s t ha.1 ha.2 ht
    obtain ⟨z2, hz2, hpc2, hmem2, h20⟩ := ih z1 (fun a ha => hf a (by simp [ha])) h0
    refine ⟨z2, ?_, ?_, ?_, h20⟩
    · simp only [metadataAssignmentsCode, List.flatMap_cons, runBlock_append]
      rw [hz1]
      exact hz2
    · rw [hpc2, hpc1]
      simp only [metadataAssignmentsCode, List.flatMap_cons, List.length_append]
      omega
    · rw [hmem2, hmem1]
      rfl

theorem metadataAssignments_frame (as : List (ℕ × MetadataExpr)) (E : RAMEnv) (t : ℕ) (m : ℕ → ℕ)
    (hs : ∀ a ∈ as, a.1 < 128) : MemoryFrame (fun addr => addr < 128) m (metadataAssignmentsMemory E t m as) := by
  induction as generalizing m with
  | nil => intro addr _; rfl
  | cons a as ih =>
    apply MemoryFrame.trans (MemoryFrame.meta_update m a.1 (a.2.value E t) (hs a (by simp)))
    exact ih _ (fun a ha => hs a (by simp [ha]))

theorem metadataAssignments_noBranch (as : List (ℕ × MetadataExpr)) : NoBranch (metadataAssignmentsCode as) := by
  induction as with
  | nil => trivial
  | cons a as ih => exact (a.2.noBranch.append_blocks (by simp [metaStoreCode])).append_blocks ih

theorem metadataAssignmentsCode_length (as : List (ℕ × MetadataExpr)) :
    (metadataAssignmentsCode as).length = (as.map (fun a => a.2.code.length + 3)).sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    change (metadataAssignmentCode a ++ metadataAssignmentsCode as).length = _
    rw [List.length_append, ih]
    simp [metadataAssignmentCode, metaStoreCode]

theorem decoderMetadata_fits (E : RAMEnv) (t : ℕ) (hEnd : decoderAllocEnd t < 2 ^ E.W) :
    ∀ a ∈ decoderMetadataAssignments, metadataAssignmentFits E t a := by
  have hsmall (i : ℕ) (hi : i ≤ 144) : i < 2 ^ E.W := by
    have he := decoderAllocEnd_eq t
    omega
  have hpoly (a b c : ℕ) (ha : a ≤ 8) (hb : b ≤ 44) (hc : c ≤ 144) : a * t * t + b * t + c < 2 ^ E.W := by
    calc
      a * t * t + b * t + c ≤ 8 * t * t + 44 * t + 144 := by gcongr
      _ = decoderAllocEnd t := (decoderAllocEnd_eq t).symm
      _ < 2 ^ E.W := hEnd
  have hPolyAssignment (slot a b c : ℕ) (hs : slot ≤ 144) (ha : a ≤ 8) (hb : b ≤ 44) (hc : c ≤ 144) :
      metadataAssignmentFits E t (slot, .poly a b c) :=
    ⟨hsmall slot hs, hsmall a (by omega), hsmall b (by omega), hsmall c hc, hpoly a b c ha hb hc⟩
  have hHeaderAssignment (slot h : ℕ) (hs : slot ≤ 144) (hh : h ≤ 144) :
      metadataAssignmentFits E t (slot, .header h) := ⟨hsmall slot hs, hsmall h hh⟩
  intro a ha
  simp [decoderMetadataAssignments] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hPolyAssignment _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    | exact hHeaderAssignment _ _ (by norm_num) (by norm_num)

theorem DecoderMetadata.of_preserved {t w N : ℕ} {m m' : ℕ → ℕ} (h : DecoderMetadata t w N m)
    (hs : ∀ slot, decoderMetadataSlots slot → m' slot = m slot) : DecoderMetadata t w N m' := by
  constructor
  · exact (hs 72 (by norm_num [decoderMetadataSlots])).trans h.rowR
  · exact (hs 73 (by norm_num [decoderMetadataSlots])).trans h.rowU
  · exact (hs 74 (by norm_num [decoderMetadataSlots])).trans h.rowD
  · exact (hs 75 (by norm_num [decoderMetadataSlots])).trans h.rowC
  · exact (hs 76 (by norm_num [decoderMetadataSlots])).trans h.length
  · exact (hs 77 (by norm_num [decoderMetadataSlots])).trans h.dimension
  · exact (hs 79 (by norm_num [decoderMetadataSlots])).trans h.saved
  · exact (hs 80 (by norm_num [decoderMetadataSlots])).trans h.capacityParameter
  · exact (hs 81 (by norm_num [decoderMetadataSlots])).trans h.capacity
  · exact (hs 82 (by norm_num [decoderMetadataSlots])).trans h.universeSize
  · exact (hs 83 (by norm_num [decoderMetadataSlots])).trans h.firstQueue
  · exact (hs 84 (by norm_num [decoderMetadataSlots])).trans h.secondQueue
  · exact (hs 85 (by norm_num [decoderMetadataSlots])).trans h.output
  · exact (hs 86 (by norm_num [decoderMetadataSlots])).trans h.verification
  · exact (hs 94 (by norm_num [decoderMetadataSlots])).trans h.padeCounter
  · exact (hs 102 (by norm_num [decoderMetadataSlots])).trans h.fixedR
  · exact (hs 103 (by norm_num [decoderMetadataSlots])).trans h.fixedD
  · exact (hs 104 (by norm_num [decoderMetadataSlots])).trans h.fixedU
  · exact (hs 105 (by norm_num [decoderMetadataSlots])).trans h.fixedC
  · exact (hs 106 (by norm_num [decoderMetadataSlots])).trans h.fixedT
  · exact (hs 107 (by norm_num [decoderMetadataSlots])).trans h.fixedQ1
  · exact (hs 108 (by norm_num [decoderMetadataSlots])).trans h.fixedZ

theorem decoderMetadataMemory_spec (E : RAMEnv) (t w N : ℕ) (m : ℕ → ℕ)
    (h1 : E.det 1 % 2 ^ E.W = w) (h2 : E.det 2 % 2 ^ E.W = N) :
    DecoderMetadata t w N (decoderMetadataMemory E t m) := by
  constructor <;>
    norm_num [decoderMetadataMemory, metadataAssignmentsMemory, decoderMetadataAssignments, MetadataExpr.value,
      h1, h2, decoderRowBase, decoderSavedBase, decoderCapacity, decoderLength, decoderQueue0, decoderQueue1, decoderOutputBase, decoderVerifyBase] <;> ring

theorem decoderMetadataCode_length : decoderMetadataCode.length = 248 := by
  rw [decoderMetadataCode, List.length_append, List.length_append, metadataAssignmentsCode_length]
  norm_num [decoderMetadataAssignments, MetadataExpr.code, zeroRegsCode]

theorem decoderMetadataCode_noBranch : NoBranch decoderMetadataCode := by
  exact ((by simp : NoBranch [iImm r15 0, iTbl r0 r15]).append_blocks
    (metadataAssignments_noBranch decoderMetadataAssignments)).append_blocks (by simp [zeroRegsCode])

theorem decoderMetadataCode_spec (E : RAMEnv) (pc t : ℕ) (m : ℕ → ℕ)
    (hEnd : decoderAllocEnd t < 2 ^ E.W) (h0 : E.det 0 % 2 ^ E.W = t) :
    runBlock decoderMetadataCode E (boundaryState pc m) = boundaryState (pc + 248) (decoderMetadataMemory E t m) := by
  let s1 := runBlock [iImm r15 0, iTbl r0 r15] E (boundaryState pc m)
  have h10 : s1.regs r0 = t := by simp [s1, runBlock_cons, runBlock_nil, execInstr, h0]
  have h1mem : s1.mem = m := rfl
  obtain ⟨s2, hs2, hpc2, hmem2, h20⟩ := metadataAssignments_spec decoderMetadataAssignments E s1 t
    (decoderMetadata_fits E t hEnd) h10
  have he : runBlock decoderMetadataCode E (boundaryState pc m) = runBlock zeroRegsCode E s2 := by
    simp only [decoderMetadataCode, runBlock_append]
    rw [hs2]
  have hfinish : runBlock decoderMetadataCode E (boundaryState pc m) = boundaryState (s2.pc + 16) s2.mem := by rw [he, zeroRegs_spec]
  have hpc : s2.pc + 16 = pc + 248 := by
    have hp := runBlock_pc decoderMetadataCode E (boundaryState pc m) decoderMetadataCode_noBranch
    rw [decoderMetadataCode_length, hfinish] at hp
    exact hp
  rw [hfinish, hpc, hmem2, h1mem]
  rfl

theorem decoderMetadataMemory_frame (E : RAMEnv) (t : ℕ) (m : ℕ → ℕ) :
    MemoryFrame (fun addr => addr < 128) m (decoderMetadataMemory E t m) :=
  metadataAssignments_frame decoderMetadataAssignments E t m (by
    intro a ha
    simp [decoderMetadataAssignments] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num)

theorem padeLoop_strong_spec {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (pc RB UB DB CB L cap n0 : ℕ)
    (e : ℕ → F) (s0 : PadeState F) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile padeLoopStmt pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (ht : 1 ≤ t) (hL : L = 2 * t + 1) (hcap : cap = 2 * L)
    (hrows : PadeRows b E RB UB DB CB L cap m s0) (hinv : PadeInv e t s0)
    (hn0 : n0 < 2 ^ E.W) (hm80 : m 80 = t) (hm94 : m 94 = n0) :
    Sem P E pc (pc + 566) (rankState pc m n0)
      (fun k z => k ≤ (34 * cap + (48 * L + 187) * L + 289) * n0 + 1 ∧
        z.regs = (fun _ => 0) ∧ z.mem 94 = 0 ∧ z.mem 80 = t ∧
        MemoryFrame (padeLoopWritable RB UB DB CB cap) m z.mem ∧
        ∃ RB' UB' DB' CB', PadeRows b E RB' UB' DB' CB' L cap z.mem (padeRun t n0 s0) ∧
          ∀ addr, padeWritable RB' UB' DB' CB' cap addr ↔ padeWritable RB UB DB CB cap addr) := by
  let I := fun n z => n ≤ n0 ∧ padeLoopInvariant b E RB UB DB CB L cap e t (padeRun t n0 s0) m n z
  have hW1 : 1 < 2 ^ E.W := by have h := hrows.layout.Rlow; have h' := hrows.Rword; omega
  have hframe : ∀ n z pc', I n z → I n { z with pc := pc' } := by
    intro n z pc' h
    simpa only [I, padeLoopInvariant] using h
  have hcounter : ∀ n z, I n z → z.regs r9 = n := by
    intro n z h
    rw [h.2.1, Function.update_self]
  obtain ⟨_, _, hBodyAt, hJumpAt⟩ := at_loop hAt
  have hbody : ∀ n z, I (n + 1) z → z.pc = pc →
      Sem P E (pc + 1) pc { z with pc := pc + 1 }
        (fun k z' => k ≤ 34 * cap + (48 * L + 187) * L + 288 ∧ I n z') := by
    intro n z hI hpc
    obtain ⟨hn, hregs, h94, h80, hframe0, RB1, UB1, DB1, CB1, s, hr, hi, hremaining, hfoot0⟩ := hI
    have hz : { z with pc := pc + 1 } = rankState (pc + 1) z.mem (n + 1) := by
      apply ramState_eq_of
      · rfl
      · rfl
      · intro r; exact congrFun hregs r
    rw [hz]
    have hrun := padeLoopBody_spec b ι t N P E (pc + 1) RB1 UB1 DB1 CB1 L cap n e s z.mem
      hBodyAt hw hW hdet ht hL hcap hr hi (by omega) h80 h94
    refine Sem.jmp_append (hAt := hJumpAt) (Sem.mono hrun ?_)
    intro k z' hQ
    obtain ⟨hk, m', RB2, UB2, DB2, CB2, hz', h94', hr', hf', hfoot'⟩ := hQ
    refine ⟨by omega, by omega, ?_⟩
    rw [hz']
    refine ⟨rfl, h94', ?_, ?_, RB2, UB2, DB2, CB2, padeTick t s,
      hr', padeInv_tick ht hi, ?_, ?_⟩
    · change m' 80 = t
      have hnot : ¬ padeLoopWritable RB1 UB1 DB1 CB1 cap 80 := by
        dsimp [padeLoopWritable, padeWritable]
        have hR := hr.layout.Rlow
        have hU := hr.layout.Ulow
        have hD := hr.layout.Dlow
        have hC := hr.layout.Clow
        omega
      exact (hf' 80 hnot).trans h80
    · exact MemoryFrame.trans hframe0 (hf'.mono (by
        intro addr ha
        rcases ha with h94 | hp
        · exact Or.inl h94
        · exact Or.inr ((hfoot0 addr).mp hp)))
    · exact (padeRun_succ_tick t n s).trans hremaining
    · intro addr
      exact (hfoot' addr).trans (hfoot0 addr)
  have hinit : I n0 (rankState pc m n0) := by
    refine ⟨le_rfl, rfl, hm94, hm80, ?_, RB, UB, DB, CB, s0, hrows, hinv, rfl, ?_⟩
    · intro addr _; rfl
    · intro addr; rfl
  have hloop := Sem.loop_invariant P E pc padeLoopBody hAt hW1 I
    (34 * cap + (48 * L + 187) * L + 288) hframe hcounter hbody n0 (rankState pc m n0) hinit rfl
  refine Sem.mono hloop ?_
  intro k z hQ
  obtain ⟨hk, _, hregs, h94, h80, hf, RB', UB', DB', CB', s, hr, _, hremaining, hfoot⟩ := hQ
  have hs : s = padeRun t n0 s0 := hremaining
  refine ⟨hk, ?_, h94, h80, hf, RB', UB', DB', CB', ?_, hfoot⟩
  · rw [hregs]
    funext r
    simp [Function.update_apply]
  · simpa only [hs] using hr

theorem padeSolveProcedure_strong_spec {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (pc RB UB DB CB L cap n0 : ℕ)
    (e : ℕ → F) (s0 : PadeState F) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile padeSolveProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (ht : 1 ≤ t) (hL : L = 2 * t + 1) (hcap : cap = 2 * L)
    (hrows : PadeRows b E RB UB DB CB L cap m s0) (hinv : PadeInv e t s0)
    (hn0 : n0 < 2 ^ E.W) (hm80 : m 80 = t) (hm94 : m 94 = n0) :
    Sem P E pc (pc + 569) (boundaryState pc m)
      (fun k z => k ≤ (34 * cap + (48 * L + 187) * L + 289) * n0 + 4 ∧
        ∃ m' RB' UB' DB' CB', z = boundaryState (pc + 569) m' ∧ m' 94 = 0 ∧ m' 80 = t ∧
          MemoryFrame (padeLoopWritable RB UB DB CB cap) m m' ∧
          PadeRows b E RB' UB' DB' CB' L cap m' (padeRun t n0 s0) ∧
          ∀ addr, padeWritable RB' UB' DB' CB' cap addr ↔ padeWritable RB UB DB CB cap addr) := by
  obtain ⟨hReadAt, hLoopAt⟩ := At.seqStmt hAt
  have hwidth : (94 : ℕ) < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : (94 : ℕ) < 2 ^ 8) hp
  have hRead : Sem P E pc (pc + 3) (boundaryState pc m)
      (fun k z => k ≤ 3 ∧ z = rankState (pc + 3) m n0) := by
    refine Sem.mono (Sem.block P E pc (metaReadCode r9 94) _ hReadAt (by simp [metaReadCode]) rfl) ?_
    intro k z hQ
    obtain ⟨hk, hz⟩ := hQ
    exact ⟨by change k = 3 at hk; omega, hz.trans (rankReadSlot_spec E pc m 94 n0 hwidth hn0 hm94)⟩
  have hLoop := padeLoop_strong_spec b ι t N P E (pc + 3) RB UB DB CB L cap n0 e s0 m hLoopAt
    hw hW hdet ht hL hcap hrows hinv hn0 hm80 hm94
  have hFull := Sem.seq_bound hRead (fun z _ hz => by subst z; exact hLoop)
  obtain ⟨hpc, k, z, hrun, hreturn, hk, hregs, h94, h80, hf, RB', UB', DB', CB', hr, hfoot⟩ := hFull
  refine ⟨hpc, k, z, hrun, hreturn, by omega, z.mem, RB', UB', DB', CB', ?_, h94, h80, hf, hr, hfoot⟩
  apply ramState_eq_of
  · exact hreturn
  · rfl
  · intro r
    simpa only [boundaryState] using congrFun hregs r

theorem padeSolveProcedure_minimal_strong {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (pc RB UB DB CB L cap : ℕ) (e : ℕ → F) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile padeSolveProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (ht : 1 ≤ t) (hL : L = 2 * t + 1) (hcap : cap = 2 * L)
    (hrows : PadeRows b E RB UB DB CB L cap m (padeInitial e t))
    (hm80 : m 80 = t) (hm94 : m 94 = L) :
    Sem P E pc (pc + 569) (boundaryState pc m)
      (fun k z => k ≤ (34 * cap + (48 * L + 187) * L + 289) * L + 4 ∧
        ∃ m' RB' UB' DB' CB', z = boundaryState (pc + 569) m' ∧
          PadeRows b E RB' UB' DB' CB' L cap m' (padeSolve e t) ∧
          KeySolEMin e t (padeSolve e t).curC (padeSolve e t).rem ∧
          MemoryFrame (padeLoopWritable RB UB DB CB cap) m m' ∧
          ∀ addr, padeWritable RB' UB' DB' CB' cap addr ↔ padeWritable RB UB DB CB cap addr) := by
  have hLWord : L < 2 ^ E.W := by have h := hrows.Rword; have h' := hrows.layout.Rlow; omega
  have h := padeSolveProcedure_strong_spec b ι t N P E pc RB UB DB CB L cap L e (padeInitial e t) m hAt
    hw hW hdet ht hL hcap hrows (padeInv_initial e t ht) hLWord hm80 hm94
  refine Sem.mono h ?_
  intro k z hQ
  obtain ⟨hk, m', RB', UB', DB', CB', hz, _, _, hf, hr, hfoot⟩ := hQ
  refine ⟨hk, m', RB', UB', DB', CB', hz, ?_, padeSolve_minimal e t ht, hf, hfoot⟩
  simpa only [padeSolve, hL] using hr

theorem initialPolynomialsCode_length : initialPolynomialsCode.length = 33 := rfl

theorem initialPolynomials_spec {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (E : RAMEnv) (s : RAMState) (R C L : ℕ)
    (hmeta : (78 : ℕ) < 2 ^ E.W) (hwe : w ≤ E.W) (hR : 128 ≤ R) (hC : C < 2 ^ E.W)
    (hL : 1 ≤ L) (hLword : L < 2 ^ E.W) (hRword : R + L ≤ 2 ^ E.W)
    (hm72 : s.mem 72 = R) (hm75 : s.mem 75 = C) (hm76 : s.mem 76 = L) (hm78 : s.mem 78 = enc b 1) :
    runBlock initialPolynomialsCode E s = boundaryState (s.pc + 33)
      (Function.update (Function.update s.mem (R + (L - 1)) (enc b 1)) C (enc b 1)) := by
  have hsmall (i : ℕ) (hi : i ≤ 78) : i % 2 ^ E.W = i := Nat.mod_eq_of_lt (by omega)
  have hR0 : R % 2 ^ E.W = R := Nat.mod_eq_of_lt (by omega)
  have hL0 : L % 2 ^ E.W = L := Nat.mod_eq_of_lt hLword
  have hC0 : C % 2 ^ E.W = C := Nat.mod_eq_of_lt hC
  have hsub : (L + 2 ^ E.W - 1) % 2 ^ E.W = L - 1 := by
    simpa [positionValidBit, show 0 < L by omega] using position_index_word L (2 ^ E.W) (by omega) hLword
  have haddr : (R + (L - 1)) % 2 ^ E.W = R + (L - 1) := Nat.mod_eq_of_lt (by omega)
  have hUnit : enc b (1 : F) % 2 ^ E.W = enc b (1 : F) :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le (enc_lt b _) (Nat.pow_le_pow_right (by norm_num) hwe))
  let sA := runBlock initialRowOffsetCode E s
  have hA2 : sA.regs r2 = R + (L - 1) := by
    simp [sA, initialRowOffsetCode, runBlock_append, metaRead_spec, runBlock_cons, runBlock_nil, execInstr,
      hsmall, hm72, hm76, hR0, hL0, hsub, haddr]
  have hAmem : sA.mem = s.mem := rfl
  let sB := runBlock (metaReadCode r10 78) E sA
  have hB2 : sB.regs r2 = R + (L - 1) := by simp [sB, metaRead_spec, hA2]
  have hB10 : sB.regs r10 = enc b (1 : F) := by simp [sB, metaRead_spec, hsmall, hAmem, hm78, hUnit]
  let sC := runBlock [iSt r2 r10] E sB
  have hCmem : sC.mem = Function.update s.mem (R + (L - 1)) (enc b 1) := by
    simp [sC, runBlock_cons, runBlock_nil, execInstr, hB2, hB10] <;> rfl
  have hC10 : sC.regs r10 = enc b (1 : F) := by simp [sC, runBlock_cons, runBlock_nil, execInstr, hB10]
  let sD := runBlock (metaReadCode r2 75) E sC
  have hD2 : sD.regs r2 = C := by
    simp [sD, metaRead_spec, hsmall, hCmem, show 75 ≠ R + (L - 1) by omega, hm75, hC0]
  have hD10 : sD.regs r10 = enc b (1 : F) := by simp [sD, metaRead_spec, hC10]
  let sE := runBlock [iSt r2 r10] E sD
  have hEmem : sE.mem = Function.update (Function.update s.mem (R + (L - 1)) (enc b 1)) C (enc b 1) := by
    change Function.update sD.mem (sD.regs r2) (sD.regs r10) = _
    rw [hD2, hD10]
    have hmD : sD.mem = sC.mem := rfl
    rw [hmD, hCmem]
  have hfinish : runBlock initialPolynomialsCode E s = boundaryState (sE.pc + 16) sE.mem := by
    have he : runBlock initialPolynomialsCode E s = runBlock zeroRegsCode E sE := by
      simp only [initialPolynomialsCode, runBlock_append]
      rfl
    rw [he, zeroRegs_spec]
  have hpc : sE.pc + 16 = s.pc + 33 := by
    have hp := runBlock_pc initialPolynomialsCode E s (by
      simp [initialPolynomialsCode, initialRowOffsetCode, metaReadCode, zeroRegsCode])
    rw [hfinish] at hp
    exact hp
  rw [hfinish, hpc, hEmem]

theorem PolynomialStored.zero_to_X_pow {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {m : ℕ → ℕ} {B cap : ℕ}
    (h : PolynomialStored b m B cap 0) (n : ℕ) :
    PolynomialStored b (Function.update m (B + n) (enc b 1)) B cap (Polynomial.X ^ n) := by
  intro j hj
  by_cases he : j = n
  · subst j
    rw [Function.update_self]
    simp
  · rw [Function.update_of_ne (by omega : B + j ≠ B + n)]
    rw [h j hj]
    simp [Polynomial.coeff_X_pow, he, Ne.symm he]

theorem solverInitializationProcedure_spec {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) (P : Program) (E : RAMEnv) (pc : ℕ)
    (e : ℕ → F) (m : ℕ → ℕ) (hAt : At P pc (Stmt.compile solverInitializationProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι)
    (hEnd : decoderAllocEnd t < 2 ^ E.W) (h0 : ι 0 ≠ 0)
    (hh0 : E.det 0 % 2 ^ E.W = t) (hh1 : E.det 1 % 2 ^ E.W = w) (hh2 : E.det 2 % 2 ^ E.W = N)
    (hSaved : FieldArrayStored b m (decoderSavedBase t) (2 * t) e)
    (hTail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → m addr = 0) :
    Sem P E pc (pc + 391) (boundaryState pc m)
      (fun k z => k ≤ 12 * decoderCapacity t + 381 ∧ ∃ m', z = boundaryState (pc + 391) m' ∧
        DecoderMetadata t w N m' ∧
        PadeRows b E (decoderRowBase t 0) (decoderRowBase t 1) (decoderRowBase t 2) (decoderRowBase t 3)
          (decoderLength t) (decoderCapacity t) m' (padeInitial e t) ∧
        RootConstants b (decoderRowBase t 0) (decoderRowBase t 6) (decoderRowBase t 1) (decoderRowBase t 7)
          (decoderRowBase t 4) (decoderRowBase t 5) (decoderCapacity t) (decoderLength t) m' ∧
        FieldArrayStored b m' (decoderSavedBase t) (2 * t) e ∧ MemoryFrame (solverInitWritable t) m m') := by
  let R := decoderRowBase t 0
  let U := decoderRowBase t 1
  let D := decoderRowBase t 2
  let C := decoderRowBase t 3
  let cap := decoderCapacity t
  let L := decoderLength t
  have hl := decoderRows_pade t
  have hcap2 : 2 ≤ cap := decoderCapacity_pos t
  have hindex : 2 * t < cap := by dsimp [cap, decoderCapacity, decoderLength]; omega
  have hmeta : (108 : ℕ) < 2 ^ E.W := by
    have hh := decoderAllocEnd_eq t
    omega
  have hword (j : ℕ) (hj : j < 8) : decoderRowBase t j + cap ≤ 2 ^ E.W := decoderRow_word E t j hj (le_of_lt hEnd)
  have hSourceWord : decoderSavedBase t + cap ≤ 2 ^ E.W := by
    have hDword := hword 2 (by norm_num)
    dsimp [decoderRowBase] at hDword
    omega
  let m1 := decoderMetadataMemory E t m
  let m2 := Function.update m1 78 (enc b 1)
  have hm1 := decoderMetadataMemory_spec E t w N m hh1 hh2
  have hm2 : DecoderMetadata t w N m2 := hm1.of_preserved (by
    intro slot hs
    have hne : slot ≠ 78 := by dsimp [decoderMetadataSlots] at hs; omega
    simp [m2, m1, hne])
  have hf01 := decoderMetadataMemory_frame E t m
  have hf12 : MemoryFrame (fun addr => addr < 128) m1 m2 := MemoryFrame.meta_update m1 78 (enc b 1) (by norm_num)
  have hf02 := MemoryFrame.trans hf01 hf12
  have hSource2 : PolynomialStored b m2 (decoderSavedBase t) cap (syndromePoly e t) :=
    (saved_syndrome_polynomial b t e m hSaved hTail).of_frame hf02 (by intro j hj; dsimp [decoderSavedBase]; omega)
  have hZero2 (j : ℕ) : PolynomialStored b m2 (decoderRowBase t j) cap 0 :=
    (saved_rows_zero b t m hTail j).of_frame hf02 (by intro i hi; exact not_lt_of_ge (le_trans (decoderRow_low t j) (by omega)))
  obtain ⟨hMetaAt, hRestRaw⟩ := At.seqStmt hAt
  have hRestAt : At P (pc + 248)
      (Stmt.compile (.seq (.code cacheUnitCode) (.seq (copyFromSlotsProcedure 74 79) (.code initialPolynomialsCode))) (pc + 248)) := by
    simpa only [Stmt.len, decoderMetadataCode_length] using hRestRaw
  obtain ⟨hUnitAt, hRest2⟩ := At.seqStmt hRestAt
  obtain ⟨hCopyAt, hInitialAt⟩ := At.seqStmt hRest2
  have hMetadata : Sem P E pc (pc + 248) (boundaryState pc m)
      (fun k z => k ≤ 248 ∧ z = boundaryState (pc + 248) m1) := by
    have hrun : runBlock decoderMetadataCode E (boundaryState pc m) = boundaryState (pc + decoderMetadataCode.length) m1 := by
      rw [decoderMetadataCode_length]
      exact decoderMetadataCode_spec E pc t m hEnd hh0
    have hs := Sem.boundary_block P E pc decoderMetadataCode m m1 hMetaAt decoderMetadataCode_noBranch hrun
    simpa only [decoderMetadataCode_length] using hs
  have hUnit : Sem P E (pc + 248) (pc + 288) (boundaryState (pc + 248) m1)
      (fun k z => k ≤ 40 ∧ z = boundaryState (pc + 288) m2) :=
    Sem.boundary_block P E _ cacheUnitCode m1 m2 hUnitAt
      (by simp [cacheUnitCode, metaReadCode, imageZeroCode, fieldInvCode, fieldMulCode, metaStoreCode, zeroRegsCode])
      (cacheUnit_spec b ι t N E _ hw hW hdet h0 hm1.dimension)
  have hCopy := copyFromSlots_spec b P E (pc + 288) 74 79 D (decoderSavedBase t) cap (syndromePoly e t) m2 hCopyAt
    (by omega) (by omega) (by omega) (by omega) (by omega) hl.Dlow (by dsimp [decoderSavedBase]; omega)
    (hword 2 (by norm_num)) hSourceWord (by left; dsimp [D, decoderRowBase]; omega) hSource2 hm2.rowD hm2.saved hm2.capacity
  obtain ⟨_, k3, z3, hRun3, hPc3, hCost3, m3, hz3, hD3, hf23raw⟩ := hCopy
  have hm3 : DecoderMetadata t w N m3 := hm2.of_preserved (by
    intro slot hs
    apply root_copy_meta hf23raw hl.Dlow
    · dsimp [decoderMetadataSlots] at hs; omega
    · dsimp [decoderMetadataSlots] at hs; omega)
  have hunit3 : m3 78 = enc b (1 : F) :=
    (root_copy_meta hf23raw hl.Dlow (by norm_num) (by norm_num)).trans (by simp [m2])
  have hR3 : PolynomialStored b m3 R cap 0 :=
    (hZero2 0).after_root_copy hl.Rlow (hl.RD.elim Or.inr Or.inl) hf23raw
  have hU3 : PolynomialStored b m3 U cap 0 :=
    (hZero2 1).after_root_copy hl.Ulow (hl.UD.elim Or.inr Or.inl) hf23raw
  have hC3 : PolynomialStored b m3 C cap 0 := (hZero2 3).after_root_copy hl.Clow hl.DC hf23raw
  let mR := Function.update m3 (R + 2 * t) (enc b 1)
  let m4 := Function.update mR C (enc b 1)
  have hPointFrame : MemoryFrame (fun addr => addr = R + 2 * t ∨ addr = C) m3 m4 :=
    MemoryFrame.trans (MemoryFrame.update_allowed _ m3 (R + 2 * t) _ (Or.inl rfl))
      (MemoryFrame.update_allowed _ _ C _ (Or.inr rfl))
  have hm4 : DecoderMetadata t w N m4 := hm3.of_preserved (by
    intro slot hs
    have hslt : slot < 128 := by dsimp [decoderMetadataSlots] at hs; omega
    apply hPointFrame
    change ¬ (slot = R + 2 * t ∨ slot = C)
    have hRlo := hl.Rlow
    have hClo := hl.Clow
    omega)
  have hunit4 : m4 78 = enc b (1 : F) := by
    have hRlo := hl.Rlow
    have hClo := hl.Clow
    simpa [m4, mR, show 78 ≠ C by omega, show 78 ≠ R + 2 * t by omega] using hunit3
  have hR4 : PolynomialStored b m4 R cap (Polynomial.X ^ (2 * t)) :=
    (hR3.zero_to_X_pow (2 * t)).of_frame (MemoryFrame.update _ C (enc b 1)) (by
      intro j hj
      have hsep := hl.RC
      change R + j ≠ C
      omega)
  have hU4 : PolynomialStored b m4 U cap 0 := hU3.of_frame hPointFrame (by
    intro j hj
    have hRsep := hl.RU
    have hCsep := hl.UC
    change ¬ (U + j = R + 2 * t ∨ U + j = C)
    omega)
  have hD4 : PolynomialStored b m4 D cap (syndromePoly e t) := hD3.of_frame hPointFrame (by
    intro j hj
    have hRsep := hl.RD
    have hCsep := hl.DC
    change ¬ (D + j = R + 2 * t ∨ D + j = C)
    omega)
  have hCzeroR : PolynomialStored b mR C cap 0 := hC3.of_frame (MemoryFrame.update _ (R + 2 * t) (enc b 1)) (by
    intro j hj
    have hsep := hl.RC
    change C + j ≠ R + 2 * t
    omega)
  have hC4 : PolynomialStored b m4 C cap 1 := by
    simpa only [Nat.add_zero, pow_zero] using hCzeroR.zero_to_X_pow 0
  have hf23 : MemoryFrame (solverInitWritable t) m2 m3 := hf23raw.mono (by
    intro addr ha
    dsimp [copyFromSlotsWritable] at ha
    dsimp [solverInitWritable, D, decoderRowBase, cap] at ha ⊢
    omega)
  have hf34 : MemoryFrame (solverInitWritable t) m3 m4 := hPointFrame.mono (by
    intro addr ha
    dsimp [solverInitWritable, R, C, decoderRowBase, cap] at ha ⊢
    dsimp only [cap] at hindex
    omega)
  have hf04 : MemoryFrame (solverInitWritable t) m m4 :=
    MemoryFrame.trans (MemoryFrame.trans (hf02.mono (fun _ ha => Or.inl ha)) hf23) hf34
  have hSaved4 : FieldArrayStored b m4 (decoderSavedBase t) (2 * t) e := hSaved.of_frame hf04 (by
    intro j hj
    dsimp [solverInitWritable, decoderRowBase, decoderSavedBase]
    omega)
  have hZero4 : PolynomialStored b m4 (decoderRowBase t 5) cap 0 := (saved_rows_zero b t m hTail 5).of_frame hf04 (by
    intro j hj
    dsimp [solverInitWritable, decoderRowBase, decoderSavedBase]
    have hc := decoderCapacity_pos t
    omega)
  have hRows4 : PadeRows b E R U D C L cap m4 (padeInitial e t) :=
    ⟨hl, hword 0 (by norm_num), hword 1 (by norm_num), hword 2 (by norm_num), hword 3 (by norm_num),
      hR4, hU4, hD4, hC4, hm4.rowR, hm4.rowU, hm4.rowD, hm4.rowC, hm4.length, hm4.dimension, hm4.capacity⟩
  have hRoot4 : RootConstants b R (decoderRowBase t 6) U (decoderRowBase t 7) (decoderRowBase t 4) (decoderRowBase t 5) cap L m4 :=
    ⟨hm4.length, hm4.dimension, hunit4, hm4.capacity, hm4.fixedR, hm4.fixedD, hm4.fixedU, hm4.fixedC, hm4.fixedT, hm4.fixedZ, hZero4⟩
  have hCopyExact : Sem P E (pc + 288) (pc + 358) (boundaryState (pc + 288) m2)
      (fun k z => k ≤ 12 * cap + 60 ∧ z = boundaryState (pc + 358) m3) :=
    ⟨rfl, k3, z3, hRun3, hPc3, hCost3, hz3⟩
  have hInitial : Sem P E (pc + 358) (pc + 391) (boundaryState (pc + 358) m3)
      (fun k z => k ≤ 33 ∧ z = boundaryState (pc + 391) m4) :=
    Sem.boundary_block P E _ initialPolynomialsCode m3 m4 hInitialAt
      (by simp [initialPolynomialsCode, initialRowOffsetCode, metaReadCode, zeroRegsCode])
      (by
        have hp := initialPolynomials_spec b E (boundaryState (pc + 358) m3) R C L (by omega) (by omega) hl.Rlow
          (by have hh := hword 3 (by norm_num); omega) (by dsimp [L, decoderLength]; omega)
          (by have hh := hword 0 (by norm_num); dsimp [cap, decoderCapacity] at hh; omega)
          (by have hh := hword 0 (by norm_num); dsimp [cap, decoderCapacity] at hh; omega)
          hm3.rowR hm3.rowC hm3.length hunit3
        simpa [L, decoderLength, m4, mR, boundaryState, initialPolynomialsCode_length] using hp)
  have hFull := Sem.seq_bound hMetadata (fun z _ hz => by
    subst z
    exact Sem.seq_bound hUnit (fun z _ hz => by
      subst z
      exact Sem.seq_bound hCopyExact (fun z _ hz => by subst z; exact hInitial)))
  exact Sem.mono hFull (fun k z hQ => ⟨by omega, m4, hQ.2, hm4, hRows4, hRoot4, hSaved4, hf04⟩)

theorem solverInitializationProcedure_length : solverInitializationProcedure.len = 391 := by
  simp only [solverInitializationProcedure, Stmt.len, decoderMetadataCode_length, initialPolynomialsCode_length] <;> rfl

theorem pade_write_le_solver_init (t addr : ℕ)
    (ha : padeLoopWritable (decoderRowBase t 0) (decoderRowBase t 1) (decoderRowBase t 2) (decoderRowBase t 3) (decoderCapacity t) addr) :
    solverInitWritable t addr := by
  dsimp [padeLoopWritable, padeWritable, decoderRowBase] at ha
  dsimp [solverInitWritable, decoderRowBase]
  omega

theorem solver_saved_readonly (t j : ℕ) (hj : j < 2 * t) : ¬ solverInitWritable t (decoderSavedBase t + j) := by
  dsimp [solverInitWritable, decoderRowBase, decoderSavedBase]
  omega

theorem solver_zero_readonly (t j : ℕ) : ¬ solverInitWritable t (decoderRowBase t 5 + j) := by
  dsimp [solverInitWritable, decoderRowBase, decoderSavedBase]
  have hc := decoderCapacity_pos t
  omega

theorem pade_preserved_meta {t : ℕ} {m m' : ℕ → ℕ}
    (hf : MemoryFrame (padeLoopWritable (decoderRowBase t 0) (decoderRowBase t 1) (decoderRowBase t 2) (decoderRowBase t 3) (decoderCapacity t)) m m')
    (slot : ℕ) (hlo : 76 ≤ slot) (hhi : slot < 128) (h94 : slot ≠ 94) (h95 : slot ≠ 95) : m' slot = m slot := by
  apply hf
  have hR := decoderRow_low t 0
  have hU := decoderRow_low t 1
  have hD := decoderRow_low t 2
  have hC := decoderRow_low t 3
  dsimp [padeLoopWritable, padeWritable]
  omega

theorem RootConstants.after_pade {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {t : ℕ} {m m' : ℕ → ℕ}
    (h : RootConstants b (decoderRowBase t 0) (decoderRowBase t 6) (decoderRowBase t 1) (decoderRowBase t 7)
      (decoderRowBase t 4) (decoderRowBase t 5) (decoderCapacity t) (decoderLength t) m)
    (hf : MemoryFrame (padeLoopWritable (decoderRowBase t 0) (decoderRowBase t 1) (decoderRowBase t 2) (decoderRowBase t 3) (decoderCapacity t)) m m') :
    RootConstants b (decoderRowBase t 0) (decoderRowBase t 6) (decoderRowBase t 1) (decoderRowBase t 7)
      (decoderRowBase t 4) (decoderRowBase t 5) (decoderCapacity t) (decoderLength t) m' := by
  have hm (slot : ℕ) (hs : 76 ≤ slot) (hh : slot < 128) (h94 : slot ≠ 94) (h95 : slot ≠ 95) := pade_preserved_meta hf slot hs hh h94 h95
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.zero.of_frame (hf.mono (pade_write_le_solver_init t)) (by intro j hj; exact solver_zero_readonly t j)⟩
  · exact (hm 76 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans h.length
  · exact (hm 77 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans h.dimension
  · exact (hm 78 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans h.unit
  · exact (hm 81 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans h.capacity
  · exact (hm 102 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans h.fixedR
  · exact (hm 103 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans h.fixedD
  · exact (hm 104 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans h.fixedU
  · exact (hm 105 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans h.fixedC
  · exact (hm 106 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans h.fixedT
  · exact (hm 108 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans h.fixedZ

section PinBits

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end PinBits

section Uniqueness

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

end Uniqueness

section Slp

variable {F : Type} [Field F]

end Slp


open LinearSetReconciliation327.Main in
theorem LinearSetReconciliation327.Main.pinsketch_decoder_key_solver
    {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) (P : Program) (E : RAMEnv) (pc : ℕ)
    (e : ℕ → F) (m : ℕ → ℕ) (hAt : At P pc (Stmt.compile keySolverProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : DetAgrees E t N b ι) (ht : 1 ≤ t)
    (hEnd : decoderAllocEnd t < 2 ^ E.W) (h0 : ι 0 ≠ 0)
    (hh0 : E.det 0 % 2 ^ E.W = t) (hh1 : E.det 1 % 2 ^ E.W = w) (hh2 : E.det 2 % 2 ^ E.W = N)
    (hSaved : FieldArrayStored b m (decoderSavedBase t) (2 * t) e)
    (hTail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → m addr = 0) :
    Sem P E pc (pc + 960) (boundaryState pc m)
      (fun k z => k ≤ (34 * decoderCapacity t + (48 * decoderLength t + 187) * decoderLength t + 289) * decoderLength t +
          12 * decoderCapacity t + 385 ∧ ∃ m', z = boundaryState (pc + 960) m' ∧
        KeyReady b E t N e m' ∧
        MemoryFrame (solverInitWritable t) m m') := by
  obtain ⟨hInitAt, hPadeRaw⟩ := At.seqStmt hAt
  have hPadeAt : At P (pc + 391) (Stmt.compile padeSolveProcedure (pc + 391)) := by
    simpa only [solverInitializationProcedure_length] using hPadeRaw
  have hInit := solverInitializationProcedure_spec b ι t N P E pc e m hInitAt hw hW hdet hEnd h0 hh0 hh1 hh2 hSaved hTail
  obtain ⟨_, k1, z1, hRun1, hPc1, hCost1, m1, hz1, hm1, hRows1, hRoot1, hSaved1, hf01⟩ := hInit
  have hInitExact : Sem P E pc (pc + 391) (boundaryState pc m)
      (fun k z => k ≤ 12 * decoderCapacity t + 381 ∧ z = boundaryState (pc + 391) m1) :=
    ⟨rfl, k1, z1, hRun1, hPc1, hCost1, hz1⟩
  have hPade := padeSolveProcedure_minimal_strong b ι t N P E (pc + 391)
    (decoderRowBase t 0) (decoderRowBase t 1) (decoderRowBase t 2) (decoderRowBase t 3)
    (decoderLength t) (decoderCapacity t) e m1 hPadeAt hw hW hdet ht rfl rfl hRows1 hm1.capacityParameter hm1.padeCounter
  have hFull := Sem.seq_bound hInitExact (fun z _ hz => by subst z; exact hPade)
  refine Sem.mono hFull ?_
  intro k z hQ
  obtain ⟨hk, m2, R', U', D', C', hz2, hRows2, hmin, hf12, hfoot⟩ := hQ
  have hRoot2 := hRoot1.after_pade hf12
  have hSaved2 := hSaved1.of_frame (hf12.mono (pade_write_le_solver_init t)) (solver_saved_readonly t)
  have hm (slot : ℕ) (hs : 76 ≤ slot) (hh : slot < 128) (h94 : slot ≠ 94) (h95 : slot ≠ 95) := pade_preserved_meta hf12 slot hs hh h94 h95
  have hrange : ∀ j < decoderCapacity t, padeWritable (decoderRowBase t 0) (decoderRowBase t 1)
      (decoderRowBase t 2) (decoderRowBase t 3) (decoderCapacity t) (C' + j) := by
    intro j hj
    apply (hfoot (C' + j)).mp
    dsimp [padeWritable]
    omega
  have hdisj := (decoderQueue0_pade_separated t).gcd_output_disjoint (decoderRow_low t 8) (by have h := decoderCapacity_pos t; omega) ht hrange
  have hReady : KeyReady b E t N e m2 := by
    refine ⟨hRoot2, hSaved2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, C', hRows2.ptr75, hRows2.layout.Clow, hRows2.Cword, hRows2.curC, hdisj⟩
    · exact (hm 79 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.saved
    · exact (hm 80 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.capacityParameter
    · exact (hm 82 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.universeSize
    · exact (hm 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.firstQueue
    · exact (hm 85 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.output
    · exact (hm 86 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.verification
    · exact (hm 107 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans hm1.fixedQ1
  exact ⟨by omega, m2, hz2, hReady, MemoryFrame.trans hf01 (hf12.mono (pade_write_le_solver_init t))⟩
end LinearSetReconciliation327.Main


