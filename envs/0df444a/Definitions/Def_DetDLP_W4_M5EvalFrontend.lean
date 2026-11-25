-- Prove2me | Definitions.Def_DetDLP_W4_M5EvalFrontend
-- name    : DetDLP_W4_M5EvalFrontend
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:33:57.591247+00:00
-- url     : https://prove2.me/theorems/e6c2d74e-4f27-4b53-ae7b-ea01545ebbc0
-- title:
--   Polynomial-time multiplication query parser and budget
-- statement:
--   Proves polynomial time for the frame parser, binary parameter arithmetic and leaf classification, and supplies a unary iteration budget from the quadratic clamp.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Definitions.Def_DetDLP_W4_M5EvalSpec
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_pow_const
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_PolyT_unary_min_length

set_option autoImplicit false
namespace DetDLP.w4_M5Evaluator
open Groundwork Groundwork.PolyT
open w4_MulParams w4_M5GraphBounds

attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.mod
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.pow_const
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] Groundwork.PolyT.testBit
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_log2__935ea318e2e8
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45
theorem scanStep_poly : PolyT (fun p : ScanState × Bool => scanStep p.1 p.2) := by
  unfold scanStep; fun_prop

theorem splitFrame_poly : PolyT splitFrame := by
  have hfold : PolyT (fun xs : List Bool => xs.foldl scanStep (0,[],[])) := by
    apply Groundwork.PolyT.foldl_add (g := fun _ => scanStep) (hl := (by fun_prop)) (ha := (by fun_prop)) (Groundwork.PolyT.comp scanStep_poly (by fun_prop))
    refine ⟨fun _ => 20, PB.const 20, ?_⟩
    intro xs st b hb
    rcases st with ⟨q,p,r⟩
    have h0 : len (0:ℕ) = 2 := rfl
    have h1 : len (1:ℕ) = 5 := rfl
    have h3 : len (3:ℕ) = 8 := rfl
    by_cases hq : q = 0
    · cases b <;> simp [scanStep,hq,len_pair,h0,h1,h3] <;> omega
    · by_cases hq' : q = 1 <;> simp [scanStep,hq,hq',len_pair,len_cons,len_bool,h0,h1,h3] <;> omega
  exact Groundwork.PolyT.comp (f := fun s : ScanState => (s.2.1.reverse,s.2.2.reverse)) (by fun_prop) hfold

@[local fun_prop] theorem splitFrame_comp {α} [Enc α] {g : α → List Bool} (hg : PolyT g) :
    PolyT (fun x => splitFrame (g x)) := Groundwork.PolyT.comp splitFrame_poly hg

set_option maxHeartbeats 1000000 in
theorem firstThree_poly : PolyT firstThree := by
  let s := fun x : List Bool => splitFrame (x.drop 1)
  let t := fun x : List Bool => splitFrame ((s x).2.drop 1)
  let u := fun x : List Bool => splitFrame ((t x).2.drop 1)
  have hs : PolyT s := splitFrame_comp (Groundwork.PolyT.drop (const 1) P2M_Groundwork_PolyT_id__1c5d0f44cc8f)
  have ht : PolyT t := splitFrame_comp (Groundwork.PolyT.drop (const 1) (Groundwork.PolyT.snd hs))
  have hu : PolyT u := splitFrame_comp (Groundwork.PolyT.drop (const 1) (Groundwork.PolyT.snd ht))
  have hp := Groundwork.PolyT.prodMk (Groundwork.PolyT.fst hs) (Groundwork.PolyT.prodMk (Groundwork.PolyT.fst ht) (Groundwork.PolyT.fst hu))
  apply hp.congr
  intro x
  simp only [firstThree, s, t, u]

private theorem clog2_size (n : ℕ) : Nat.clog 2 n = Nat.size (n-1) := by
  apply le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by decide)).2
    have := Nat.lt_size_self (n-1); omega
  · apply Nat.size_le.mpr
    have := Nat.le_pow_clog (by decide : 1 < 2) n
    have : 0 < 2 ^ Nat.clog 2 n := by positivity
    omega

@[local fun_prop] theorem clog2_poly {α} [Enc α] {g : α → ℕ} (hg : PolyT g) :
    PolyT (fun x => Nat.clog 2 (g x)) := by simp only [clog2_size]; fun_prop

private theorem unary_bounded {α} [Enc α] {g : α → ℕ} {l : α → List Bool}
    (hg : PolyT g) (hl : PolyT l) (hb : ∀ x, g x ≤ (l x).length) : Unary g :=
  (unary_min_length hg hl).congr fun x => by simp [min_eq_left (hb x)]

private theorem unary_clog2_bound {α} [Enc α] {g h : α → ℕ} (hg : PolyT g) (hh : PolyT h)
    (hb : ∀ x, g x ≤ Nat.clog 2 (h x)) : Unary g := by
  apply unary_bounded hg (bits hh)
  intro x
  rw [Nat.size_eq_bits_len]
  exact (hb x).trans (by rw [clog2_size]; exact Nat.size_le_size (Nat.sub_le ..))

@[local fun_prop] theorem j_poly {α} [Enc α] {g : α → ℕ} (hg : PolyT g) :
    PolyT (fun x => j (g x)) := by
  have eq (n : ℕ) : j n = (Nat.clog 2 (64 * (n+1)) + 1) / 2 := Nat.clog_pow_left 2 2 _
  simp only [eq]; fun_prop

@[local fun_prop] theorem J_poly {α} [Enc α] {g : α → ℕ} (hg : PolyT g) :
    PolyT (fun x => J (g x)) := by
  apply pow_unary (b := fun _ => 2) (const 2)
  apply unary_clog2_bound (j_poly hg) (h := fun x => 64 * (g x+1)) (by fun_prop)
  intro x; exact Nat.clog_anti_left (by decide) (by decide : 2 ≤ 4)

@[local fun_prop] theorem n0_poly {α} [Enc α] {g : α → ℕ} (hg : PolyT g) :
    PolyT (fun x => n0 (g x)) := by unfold n0 k; fun_prop

@[local fun_prop] theorem mu_poly {α} [Enc α] {g : α → ℕ} (hg : PolyT g) :
    PolyT (fun x => μ (g x)) := by unfold μ; fun_prop

@[local fun_prop] theorem L1_poly {α} [Enc α] {g : α → ℕ} (hg : PolyT g) :
    PolyT (fun x => L1 (g x)) := by
  apply pow_unary (b := fun _ => 2) (const 2)
  apply unary_clog2_bound (g := fun x => μ (g x) / 2) (by fun_prop) (h := fun x => 2 * n0 (g x)) (by fun_prop)
  intro x; exact Nat.div_le_self ..

@[local fun_prop] theorem L2_poly {α} [Enc α] {g : α → ℕ} (hg : PolyT g) :
    PolyT (fun x => L2 (g x)) := by
  apply pow_unary (b := fun _ => 2) (const 2)
  apply unary_clog2_bound (g := fun x => (μ (g x)+1) / 2) (by fun_prop) (h := fun x => 2 * n0 (g x)) (by fun_prop)
  intro x; change (μ (g x)+1)/2 ≤ μ (g x); omega

@[local fun_prop] theorem vertexCount_poly {α} [Enc α] {g : α → ℕ} (hg : PolyT g) :
    PolyT (fun x => vertexCount (g x)) := by unfold vertexCount; fun_prop

@[local fun_prop] theorem leafIndex_poly {α} [Enc α] {d v : α → ℕ} (hd : PolyT d) (hv : PolyT v) :
    PolyT (fun x => leafIndex (d x) (v x)) := by unfold leafIndex; fun_prop

private theorem unary_mul {α} [Enc α] {g h : α → ℕ} (hg : Unary g) (hh : Unary h) :
    Unary (fun x => g x * h x) := by
  have H : PolyT (fun x => (List.replicate (g x) ()).flatMap (fun _ => List.replicate (h x) ())) :=
    Groundwork.PolyT.flatMap (Groundwork.PolyT.comp (g := fun p : α × Unit => p.1) hh (by fun_prop)) hg
  apply H.congr; intro x
  change _ = List.replicate (g x * h x) ()
  generalize g x = n
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.flatMap_cons, ih, Nat.succ_mul]
    rw [← List.replicate_add, Nat.add_comm]

private theorem unary_budget : Unary (fun x : List Bool => 4096 * (x.length+1)^2) := by
  have H : Unary (fun x : List Bool => x.length+1) := by
    have h : PolyT (fun x : List Bool => (true::x).map (fun _ => ())) := by fun_prop
    apply h.congr; intro x; simp [List.replicate_succ]
  have C : Unary (fun _ : List Bool => 4096) := const _
  simpa only [pow_two] using unary_mul C (unary_mul H H)

theorem unary_clamp {d : List Bool → ℕ} (hd : PolyT d) :
    Unary (fun xs => min (d xs) (4096*(xs.length+1)^2)) := by
  have h := unary_min_length hd unary_budget
  simpa only [List.length_replicate] using h

theorem query_components : PolyT (fun xs => (decodeNat (firstThree xs).1, decodeNat (firstThree xs).2.1, (firstThree xs).2.2)) := by
  exact Groundwork.PolyT.prodMk (ofBits (Groundwork.PolyT.fst firstThree_poly))
    (Groundwork.PolyT.prodMk (ofBits (Groundwork.PolyT.fst (Groundwork.PolyT.snd firstThree_poly)))
      (Groundwork.PolyT.snd (Groundwork.PolyT.snd firstThree_poly)))

attribute [local irreducible] evalAt firstThree splitFrame vertexCount leafIndex
set_option maxHeartbeats 2500000 in
theorem f_poly_of_evalAt
    (hgate : ∀ {α : Type} [Enc α] {d v : α → ℕ} {a : α → List Bool},
      Unary d → PolyT d → PolyT v → PolyT a → PolyT (fun x => evalAt (d x) (v x) (a x))) : PolyT f := by
  let d := fun xs => decodeNat (firstThree xs).1
  let v := fun xs => decodeNat (firstThree xs).2.1
  let a := fun xs => (firstThree xs).2.2
  have hd : PolyT d := Groundwork.PolyT.fst (f := fun xs => (decodeNat (firstThree xs).1, decodeNat (firstThree xs).2.1, (firstThree xs).2.2)) query_components
  have hv : PolyT v := Groundwork.PolyT.fst (Groundwork.PolyT.snd query_components)
  have ha : PolyT a := Groundwork.PolyT.snd (Groundwork.PolyT.snd firstThree_poly)
  let D := fun xs : List Bool => min (d xs) (4096 * (xs.length+1)^2)
  have hD : PolyT D := by dsimp only [D]; fun_prop
  have he := hgate (unary_clamp hd) hD hv ha
  change PolyT (fun xs => if leafIndex (d xs) (v xs) then [true] else [evalAt (D xs) (v xs) (a xs)])
  have hl := leafIndex_poly hd hv
  apply Groundwork.PolyT.ite' (c := fun xs => leafIndex (d xs) (v xs) = true)
  · simpa using hl
  · exact const _
  · exact P2M_Groundwork_PolyT_cons__3a60f43a3b86 he (const [])

end DetDLP.w4_M5Evaluator


