-- Prove2me | Definitions.Def_QMCSub_Poly
-- name    : QMCSub_Poly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:16:34.231477+00:00
-- url     : https://prove2.me/theorems/86f3e393-7aed-46fe-99fa-177404c838f6
-- title:
--   The Max-Cut SDP subgradient program is polynomial-time
-- statement:
--   Every component of the list program is polynomial-time in the finite Boolean-machine runtime: the rounding and guard primitives, the guarded matrix multiplication, both loops (via the size-bounded fold principle), the preprocessing of the edge list, and the final value. In particular the solver, as a function of the raw request bits, is polynomial-time.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QMCSub_Fold
import Definitions.Def_QMCSub_Prog

/-!
The list-level program is polynomial-time in the runtime's `Poly` framework.
-/

namespace QMCSub
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime
open Polynomial

/-! ### Primitive programs as `Poly` facts -/

section prims
variable {α : Type} [Coding α]

@[fun_prop] theorem ratNum_poly : Poly Rat.num := ⟨PolyProgram.ratNum⟩
@[fun_prop] theorem ratDen_poly : Poly Rat.den := ⟨PolyProgram.ratDen⟩
@[fun_prop] theorem intNatAbs_poly : Poly Int.natAbs := ⟨PolyProgram.intAbs⟩
@[fun_prop] theorem natSize_poly : Poly Nat.size := ⟨PolyProgram.natSize⟩
@[fun_prop] theorem natDiv_poly : Poly (fun x : ℕ × ℕ => x.1 / x.2) := ⟨PolyProgram.natDiv⟩

@[fun_prop] theorem qfloor_poly : Poly qfloor := by
  unfold qfloor
  fun_prop

@[fun_prop] theorem fitsQ_poly : Poly (fun x : ℕ × ℚ => fitsQ x.1 x.2) := by
  unfold fitsQ
  fun_prop

@[fun_prop] theorem fitsQ_poly_comp {m : α → ℕ} {q : α → ℚ} (hm : Poly m) (hq : Poly q) :
    Poly (fun x => fitsQ (m x) (q x)) := Poly.comp (f := fun x : ℕ × ℚ => fitsQ x.1 x.2) (g := fun x => (m x, q x))
    fitsQ_poly (Poly.pair hm hq)

@[fun_prop] theorem capQ_poly : Poly (fun x : List Unit × ℚ => capQ x.1 x.2) := by
  unfold capQ
  fun_prop

@[fun_prop] theorem capQ_poly_comp {p : α → List Unit} {q : α → ℚ} (hp : Poly p) (hq : Poly q) :
    Poly (fun x => capQ (p x) (q x)) := Poly.comp (f := fun x : List Unit × ℚ => capQ x.1 x.2) (g := fun x => (p x, q x))
    capQ_poly (Poly.pair hp hq)

@[fun_prop] theorem gv_poly : Poly (fun x : Vec × ℕ => gv x.1 x.2) := by
  unfold gv
  fun_prop

@[fun_prop] theorem gv_poly_comp {v : α → Vec} {i : α → ℕ} (hv : Poly v) (hi : Poly i) :
    Poly (fun x => gv (v x) (i x)) := Poly.comp (f := fun x : Vec × ℕ => gv x.1 x.2) (g := fun x => (v x, i x))
    gv_poly (Poly.pair hv hi)

theorem gm_poly : Poly (fun x : Mat × ℕ × ℕ => gm x.1 x.2.1 x.2.2) := by
  unfold gm
  fun_prop

@[fun_prop] theorem gm_poly_comp {A : α → Mat} {i j : α → ℕ}
    (hA : Poly A) (hi : Poly i) (hj : Poly j) :
    Poly (fun x => gm (A x) (i x) (j x)) := Poly.comp (f := fun x : Mat × ℕ × ℕ => gm x.1 x.2.1 x.2.2) (g := fun x => (A x, i x, j x))
    gm_poly (Poly.pair hA (Poly.pair hi hj))

@[fun_prop] theorem idMat_poly : Poly idMat := by
  unfold idMat
  fun_prop

end prims

/-! ### Size bounds for guarded values -/

theorem enc_capQ_le (pad : List Unit) (q : ℚ) :
    (enc (capQ pad q)).length ≤ 8 + 3 * pad.length := by
  change (Ratio.encode (capQ pad q)).length ≤ _
  rw [Ratio.encode_length, Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  unfold capQ
  split_ifs with h
  · unfold fitsQ at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  · simp

theorem encodeList_map_le {β γ : Type} (ea : γ → List Bool) (f : β → γ) (B : ℕ)
    (h : ∀ b, (ea (f b)).length ≤ B) (l : List β) :
    (encodeList ea (l.map f)).length ≤ l.length * (2 * B + 1) := by
  induction l with
  | nil => simp [encodeList]
  | cons a l ih =>
      rw [List.map_cons, EncodedList.cons_length, List.length_cons, Nat.add_mul, Nat.one_mul]
      have := h a
      omega

theorem length_fst_le_enc {β γ : Type} [Coding β] [Coding γ] (s : List β × γ) :
    s.1.length ≤ (enc s).length := by
  change _ ≤ (encodePair enc enc s).length
  rw [encodePair_length]
  have := EncodedList.length_le (enc : β → List Bool) s.1
  change s.1.length ≤ (enc s.1).length at this
  omega

theorem enc_snd_le_enc {β γ : Type} [Coding β] [Coding γ] (s : β × γ) :
    (enc s.2).length ≤ (enc s).length := by
  change _ ≤ (encodePair enc enc s).length
  rw [encodePair_length]
  omega

theorem length_le_enc {β : Type} [Coding β] (l : List β) : l.length ≤ (enc l).length :=
  EncodedList.length_le (enc : β → List Bool) l

/-! ### The inner loop -/

@[fun_prop] theorem innerStep_poly : Poly (fun x : SI × Mat => innerStep x.1 x.2) := by
  unfold innerStep
  fun_prop

/-- Size polynomial for the inner step. -/
noncomputable def innerQ : Polynomial ℕ := X * (2 * (X * (2 * (8 + 3 * X) + 1)) + 1)

theorem innerStep_size (s : SI) (P : Mat) :
    (enc (innerStep s P)).length ≤ innerQ.eval (enc s).length := by
  have hn : s.1.length ≤ (enc s).length := length_fst_le_enc s
  have hp : s.2.2.length ≤ (enc s).length :=
    (length_le_enc s.2.2).trans ((enc_snd_le_enc s.2).trans (enc_snd_le_enc s))
  have h1 : ∀ i : ℕ, (enc (s.1.map (fun j =>
      capQ s.2.2 ((s.1.map (fun k => gm P i k * gm s.2.1 k j)).sum)))).length ≤
      s.1.length * (2 * (8 + 3 * s.2.2.length) + 1) := fun i =>
    encodeList_map_le enc _ _ (fun j => enc_capQ_le _ _) _
  have h2 : (enc (innerStep s P)).length ≤
      s.1.length * (2 * (s.1.length * (2 * (8 + 3 * s.2.2.length) + 1)) + 1) :=
    encodeList_map_le enc _ _ h1 _
  refine h2.trans ?_
  simp only [innerQ, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]
  gcongr

theorem innerFold_poly : Poly (fun x : List Unit × (SI × Mat) => gfold innerStep x.1 x.2) :=
  poly_gfold innerStep innerStep_poly innerQ innerStep_size

section mats
variable {α : Type} [Coding α]

theorem matPow_poly :
    Poly (fun x : List ℕ × Mat × List Unit × List Unit => matPow x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have h1 : Poly (fun x : List ℕ × Mat × List Unit × List Unit =>
      (x.2.2.2, ((x.1, x.2.1, x.2.2.1), idMat x.1))) := by fun_prop
  exact Poly.comp Poly.snd (Poly.comp innerFold_poly h1)

@[fun_prop] theorem matPow_poly_comp {idx : α → List ℕ} {M : α → Mat} {pad fuel : α → List Unit}
    (hi : Poly idx) (hM : Poly M) (hp : Poly pad) (hf : Poly fuel) :
    Poly (fun x => matPow (idx x) (M x) (pad x) (fuel x)) :=
  Poly.comp (f := fun x : List ℕ × Mat × List Unit × List Unit => matPow x.1 x.2.1 x.2.2.1 x.2.2.2)
    (g := fun x => (idx x, M x, pad x, fuel x)) matPow_poly
    (Poly.pair hi (Poly.pair hM (Poly.pair hp hf)))

theorem shiftMat_poly :
    Poly (fun x : List ℕ × Mat × ℚ × Vec => shiftMat x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold shiftMat
  fun_prop

@[fun_prop] theorem shiftMat_poly_comp {idx : α → List ℕ} {lap : α → Mat} {sig : α → ℚ}
    {u : α → Vec} (hi : Poly idx) (hl : Poly lap) (hs : Poly sig) (hu : Poly u) :
    Poly (fun x => shiftMat (idx x) (lap x) (sig x) (u x)) :=
  Poly.comp (f := fun x : List ℕ × Mat × ℚ × Vec => shiftMat x.1 x.2.1 x.2.2.1 x.2.2.2)
    (g := fun x => (idx x, lap x, sig x, u x)) shiftMat_poly
    (Poly.pair hi (Poly.pair hl (Poly.pair hs hu)))

theorem diagSum_poly : Poly (fun x : List ℕ × Mat => diagSum x.1 x.2) := by
  unfold diagSum
  fun_prop

@[fun_prop] theorem diagSum_poly_comp {idx : α → List ℕ} {Q : α → Mat}
    (hi : Poly idx) (hQ : Poly Q) : Poly (fun x => diagSum (idx x) (Q x)) :=
  Poly.comp (f := fun x : List ℕ × Mat => diagSum x.1 x.2) (g := fun x => (idx x, Q x))
    diagSum_poly (Poly.pair hi hQ)

theorem lapDot_poly : Poly (fun x : List ℕ × Mat × Mat => lapDot x.1 x.2.1 x.2.2) := by
  unfold lapDot
  fun_prop

@[fun_prop] theorem lapDot_poly_comp {idx : α → List ℕ} {lap Q : α → Mat}
    (hi : Poly idx) (hl : Poly lap) (hQ : Poly Q) :
    Poly (fun x => lapDot (idx x) (lap x) (Q x)) :=
  Poly.comp (f := fun x : List ℕ × Mat × Mat => lapDot x.1 x.2.1 x.2.2)
    (g := fun x => (idx x, lap x, Q x)) lapDot_poly (Poly.pair hi (Poly.pair hl hQ))

theorem powQ_poly : Poly (fun x : SO × Vec => powQ x.1 x.2) := by
  unfold powQ
  fun_prop

@[fun_prop] theorem powQ_poly_comp {s : α → SO} {u : α → Vec}
    (hs : Poly s) (hu : Poly u) : Poly (fun x => powQ (s x) (u x)) :=
  Poly.comp (f := fun x : SO × Vec => powQ x.1 x.2) (g := fun x => (s x, u x))
    powQ_poly (Poly.pair hs hu)

end mats

/-! ### The outer loop -/

theorem outerStep_poly : Poly (fun x : SO × (Vec × ℚ) => outerStep x.1 x.2) := by
  unfold outerStep
  fun_prop

/-- Size polynomial for the outer step. -/
noncomputable def outerQ : Polynomial ℕ := 2 * (X * (2 * (8 + 3 * X) + 1)) + 1 + (8 + 3 * X)

theorem outerStep_size (s : SO) (d : Vec × ℚ) :
    (enc (outerStep s d)).length ≤ outerQ.eval (enc s).length := by
  have hn : s.1.length ≤ (enc s).length := length_fst_le_enc s
  have hp : s.2.2.2.2.1.length ≤ (enc s).length :=
    (length_fst_le_enc s.2.2.2.2).trans ((enc_snd_le_enc s.2.2.2).trans
      ((enc_snd_le_enc s.2.2).trans ((enc_snd_le_enc s.2).trans (enc_snd_le_enc s))))
  have h1 : (enc (outerStep s d).1).length ≤
      s.1.length * (2 * (8 + 3 * s.2.2.2.2.1.length) + 1) :=
    encodeList_map_le enc _ _ (fun i => enc_capQ_le _ _) _
  have h2 : (enc (outerStep s d).2).length ≤ 8 + 3 * s.2.2.2.2.1.length :=
    enc_capQ_le _ _
  have h3 : s.1.length * (2 * (8 + 3 * s.2.2.2.2.1.length) + 1) ≤
      (enc s).length * (2 * (8 + 3 * (enc s).length) + 1) := by gcongr
  change (encodePair enc enc (outerStep s d)).length ≤ _
  rw [encodePair_length]
  simp only [outerQ, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]
  omega

theorem outerFold_poly :
    Poly (fun x : List Unit × (SO × (Vec × ℚ)) => gfold outerStep x.1 x.2) :=
  poly_gfold outerStep outerStep_poly outerQ outerStep_size

/-! ### Constants, pads and static data -/

section consts
variable {α : Type} [Coding α]

theorem pw_poly : Poly (fun x : List ℕ × List Unit => pw x.1 x.2) := by
  unfold pw
  fun_prop

@[fun_prop] theorem pw_poly_comp {idx : α → List ℕ} {l : α → List Unit}
    (hi : Poly idx) (hl : Poly l) : Poly (fun x => pw (idx x) (l x)) :=
  Poly.comp (f := fun x : List ℕ × List Unit => pw x.1 x.2) (g := fun x => (idx x, l x))
    pw_poly (Poly.pair hi hl)

@[fun_prop] theorem fuelT_poly (c : Consts) : Poly (fuelT c) := by
  unfold fuelT
  fun_prop

@[fun_prop] theorem fuelK_poly (c : Consts) : Poly (fuelK c) := by
  unfold fuelK
  fun_prop

@[fun_prop] theorem padI_poly (c : Consts) : Poly (padI c) := by
  unfold padI
  fun_prop

@[fun_prop] theorem padO_poly (c : Consts) : Poly (padO c) := by
  unfold padO
  fun_prop

@[fun_prop] theorem nq_poly : Poly nq := by
  unfold nq
  fun_prop

@[fun_prop] theorem etaQ_poly (c : Consts) : Poly (etaQ c) := by
  unfold etaQ
  fun_prop

@[fun_prop] theorem sigQ_poly (c : Consts) : Poly (sigQ c) := by
  unfold sigQ
  fun_prop

@[fun_prop] theorem omQ_poly (c : Consts) : Poly (omQ c) := by
  unfold omQ
  fun_prop

@[fun_prop] theorem TQ_poly (c : Consts) : Poly (TQ c) := by
  unfold TQ
  fun_prop

theorem edgeW_poly : Poly (fun x : List NumericEdge × ℕ × ℕ => edgeW x.1 x.2.1 x.2.2) := by
  unfold edgeW
  fun_prop

@[fun_prop] theorem edgeW_poly_comp {xs : α → List NumericEdge} {i j : α → ℕ}
    (hx : Poly xs) (hi : Poly i) (hj : Poly j) :
    Poly (fun x => edgeW (xs x) (i x) (j x)) :=
  Poly.comp (f := fun x : List NumericEdge × ℕ × ℕ => edgeW x.1 x.2.1 x.2.2)
    (g := fun x => (xs x, i x, j x)) edgeW_poly (Poly.pair hx (Poly.pair hi hj))

theorem scaledN_poly (c : Consts) :
    Poly (fun x : List ℕ × List NumericEdge × ℕ × ℕ => scaledN c x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold scaledN
  fun_prop

@[fun_prop] theorem scaledN_poly_comp (c : Consts) {idx : α → List ℕ}
    {xs : α → List NumericEdge} {i j : α → ℕ}
    (hd : Poly idx) (hx : Poly xs) (hi : Poly i) (hj : Poly j) :
    Poly (fun x => scaledN c (idx x) (xs x) (i x) (j x)) :=
  Poly.comp
    (f := fun x : List ℕ × List NumericEdge × ℕ × ℕ => scaledN c x.1 x.2.1 x.2.2.1 x.2.2.2)
    (g := fun x => (idx x, xs x, i x, j x)) (scaledN_poly c)
    (Poly.pair hd (Poly.pair hx (Poly.pair hi hj)))

theorem lapList_poly (c : Consts) :
    Poly (fun x : List ℕ × List NumericEdge => lapList c x.1 x.2) := by
  unfold lapList
  fun_prop

@[fun_prop] theorem lapList_poly_comp (c : Consts) {idx : α → List ℕ}
    {xs : α → List NumericEdge} (hd : Poly idx) (hx : Poly xs) :
    Poly (fun x => lapList c (idx x) (xs x)) :=
  Poly.comp (f := fun x : List ℕ × List NumericEdge => lapList c x.1 x.2)
    (g := fun x => (idx x, xs x)) (lapList_poly c) (Poly.pair hd hx)

theorem staticO_poly (c : Consts) :
    Poly (fun x : List ℕ × List NumericEdge => staticO c x.1 x.2) := by
  unfold staticO
  fun_prop

theorem runO_poly (c : Consts) :
    Poly (fun x : List ℕ × List NumericEdge => runO c x.1 x.2) := by
  have h0 : Poly (fun x : List ℕ × List NumericEdge => x.1.map (fun _ => (0 : ℚ))) := by
    fun_prop
  have h1 : Poly (fun x : List ℕ × List NumericEdge =>
      (fuelT c x.1, (staticO c x.1 x.2, (x.1.map (fun _ => (0 : ℚ)), (0 : ℚ))))) :=
    Poly.pair (Poly.comp (fuelT_poly c) Poly.fst)
      (Poly.pair (staticO_poly c) (Poly.pair h0 (Automatic.Poly.const (0 : ℚ))))
  exact Poly.comp Poly.snd (Poly.comp outerFold_poly h1)

@[fun_prop] theorem runO_poly_comp (c : Consts) {idx : α → List ℕ}
    {xs : α → List NumericEdge} (hd : Poly idx) (hx : Poly xs) :
    Poly (fun x => runO c (idx x) (xs x)) :=
  Poly.comp (f := fun x : List ℕ × List NumericEdge => runO c x.1 x.2)
    (g := fun x => (idx x, xs x)) (runO_poly c) (Poly.pair hd hx)

theorem checkOK_poly (c : Consts) :
    Poly (fun x : List ℕ × Vec => checkOK c x.1 x.2) := by
  unfold checkOK
  fun_prop

@[fun_prop] theorem checkOK_poly_comp (c : Consts) {idx : α → List ℕ}
    {u : α → Vec} (hd : Poly idx) (hu : Poly u) :
    Poly (fun x => checkOK c (idx x) (u x)) :=
  Poly.comp (f := fun x : List ℕ × Vec => checkOK c x.1 x.2)
    (g := fun x => (idx x, u x)) (checkOK_poly c) (Poly.pair hd hu)

theorem rawVal_poly (c : Consts) :
    Poly (fun x : List ℕ × List NumericEdge => rawVal c x.1 x.2) := by
  unfold rawVal
  fun_prop

@[fun_prop] theorem rawVal_poly_comp (c : Consts) {idx : α → List ℕ}
    {xs : α → List NumericEdge} (hd : Poly idx) (hx : Poly xs) :
    Poly (fun x => rawVal c (idx x) (xs x)) :=
  Poly.comp (f := fun x : List ℕ × List NumericEdge => rawVal c x.1 x.2)
    (g := fun x => (idx x, xs x)) (rawVal_poly c) (Poly.pair hd hx)

theorem solveCore_poly (c : Consts) :
    Poly (fun x : List ℕ × List NumericEdge => solveCore c x.1 x.2) := by
  unfold solveCore
  fun_prop

end consts

/-- The solver is a polynomial-time function of the raw request bits. -/
theorem solveRaw_poly (c : Consts) : Poly (solveRaw c) := by
  unfold solveRaw
  exact Poly.comp (f := fun x : List ℕ × List NumericEdge => solveCore c x.1 x.2)
    (g := fun bits => (parserVertices bits, parseEdges bits)) (solveCore_poly c)
    (Poly.pair parserVertices_poly parseEdges_poly)

end QMCSub


