-- Prove2me | Definitions.Def_QMCTied_Poly
-- name    : QMCTied_Poly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T10:15:10.014046+00:00
-- url     : https://prove2.me/theorems/5512393c-a6fc-4129-96d5-60b37b74858c
-- title:
--   The Pauli moment relaxation program is polynomial-time
-- statement:
--   For every fixed level $k$ and accuracy parameter $E$, the solver is a polynomial-time function of the raw request bits in the finite Boolean-machine runtime: the word enumeration, the tables, the guarded matrix-power loop and the outer loop.
-- source:
--   Supporting library for QuantumMaxCutEnergy.PauliSDP.uniform_value_lower_approximation_compiler (Prove2me Quantum Max-Cut campaign; level-k Pauli moment relaxation as in Gribling, Sinjorgo and Sotirov, arXiv:2504.11120, Section 2). Method: integer penalty supergradient iteration with matrix-power certificates.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QMCSub_Fold
import Definitions.Def_QMCSub_Prog
import Definitions.Def_QMCSub_Poly
import Definitions.Def_QMCTied_Prog

/-!
The list program for the Pauli moment relaxation is polynomial-time.
-/

namespace QMCTied
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime QMCSub
open Polynomial

/-! ### Scalar pieces and the shifted matrix -/

section pieces
variable {α : Type} [Coding α]

/-- The index list of a list. -/
theorem range_poly {β : Type} [Coding β] [Inhabited β] {xs : α → List β} (hx : Poly xs) :
    Poly (fun x => List.range (xs x).length) :=
  Poly.comp (f := fun l : List β => List.range l.length) (g := xs) Poly.list_indices hx

/-- The index list of a list, as a named function. -/
def rangeL {β : Type} (l : List β) : List ℕ := List.range l.length

theorem range_eq {β : Type} (l : List β) : List.range l.length = rangeL l := rfl

@[fun_prop] theorem rangeL_poly {β : Type} [Coding β] [Inhabited β] :
    Poly (rangeL : List β → List ℕ) := Poly.list_indices

@[fun_prop] theorem qrnd_poly : Poly qrnd := by
  unfold qrnd
  fun_prop

theorem clampQ_poly : Poly (fun x : ℚ × ℚ => clampQ x.1 x.2) := by
  unfold clampQ
  fun_prop

@[fun_prop] theorem clampQ_poly_comp {D q : α → ℚ} (hD : Poly D) (hq : Poly q) :
    Poly (fun x => clampQ (D x) (q x)) :=
  Poly.comp (f := fun x : ℚ × ℚ => clampQ x.1 x.2) (g := fun x => (D x, q x))
    clampQ_poly (Poly.pair hD hq)

theorem maxQ_poly : Poly (fun x : ℚ × ℚ => maxQ x.1 x.2) := by
  unfold maxQ
  fun_prop

@[fun_prop] theorem maxQ_poly_comp {a b : α → ℚ} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => maxQ (a x) (b x)) :=
  Poly.comp (f := fun x : ℚ × ℚ => maxQ x.1 x.2) (g := fun x => (a x, b x))
    maxQ_poly (Poly.pair ha hb)

theorem shiftT_poly :
    Poly (fun x : List ℕ × Mat × ℚ × Mat => shiftT x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold shiftT
  fun_prop

@[fun_prop] theorem shiftT_poly_comp {idx : α → List ℕ} {sg : α → Mat} {D : α → ℚ}
    {Y : α → Mat} (hi : Poly idx) (hs : Poly sg) (hD : Poly D) (hY : Poly Y) :
    Poly (fun x => shiftT (idx x) (sg x) (D x) (Y x)) :=
  Poly.comp (f := fun x : List ℕ × Mat × ℚ × Mat => shiftT x.1 x.2.1 x.2.2.1 x.2.2.2)
    (g := fun x => (idx x, sg x, D x, Y x)) shiftT_poly
    (Poly.pair hi (Poly.pair hs (Poly.pair hD hY)))

theorem gQT_poly :
    Poly (fun x : List ℕ × Mat × Mat × Mat × ℕ × ℕ =>
      gQT x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) := by
  unfold gQT
  fun_prop

@[fun_prop] theorem gQT_poly_comp {idx : α → List ℕ} {cl sg Q : α → Mat} {i j : α → ℕ}
    (hd : Poly idx) (hc : Poly cl) (hs : Poly sg) (hQ : Poly Q) (hi : Poly i) (hj : Poly j) :
    Poly (fun x => gQT (idx x) (cl x) (sg x) (Q x) (i x) (j x)) :=
  Poly.comp
    (f := fun x : List ℕ × Mat × Mat × Mat × ℕ × ℕ =>
      gQT x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (g := fun x => (idx x, cl x, sg x, Q x, i x, j x)) gQT_poly
    (Poly.pair hd (Poly.pair hc (Poly.pair hs (Poly.pair hQ (Poly.pair hi hj)))))

/-! ### The iteration on tables -/

theorem powT_poly : Poly (fun x : ST × Mat => powT x.1 x.2) := by
  unfold powT
  fun_prop

@[fun_prop] theorem powT_poly_comp {s : α → ST} {Y : α → Mat} (hs : Poly s) (hY : Poly Y) :
    Poly (fun x => powT (s x) (Y x)) :=
  Poly.comp (f := fun x : ST × Mat => powT x.1 x.2) (g := fun x => (s x, Y x))
    powT_poly (Poly.pair hs hY)

theorem actT_poly : Poly (fun x : ST × Mat => actT x.1 x.2) := by
  unfold actT
  fun_prop

@[fun_prop] theorem actT_poly_comp {s : α → ST} {Y : α → Mat} (hs : Poly s) (hY : Poly Y) :
    Poly (fun x => actT (s x) (Y x)) :=
  Poly.comp (f := fun x : ST × Mat => actT x.1 x.2) (g := fun x => (s x, Y x))
    actT_poly (Poly.pair hs hY)

theorem stepT_poly :
    Poly (fun x : ST × Mat × ℕ × ℕ => stepT x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold stepT
  fun_prop

@[fun_prop] theorem stepT_poly_comp {s : α → ST} {Y : α → Mat} {i j : α → ℕ}
    (hs : Poly s) (hY : Poly Y) (hi : Poly i) (hj : Poly j) :
    Poly (fun x => stepT (s x) (Y x) (i x) (j x)) :=
  Poly.comp (f := fun x : ST × Mat × ℕ × ℕ => stepT x.1 x.2.1 x.2.2.1 x.2.2.2)
    (g := fun x => (s x, Y x, i x, j x)) stepT_poly
    (Poly.pair hs (Poly.pair hY (Poly.pair hi hj)))

theorem nextT_poly : Poly (fun x : ST × Mat => nextT x.1 x.2) := by
  unfold nextT
  fun_prop

@[fun_prop] theorem nextT_poly_comp {s : α → ST} {Y : α → Mat} (hs : Poly s) (hY : Poly Y) :
    Poly (fun x => nextT (s x) (Y x)) :=
  Poly.comp (f := fun x : ST × Mat => nextT x.1 x.2) (g := fun x => (s x, Y x))
    nextT_poly (Poly.pair hs hY)

theorem aqT_poly : Poly (fun x : ST × Mat => aqT x.1 x.2) := by
  unfold aqT
  fun_prop

@[fun_prop] theorem aqT_poly_comp {s : α → ST} {Y : α → Mat} (hs : Poly s) (hY : Poly Y) :
    Poly (fun x => aqT (s x) (Y x)) :=
  Poly.comp (f := fun x : ST × Mat => aqT x.1 x.2) (g := fun x => (s x, Y x))
    aqT_poly (Poly.pair hs hY)

theorem objT_poly : Poly (fun x : ST × Mat => objT x.1 x.2) := by
  unfold objT
  fun_prop

@[fun_prop] theorem objT_poly_comp {s : α → ST} {Y : α → Mat} (hs : Poly s) (hY : Poly Y) :
    Poly (fun x => objT (s x) (Y x)) :=
  Poly.comp (f := fun x : ST × Mat => objT x.1 x.2) (g := fun x => (s x, Y x))
    objT_poly (Poly.pair hs hY)

theorem valT_poly : Poly (fun x : ST × Mat => valT x.1 x.2) := by
  unfold valT
  fun_prop

@[fun_prop] theorem valT_poly_comp {s : α → ST} {Y : α → Mat} (hs : Poly s) (hY : Poly Y) :
    Poly (fun x => valT (s x) (Y x)) :=
  Poly.comp (f := fun x : ST × Mat => valT x.1 x.2) (g := fun x => (s x, Y x))
    valT_poly (Poly.pair hs hY)

end pieces

theorem stepO_poly : Poly (fun x : ST × (Mat × ℚ) => stepO x.1 x.2) := by
  unfold stepO
  fun_prop

/-! ### Size of one step -/

theorem nextT_size (s : ST) (Y : Mat) :
    (enc (nextT s Y)).length ≤
      s.1.length * (2 * (s.1.length * (2 * (8 + 3 * s.2.2.2.2.2.2.2.1.length) + 1)) + 1) := by
  unfold nextT
  refine encodeList_map_le enc _ _ (fun i => ?_) _
  refine encodeList_map_le enc _ _ (fun j => ?_) _
  split_ifs <;> exact enc_capQ_le _ _

/-- Size polynomial for the step. -/
noncomputable def stepQ : Polynomial ℕ :=
  2 * (X * (2 * (X * (2 * (8 + 3 * X) + 1)) + 1)) + 1 + (8 + 3 * X)

theorem stepO_size (s : ST) (d : Mat × ℚ) :
    (enc (stepO s d)).length ≤ stepQ.eval (enc s).length := by
  have hn : s.1.length ≤ (enc s).length := length_fst_le_enc s
  have hp : s.2.2.2.2.2.2.2.1.length ≤ (enc s).length :=
    (length_fst_le_enc s.2.2.2.2.2.2.2).trans ((enc_snd_le_enc s.2.2.2.2.2.2).trans
      ((enc_snd_le_enc s.2.2.2.2.2).trans ((enc_snd_le_enc s.2.2.2.2).trans
        ((enc_snd_le_enc s.2.2.2).trans ((enc_snd_le_enc s.2.2).trans
          ((enc_snd_le_enc s.2).trans (enc_snd_le_enc s)))))))
  have h1 : (enc (stepO s d).1).length ≤
      s.1.length * (2 * (s.1.length * (2 * (8 + 3 * s.2.2.2.2.2.2.2.1.length) + 1)) + 1) :=
    nextT_size s d.1
  have h2 : (enc (stepO s d).2).length ≤ 8 + 3 * s.2.2.2.2.2.2.2.1.length :=
    enc_capQ_le _ _
  have h3 : s.1.length * (2 * (s.1.length * (2 * (8 + 3 * s.2.2.2.2.2.2.2.1.length) + 1)) + 1) ≤
      (enc s).length * (2 * ((enc s).length * (2 * (8 + 3 * (enc s).length) + 1)) + 1) := by
    gcongr
  change (encodePair enc enc (stepO s d)).length ≤ _
  rw [encodePair_length]
  simp only [stepQ, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]
  omega

theorem stepOFold_poly :
    Poly (fun x : List Unit × (ST × (Mat × ℚ)) => gfold stepO x.1 x.2) :=
  poly_gfold stepO stepO_poly stepQ stepO_size

/-! ### Pauli words and tables -/

section words
variable {α : Type} [Coding α]

@[fun_prop] theorem zeroW_poly : Poly zeroW := by
  unfold zeroW
  fun_prop

theorem setW_poly : Poly (fun x : List ℕ × Vec × ℕ × ℚ => setW x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold setW
  fun_prop

@[fun_prop] theorem setW_poly_comp {idxn : α → List ℕ} {w : α → Vec} {p : α → ℕ} {a : α → ℚ}
    (hd : Poly idxn) (hw : Poly w) (hp : Poly p) (ha : Poly a) :
    Poly (fun x => setW (idxn x) (w x) (p x) (a x)) :=
  Poly.comp (f := fun x : List ℕ × Vec × ℕ × ℚ => setW x.1 x.2.1 x.2.2.1 x.2.2.2)
    (g := fun x => (idxn x, w x, p x, a x)) setW_poly
    (Poly.pair hd (Poly.pair hw (Poly.pair hp ha)))

theorem extW_poly : Poly (fun x : List ℕ × List Vec => extW x.1 x.2) := by
  unfold extW
  fun_prop

@[fun_prop] theorem extW_poly_comp {idxn : α → List ℕ} {ws : α → List Vec}
    (hd : Poly idxn) (hw : Poly ws) : Poly (fun x => extW (idxn x) (ws x)) :=
  Poly.comp (f := fun x : List ℕ × List Vec => extW x.1 x.2) (g := fun x => (idxn x, ws x))
    extW_poly (Poly.pair hd hw)

@[fun_prop] theorem rowsRaw_poly (k : ℕ) : Poly (rowsRaw k) := by
  induction k with
  | zero =>
      have h : rowsRaw 0 = fun idxn => [zeroW idxn] := by
        funext idxn
        rfl
      rw [h]
      exact Poly.comp (f := fun x : Vec × List Vec => x.1 :: x.2)
        (g := fun idxn => (zeroW idxn, ([] : List Vec))) Poly.list_cons
        (Poly.pair zeroW_poly (Automatic.Poly.const ([] : List Vec)))
  | succ k ih =>
      have h : rowsRaw (k + 1) = fun idxn => extW idxn (rowsRaw k idxn) := by
        funext idxn
        rfl
      rw [h]
      exact extW_poly_comp (idxn := fun x => x) (ws := rowsRaw k) Poly.identity ih

theorem wordEq_poly : Poly (fun x : List ℕ × Vec × Vec => wordEq x.1 x.2.1 x.2.2) := by
  unfold wordEq
  fun_prop

@[fun_prop] theorem wordEq_poly_comp {idxn : α → List ℕ} {w v : α → Vec}
    (hd : Poly idxn) (hw : Poly w) (hv : Poly v) :
    Poly (fun x => wordEq (idxn x) (w x) (v x)) :=
  Poly.comp (f := fun x : List ℕ × Vec × Vec => wordEq x.1 x.2.1 x.2.2)
    (g := fun x => (idxn x, w x, v x)) wordEq_poly (Poly.pair hd (Poly.pair hw hv))

theorem rowAt_poly : Poly (fun x : List Vec × ℕ => rowAt x.1 x.2) := by
  unfold rowAt
  fun_prop

@[fun_prop] theorem rowAt_poly_comp {rows : α → List Vec} {i : α → ℕ}
    (hr : Poly rows) (hi : Poly i) : Poly (fun x => rowAt (rows x) (i x)) :=
  Poly.comp (f := fun x : List Vec × ℕ => rowAt x.1 x.2) (g := fun x => (rows x, i x))
    rowAt_poly (Poly.pair hr hi)

theorem dedupW_poly : Poly (fun x : List ℕ × List Vec => dedupW x.1 x.2) := by
  unfold dedupW
  simp only [range_eq]
  fun_prop

@[fun_prop] theorem dedupW_poly_comp {idxn : α → List ℕ} {R : α → List Vec}
    (hd : Poly idxn) (hR : Poly R) : Poly (fun x => dedupW (idxn x) (R x)) :=
  Poly.comp (f := fun x : List ℕ × List Vec => dedupW x.1 x.2) (g := fun x => (idxn x, R x))
    dedupW_poly (Poly.pair hd hR)

@[fun_prop] theorem rowsW_poly (k : ℕ) : Poly (rowsW k) := by
  unfold rowsW
  fun_prop

theorem lp_poly : Poly (fun x : ℚ × ℚ => lp x.1 x.2) := by
  unfold lp
  fun_prop

@[fun_prop] theorem lp_poly_comp {a b : α → ℚ} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => lp (a x) (b x)) :=
  Poly.comp (f := fun x : ℚ × ℚ => lp x.1 x.2) (g := fun x => (a x, b x))
    lp_poly (Poly.pair ha hb)

theorem le_poly : Poly (fun x : ℚ × ℚ => le x.1 x.2) := by
  unfold le
  fun_prop

@[fun_prop] theorem le_poly_comp {a b : α → ℚ} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => le (a x) (b x)) :=
  Poly.comp (f := fun x : ℚ × ℚ => le x.1 x.2) (g := fun x => (a x, b x))
    le_poly (Poly.pair ha hb)

theorem prodW_poly : Poly (fun x : List ℕ × Vec × Vec => prodW x.1 x.2.1 x.2.2) := by
  unfold prodW
  fun_prop

@[fun_prop] theorem prodW_poly_comp {idxn : α → List ℕ} {w v : α → Vec}
    (hd : Poly idxn) (hw : Poly w) (hv : Poly v) :
    Poly (fun x => prodW (idxn x) (w x) (v x)) :=
  Poly.comp (f := fun x : List ℕ × Vec × Vec => prodW x.1 x.2.1 x.2.2)
    (g := fun x => (idxn x, w x, v x)) prodW_poly (Poly.pair hd (Poly.pair hw hv))

theorem expoW_poly : Poly (fun x : List ℕ × Vec × Vec => expoW x.1 x.2.1 x.2.2) := by
  unfold expoW
  fun_prop

@[fun_prop] theorem expoW_poly_comp {idxn : α → List ℕ} {w v : α → Vec}
    (hd : Poly idxn) (hw : Poly w) (hv : Poly v) :
    Poly (fun x => expoW (idxn x) (w x) (v x)) :=
  Poly.comp (f := fun x : List ℕ × Vec × Vec => expoW x.1 x.2.1 x.2.2)
    (g := fun x => (idxn x, w x, v x)) expoW_poly (Poly.pair hd (Poly.pair hw hv))

@[fun_prop] theorem sgnOf_poly : Poly sgnOf := by
  unfold sgnOf
  fun_prop

theorem sgnTabW_poly : Poly (fun x : List ℕ × List Vec => sgnTabW x.1 x.2) := by
  unfold sgnTabW
  simp only [range_eq]
  fun_prop

@[fun_prop] theorem sgnTabW_poly_comp {idxn : α → List ℕ} {rows : α → List Vec}
    (hd : Poly idxn) (hr : Poly rows) : Poly (fun x => sgnTabW (idxn x) (rows x)) :=
  Poly.comp (f := fun x : List ℕ × List Vec => sgnTabW x.1 x.2)
    (g := fun x => (idxn x, rows x)) sgnTabW_poly (Poly.pair hd hr)

@[fun_prop] theorem pairsW_poly : Poly pairsW := by
  unfold pairsW
  simp only [range_eq]
  fun_prop

theorem clsTabW_poly : Poly (fun x : List ℕ × List Vec => clsTabW x.1 x.2) := by
  unfold clsTabW
  simp only [range_eq]
  fun_prop

@[fun_prop] theorem clsTabW_poly_comp {idxn : α → List ℕ} {rows : α → List Vec}
    (hd : Poly idxn) (hr : Poly rows) : Poly (fun x => clsTabW (idxn x) (rows x)) :=
  Poly.comp (f := fun x : List ℕ × List Vec => clsTabW x.1 x.2)
    (g := fun x => (idxn x, rows x)) clsTabW_poly (Poly.pair hd hr)

theorem suppW_poly : Poly (fun x : List ℕ × Vec => suppW x.1 x.2) := by
  unfold suppW
  fun_prop

@[fun_prop] theorem suppW_poly_comp {idxn : α → List ℕ} {w : α → Vec}
    (hd : Poly idxn) (hw : Poly w) : Poly (fun x => suppW (idxn x) (w x)) :=
  Poly.comp (f := fun x : List ℕ × Vec => suppW x.1 x.2) (g := fun x => (idxn x, w x))
    suppW_poly (Poly.pair hd hw)

theorem csTabW_poly :
    Poly (fun x : List ℕ × List Vec × List NumericEdge => csTabW x.1 x.2.1 x.2.2) := by
  unfold csTabW
  simp only [range_eq]
  fun_prop

@[fun_prop] theorem csTabW_poly_comp {idxn : α → List ℕ} {rows : α → List Vec}
    {xs : α → List NumericEdge} (hd : Poly idxn) (hr : Poly rows) (hx : Poly xs) :
    Poly (fun x => csTabW (idxn x) (rows x) (xs x)) :=
  Poly.comp (f := fun x : List ℕ × List Vec × List NumericEdge => csTabW x.1 x.2.1 x.2.2)
    (g := fun x => (idxn x, rows x, xs x)) csTabW_poly (Poly.pair hd (Poly.pair hr hx))

theorem gCTabW_poly : Poly (fun x : List ℕ × Mat × Mat => gCTabW x.1 x.2.1 x.2.2) := by
  unfold gCTabW
  fun_prop

@[fun_prop] theorem gCTabW_poly_comp {idx : α → List ℕ} {cl cs : α → Mat}
    (hd : Poly idx) (hc : Poly cl) (hs : Poly cs) :
    Poly (fun x => gCTabW (idx x) (cl x) (cs x)) :=
  Poly.comp (f := fun x : List ℕ × Mat × Mat => gCTabW x.1 x.2.1 x.2.2)
    (g := fun x => (idx x, cl x, cs x)) gCTabW_poly (Poly.pair hd (Poly.pair hc hs))

end words

/-! ### Parameters, pads and static data -/

section params
variable {α : Type} [Coding α]

@[fun_prop] theorem NQ_poly : Poly NQ := by
  unfold NQ
  fun_prop

@[fun_prop] theorem DQ_poly (E : ℕ) : Poly (DQ E) := by
  unfold DQ
  fun_prop

@[fun_prop] theorem etaQ2_poly (E : ℕ) : Poly (etaQ2 E) := by
  unfold etaQ2
  fun_prop

@[fun_prop] theorem dNQ_poly (E : ℕ) : Poly (dNQ E) := by
  unfold dNQ
  fun_prop

@[fun_prop] theorem prmW_poly (E : ℕ) : Poly (prmW E) := by
  unfold prmW
  fun_prop

@[fun_prop] theorem fuelT2_poly (E : ℕ) : Poly (fuelT2 E) := by
  unfold fuelT2
  fun_prop

@[fun_prop] theorem fuelK2_poly (E : ℕ) : Poly (fuelK2 E) := by
  unfold fuelK2
  fun_prop

@[fun_prop] theorem padI2_poly (E : ℕ) : Poly (padI2 E) := by
  unfold padI2
  fun_prop

@[fun_prop] theorem padO2_poly (E : ℕ) : Poly (padO2 E) := by
  unfold padO2
  fun_prop

theorem initY_poly : Poly (fun x : ℚ × List ℕ => initY x.1 x.2) := by
  unfold initY
  fun_prop

@[fun_prop] theorem initY_poly_comp {D : α → ℚ} {idx : α → List ℕ}
    (hD : Poly D) (hi : Poly idx) : Poly (fun x => initY (D x) (idx x)) :=
  Poly.comp (f := fun x : ℚ × List ℕ => initY x.1 x.2) (g := fun x => (D x, idx x))
    initY_poly (Poly.pair hD hi)

/-- The number of rows, as an index list. -/
def idxW (k : ℕ) (idxn : List ℕ) : List ℕ := List.range (rowsW k idxn).length

@[fun_prop] theorem idxW_poly (k : ℕ) : Poly (idxW k) := by
  unfold idxW
  exact range_poly (rowsW_poly k)

theorem staticW_eq (k E : ℕ) (idxn : List ℕ) (xs : List NumericEdge) :
    staticW k E idxn xs =
      (idxW k idxn,
       clsTabW idxn (rowsW k idxn),
       sgnTabW idxn (rowsW k idxn),
       gCTabW (idxW k idxn) (clsTabW idxn (rowsW k idxn)) (csTabW idxn (rowsW k idxn) xs),
       csTabW idxn (rowsW k idxn) xs,
       fuelK2 E (idxW k idxn),
       padI2 E (idxW k idxn),
       padO2 E (idxW k idxn),
       prmW E (idxW k idxn)) := rfl

theorem staticW_poly (k E : ℕ) :
    Poly (fun x : List ℕ × List NumericEdge => staticW k E x.1 x.2) := by
  simp only [staticW_eq]
  fun_prop

theorem runW_eq (k E : ℕ) (idxn : List ℕ) (xs : List NumericEdge) :
    runW k E idxn xs =
      (gfold stepO (fuelT2 E (idxW k idxn))
        (staticW k E idxn xs, (initY (DQ E (idxW k idxn)) (idxW k idxn), (0 : ℚ)))).2 := rfl

theorem runW_poly (k E : ℕ) :
    Poly (fun x : List ℕ × List NumericEdge => runW k E x.1 x.2) := by
  have h0 : Poly (fun x : List ℕ × List NumericEdge =>
      initY (DQ E (idxW k x.1)) (idxW k x.1)) := by
    fun_prop
  have hf : Poly (fun x : List ℕ × List NumericEdge => fuelT2 E (idxW k x.1)) := by
    fun_prop
  have h1 : Poly (fun x : List ℕ × List NumericEdge =>
      (fuelT2 E (idxW k x.1),
        (staticW k E x.1 x.2, (initY (DQ E (idxW k x.1)) (idxW k x.1), (0 : ℚ))))) :=
    Poly.pair hf (Poly.pair (staticW_poly k E) (Poly.pair h0 (Automatic.Poly.const (0 : ℚ))))
  have h2 : Poly (fun x : List ℕ × List NumericEdge =>
      gfold stepO (fuelT2 E (idxW k x.1))
        (staticW k E x.1 x.2, (initY (DQ E (idxW k x.1)) (idxW k x.1), (0 : ℚ)))) :=
    Poly.comp (f := fun x : List Unit × (ST × (Mat × ℚ)) => gfold stepO x.1 x.2)
      (g := fun x : List ℕ × List NumericEdge =>
        (fuelT2 E (idxW k x.1),
          (staticW k E x.1 x.2, (initY (DQ E (idxW k x.1)) (idxW k x.1), (0 : ℚ)))))
      stepOFold_poly h1
  simp only [runW_eq]
  exact Poly.comp (f := Prod.snd) (g := fun x : List ℕ × List NumericEdge =>
      gfold stepO (fuelT2 E (idxW k x.1))
        (staticW k E x.1 x.2, (initY (DQ E (idxW k x.1)) (idxW k x.1), (0 : ℚ))))
    Poly.snd h2

@[fun_prop] theorem runW_poly_comp (k E : ℕ) {idxn : α → List ℕ}
    {xs : α → List NumericEdge} (hd : Poly idxn) (hx : Poly xs) :
    Poly (fun x => runW k E (idxn x) (xs x)) :=
  Poly.comp (f := fun x : List ℕ × List NumericEdge => runW k E x.1 x.2)
    (g := fun x => (idxn x, xs x)) (runW_poly k E) (Poly.pair hd hx)

theorem solveW_poly (k E : ℕ) :
    Poly (fun x : List ℕ × List NumericEdge => solveW k E x.1 x.2) := by
  unfold solveW
  fun_prop

end params

/-- The solver is a polynomial-time function of the raw request bits. -/
theorem solveRawW_poly (k E : ℕ) : Poly (solveRawW k E) := by
  unfold solveRawW
  exact Poly.comp (f := fun x : List ℕ × List NumericEdge => solveW k E x.1 x.2)
    (g := fun bits => (parserVertices bits, parseEdges bits)) (solveW_poly k E)
    (Poly.pair parserVertices_poly parseEdges_poly)

end QMCTied


