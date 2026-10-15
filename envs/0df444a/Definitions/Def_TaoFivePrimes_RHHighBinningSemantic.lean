-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighBinningSemantic
-- name    : TaoFivePrimes_RHHighBinningSemantic
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T05:42:19.403591+00:00
-- url     : https://prove2.me/theorems/ec46224d-c89b-45c2-929c-6a51af98406f
-- title:
--   Generic proved semantics of rational Dirichlet bin accumulation
-- statement:
--   Reusable definitions and ordinary Lean proofs for complex pair values, sparse coefficient lookup, componentwise accumulation and exact bin-list semantics. These are generic finite-list identities, with no finite-height zeta, analytic approximation, sign, count or RH assertion. A distinct public namespace avoids collisions with older proof-local helpers.
-- source:
--   Existing rational binning verification architecture after Platt DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
namespace RHHighBinningSemantic
open RHHighDirichletBinning
lemma termsAux_length (K : Nat) (d wr wi p : Int) : (termsAux K d wr wi p).length=K := by
  induction K generalizing p with
  | zero => rfl
  | succ K ih => simp only [termsAux,List.length_cons,ih]
lemma terms_length (w : Nat) : (terms w).length=24 := termsAux_length _ _ _ _ _
lemma termsAux_iterates (K : Nat) (d wr wi p : Int) :
    termsAux K d wr wi p=(List.range K).map (fun k=>
      (wr*((fun v:Int=>v*d/(2:Int)^128)^[k] p)/(2:Int)^128,
       wi*((fun v:Int=>v*d/(2:Int)^128)^[k] p)/(2:Int)^128)) := by
  induction K generalizing p with
  | zero => rfl
  | succ K ih =>
    rw [termsAux,List.range_succ_eq_map,List.map_cons,List.map_map,ih]
    congr 1
lemma add_length (xs ys : List (Int×Int)) : (add xs ys).length=min xs.length ys.length := by
  simp only [add,List.length_zipWith]
lemma add_get (xs ys : List (Int×Int)) (k : Nat) (hx:k<xs.length) (hy:k<ys.length) :
    (add xs ys)[k]'(by rw [add_length];omega)=(xs[k].1+ys[k].1,xs[k].2+ys[k].2) := by
  simp only [add,List.getElem_zipWith]
noncomputable def pairValue (v : Int×Int) : ℂ := (v.1:ℂ)+(v.2:ℂ)*I
noncomputable def coefficientAt (xs : List (Int×Int)) (k : Nat) : ℂ := pairValue ((xs[k]?).getD (0,0))
lemma coefficientAt_add (xs ys : List (Int×Int)) (k : Nat) (hx:k<xs.length) (hy:k<ys.length) :
    coefficientAt (add xs ys) k=coefficientAt xs k+coefficientAt ys k := by
  unfold coefficientAt
  rw [List.getElem?_eq_getElem (by rw [add_length];omega),List.getElem?_eq_getElem hx,
    List.getElem?_eq_getElem hy]
  simp only [Option.getD_some]
  rw [add_get xs ys k hx hy]
  unfold pairValue
  push_cast
  ring
noncomputable def sparseValue (m k : Nat) (gs : List (Nat×List (Int×Int))) : ℂ :=
  (gs.map (fun g=>if g.1=m then coefficientAt g.2 k else 0)).sum
lemma sparseValue_cons (m k j : Nat) (a : List (Int×Int)) (gs : List (Nat×List (Int×Int))) :
    sparseValue m k ((j,a)::gs)=(if j=m then coefficientAt a k else 0)+sparseValue m k gs := by
  rfl
lemma accumulate_value (m k j : Nat) (acc : List (Int×Int)) (ws : List Nat)
    (hk:k<24) (ha:acc.length=24) :
    sparseValue m k (accumulate j acc ws)=
      (if j=m then coefficientAt acc k else 0)+
      ((ws.map (fun w=>if bin w=m then coefficientAt (terms w) k else 0)).sum) := by
  induction ws generalizing j acc with
  | nil => simp [accumulate,sparseValue]
  | cons w ws ih =>
    by_cases hb:bin w=j
    · rw [accumulate,if_pos hb]
      rw [ih j (add acc (terms w)) (by rw [add_length,ha,terms_length];rfl),
        coefficientAt_add acc (terms w) k (by omega) (by rw [terms_length];exact hk)]
      simp only [List.map_cons,List.sum_cons,hb]
      by_cases hm:j=m <;> simp only [hm,if_true,if_false] <;> ring
    · rw [accumulate,if_neg hb,sparseValue_cons,ih (bin w) (terms w) (terms_length w)]
      simp only [List.map_cons,List.sum_cons]
lemma bins_value (m k : Nat) (ws : List Nat) (hk:k<24) :
    sparseValue m k (bins ws)=((ws.map (fun w=>if bin w=m then coefficientAt (terms w) k else 0)).sum) := by
  cases ws with
  | nil => rfl
  | cons w ws => exact accumulate_value m k (bin w) (terms w) ws hk (terms_length w)
end RHHighBinningSemantic
noncomputable def TaoFivePrimes_RHHighBinningSemantic : Nat := 24


