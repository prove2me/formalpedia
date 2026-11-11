-- Prove2me | Definitions.Def_LiuHelsenDesigns_OneD_permutations
-- name    : LiuHelsenDesigns_OneD_permutations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T11:08:33.279225+00:00
-- url     : https://prove2.me/theorems/04e909ff-9e13-4e43-8d24-13f5cf7fe404
-- title:
--   Ordinary permutation moments and overlapping-register averages
-- statement:
--   Permutation matrices act on basis vectors by $|x\rangle\mapsto|\pi x\rangle$. Uniform averages range over the actual symmetric or alternating group, without multiplicity weights. AB and BC matrices include identity on the complementary register.
--
--   $$E_{AB}^{(k)}E_{BC}^{(k)}-E_{ABC}^{(k)}.$$
--
--   The overlap norm is the Euclidean operator norm of this difference. The printed bound is numerator cubed divided by the square root of the overlap dimension. When the overlap basis is empty and the order is positive, the ambient space is zero-dimensional and the bound is explicitly defined as zero.
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), pp.29,35, Lemmas 10 and 15, Eqs.(164),(196). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_designs
import Definitions.Def_DepthOneQExp_permToMatrix

noncomputable section

namespace LiuHelsenDesigns.OneD
attribute [local instance] Classical.decEq Classical.propDecidable

def permutationSet (I : Type) [Fintype I] (alt : Bool) : Finset (Equiv.Perm I) :=
  Finset.univ.filter fun p => alt = false ∨ Equiv.Perm.sign p = 1

def finiteAverage {I J : Type} [Fintype J]
    (S : Finset I) (F : I → Matrix J J ℂ) : Matrix J J ℂ :=
  (1 / (S.card : ℂ)) • ∑ s ∈ S, F s

def permutationAverage (I : Type) [Fintype I] (k : ℕ) (alt : Bool) :=
  finiteAverage (permutationSet I alt) (fun p => tensorPower (DepthOneQExp.permToMatrix p) k)

def permutationAB {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (p : Equiv.Perm (A × B)) : Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  fun x y => DepthOneQExp.permToMatrix p (x.1,x.2.1) (y.1,y.2.1) *
    (if x.2.2 = y.2.2 then 1 else 0)

def permutationBC {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (p : Equiv.Perm (B × C)) : Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  fun x y => (if x.1 = y.1 then 1 else 0) * DepthOneQExp.permToMatrix p x.2 y.2

def overlapError (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
    (k : ℕ) (alt : Bool) : ℝ :=
  matrixNorm
    (finiteAverage (permutationSet (A × B) alt) (fun p => tensorPower (permutationAB (C := C) p) k) *
      finiteAverage (permutationSet (B × C) alt) (fun p => tensorPower (permutationBC (A := A) p) k) -
      permutationAverage (A × (B × C)) k alt)

def overlapBound (b k : ℕ) : ℝ :=
  if b = 0 then 0 else ((k : ℝ)*Real.logb 2 k + Real.logb 2 b)^3 / Real.sqrt b

end LiuHelsenDesigns.OneD


