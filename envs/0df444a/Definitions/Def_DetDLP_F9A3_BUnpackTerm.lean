-- Prove2me | Definitions.Def_DetDLP_F9A3_BUnpackTerm
-- name    : DetDLP_F9A3_BUnpackTerm
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T02:51:05.68268+00:00
-- url     : https://prove2.me/theorems/1ea07cf8-4740-48cc-bc37-a558fc4ebcd5
-- title:
--   Bit decoder for one residual unpacking term
-- statement:
--   The raw decoder receives the modulus, scale, unary row and column counts, lower coefficients of the monic polynomial, and flattened digit table. It scales each row and reduces it by Horner iteration modulo the defining monic polynomial.

import Definitions.Def_DetDLP_ResidualScalarOracle

import Definitions.Def_DetDLP_W1_Queries
import Definitions.Def_DetDLP_W5_M6Sort
import Definitions.Def_DetDLP_PolyTBridge

namespace DetDLP.ResidualScalarOracle
open Polynomial Finset
noncomputable section

def unpackTerm (f : ℤ[X]) (ell q : ℕ) (G : BipartiteMultigraph) (h : ℕ) {J : ℕ}
    (a : Fin G.nV → Fin J) (d : Fin (spacing f G * ell) → ℕ) : B f ell q :=
  let K := spacing f G
  let digit (j : Fin ell) (i : Fin K) : ℤ :=
    (2:ℤ)^(h*∑ v,(a v).val)*(d ⟨i.val+K*j.val,by
      have H := Nat.mul_le_mul_left K j.isLt
      rw [Nat.mul_succ] at H; have hi := i.isLt; change i.val+K*j.val<K*ell; omega⟩:ℤ)
  let inner := (AdjoinRoot.mk (f.map (Int.castRingHom (ZMod (2^q))))).comp (Polynomial.mapRingHom (Int.castRingHom (ZMod (2^q))))
  let outer := (AdjoinRoot.mk ((X:(U f q)[X])^ell)).comp (Polynomial.mapRingHom inner)
  outer (∑ j : Fin ell,monomial j.val (∑ i : Fin K,monomial i.val (digit j i)))

def fCoeffs (f : ℤ[X]) (q : ℕ) : List ℕ :=
  List.ofFn fun j : Fin f.natDegree => (f.coeff j.val : ZMod (2^q)).val

/-- One Horner step, reducing the overflow using the monic defining relation. -/
def hornerStep (m : ℕ) (fc s : List ℕ) (v : ℕ) : List ℕ :=
  (List.range fc.length).map fun i =>
    (((v :: s).getD i 0 + m) - (s.getD (fc.length - 1) 0 * fc.getD i 0) % m) % m

def reduceRow (m : ℕ) (fc row : List ℕ) : List ℕ :=
  row.reverse.foldl (hornerStep (max 1 m) fc) (fc.map fun _ => 0)

def unpackRows (m scalar : ℕ) (rows cols : List Bool) (fc ds : List ℕ) : List ℕ :=
  (List.range rows.length).flatMap fun j => reduceRow m fc ((List.range cols.length).map
    fun i => scalar * ds.getD (i + cols.length * j) 0)

open DetDLP_W1_Queries in
def bUnpackTermRaw (w : List Bool) : List Bool :=
  encodeNatListBin (unpackRows (Groundwork.PolyT.bval (first w))
    (Groundwork.PolyT.bval (first (more w))) (first (more (more w)))
    (first (more (more (more w)))) (w5_M6Sort.decode (first (more (more (more (more w))))))
    (w5_M6Sort.decode (first (more (more (more (more (more w))))))))

end
end DetDLP.ResidualScalarOracle


