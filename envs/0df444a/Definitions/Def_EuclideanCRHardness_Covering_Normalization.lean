-- Prove2me | Definitions.Def_EuclideanCRHardness_Covering_Normalization
-- name    : EuclideanCRHardness_Covering_Normalization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:40.313633+00:00
-- url     : https://prove2.me/theorems/d1fcb76c-97ab-438a-9380-5243e8c1f785
-- title:
--   Degree normalization and rational lattice basis
-- statement:
--   Let $A_{ij}$ count inequality objects minus equality objects joining $i$ and $j$, with $A_{ii}=0$. Let $d_i$ be the uncancelled incidence degree. Choose the least $k_i\ge0$ with $4^{k_i}\ge d_i$, and put $T_i=2^{k_i}$ and $S=\sum_iT_i^2$. For rational $t$ define
--   $$B_{ij}=\mathbf1_{i=j}T_i+\frac{t}{2T_i}A_{ij}.$$
--
--   These are computations on the actual edge list, rather than free matrices assumed to encode its score. Rational bit length counts the explicit numerator and denominator fields. The degree-zero convention is defined, although Proposition 4.1 applies to nonisolated instances.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), equations (4.1)–(4.4), printed p. 7 / PDF p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf

import Definitions.Def_EuclideanCRHardness_Covering_Signed
import Definitions.Def_EuclideanCRHardness_Covering_Lattice

namespace EuclideanCRHardness.Covering

open scoped BigOperators

def adjacency (G : SignedInstance) : Matrix (Fin G.n) (Fin G.n) ℚ := fun i j =>
  if i = j then 0 else
    (G.edges.map (fun e =>
      if (e.u = i.val ∧ e.v = j.val) ∨ (e.v = i.val ∧ e.u = j.val)
      then if e.equal then (-1 : ℚ) else 1 else 0)).sum
/-- Finite search includes degree itself, so the least valid power is always found. -/
def dyadicScale (d : ℕ) : ℕ :=
  2 ^ (((List.range (d+1)).find? (fun k => d ≤ (2^k)^2)).getD 0)
def scale (G : SignedInstance) (i : Fin G.n) : ℚ := dyadicScale (degree G i)
def diagonalMass (G : SignedInstance) : ℚ := ∑ i, (scale G i)^2

def rationalBasis (t : ℚ) (G : SignedInstance) : Matrix (Fin G.n) (Fin G.n) ℚ :=
  fun i j => (if i = j then scale G i else 0) + (t/2) / scale G i * adjacency G i j

def realBasis (t : ℚ) (G : SignedInstance) : Matrix (Fin G.n) (Fin G.n) ℝ :=
  fun i j => rationalBasis t G i j

def rationalBits (q : ℚ) : ℕ := (ratFields q).foldl (fun n z => n + (intWord z).length) 0

end EuclideanCRHardness.Covering


