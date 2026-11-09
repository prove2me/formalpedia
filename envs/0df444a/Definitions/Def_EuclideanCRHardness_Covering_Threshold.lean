-- Prove2me | Definitions.Def_EuclideanCRHardness_Covering_Threshold
-- name    : EuclideanCRHardness_Covering_Threshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:20:56.127835+00:00
-- url     : https://prove2.me/theorems/20577ee3-e772-4993-89bf-0c9d37ec40b6
-- title:
--   Exact rational threshold and binary search
-- statement:
--   Fix $t=1/1000$ and $\gamma=1+10^{-6}$. For an instance with $m$ edges and diagonal mass $S$, set
--   $$U=S/4+t(1/2-95/128)m+14t^2m,\quad L=S/4+t(1/2-89/128)m.$$
--   Set $H=10^{12}m$. Bounded binary search on $[0,2Hm+1]$ finds the first nonnegative integer $k$ satisfying $k^2\ge H^2U$; put $r=k/H$ and output $(B,r)$.
--
--   The search uses exact rational comparisons and logarithmically many iterations. Invalid or isolated graph encodings return an empty bit string before dense output construction. Correctness and polynomial runtime are separate theorem targets.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), §5, equations (5.1)–(5.7), printed p. 9 / PDF p. 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf

import Definitions.Def_EuclideanCRHardness_Covering_Normalization
import Definitions.Def_EuclideanCRHardness_Covering_RationalInput

namespace EuclideanCRHardness.Covering

def tMain : ℚ := 1/1000
def gamma : ℚ := 1+1/1000000
def upperThreshold (G : SignedInstance) : ℚ :=
  diagonalMass G / 4 + tMain*(1/2-95/128)*G.edges.length + 14*tMain^2*G.edges.length

def lowerThreshold (G : SignedInstance) : ℚ :=
  diagonalMass G / 4 + tMain*(1/2-89/128)*G.edges.length

def denominatorScale (G : SignedInstance) : ℕ := 10^12 * G.edges.length
/-- Exact bounded binary search for the first square at least the rational threshold. -/
def lowerBoundSearch (p : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
      if lo < hi then
        let mid := (lo+hi)/2
        if p mid then lowerBoundSearch p fuel lo mid
        else lowerBoundSearch p fuel (mid+1) hi
      else lo

def thresholdIndex (G : SignedInstance) : ℕ :=
  let H := denominatorScale G
  let hi := 2*H*G.edges.length+1
  lowerBoundSearch (fun j => (H : ℚ)^2 * upperThreshold G ≤ (j : ℚ)^2)
    (Nat.log2 hi + 2) 0 hi

def roundedRadius (G : SignedInstance) : ℚ := thresholdIndex G / (denominatorScale G : ℚ)

def thresholdInput (G : SignedInstance) : CRInput :=
  matrixInput (rationalBasis tMain G) (roundedRadius G)
def basisBits (t : ℚ) (bits : List Bool) : List Bool :=
  match decodeSigned bits with
  | none => []
  | some G => if eligible G then encodeCR (matrixInput (rationalBasis t G) 1) else []
def thresholdBits (bits : List Bool) : List Bool :=
  match decodeSigned bits with
  | none => []
  | some G => if eligible G then encodeCR (thresholdInput G) else []

end EuclideanCRHardness.Covering


