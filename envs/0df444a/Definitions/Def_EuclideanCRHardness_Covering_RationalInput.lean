-- Prove2me | Definitions.Def_EuclideanCRHardness_Covering_RationalInput
-- name    : EuclideanCRHardness_Covering_RationalInput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:07.175879+00:00
-- url     : https://prove2.me/theorems/8a35664f-8e73-4640-8a53-2cd16a33edc3
-- title:
--   Square rational basis and positive radius input
-- statement:
--   A raw input consists of a dimension $n$, a row-major list of rational entries, and a rational radius $r$. It is valid exactly when the list has $n^2$ entries, its square matrix $B$ has nonzero determinant, and $r>0$.
--
--   The input codec serializes every matrix entry separately as binary rational fields. Invalid raw records have defined parsing behavior but belong to neither promise branch. Dimension zero is retained: its unique lattice has radius zero.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), Definition 1.1, printed p. 1 / PDF p. 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf

import Definitions.Def_EuclideanCRHardness_Covering_Wire

namespace EuclideanCRHardness.Covering

/-- Dense row-major rational input; validity is separate from the raw record. -/
structure CRInput where
  n : ℕ
  entries : List ℚ
  radius : ℚ
  deriving DecidableEq

def CRInput.basis (I : CRInput) : Matrix (Fin I.n) (Fin I.n) ℚ :=
  fun i j => I.entries[i.val * I.n + j.val]?.getD 0

def CRInput.Valid (I : CRInput) : Prop :=
  I.entries.length = I.n * I.n ∧ I.basis.det ≠ 0 ∧ 0 < I.radius

def encodeCR (I : CRInput) : List Bool :=
  wireEncode ((I.n : ℤ) :: ratFields I.radius ++ I.entries.flatMap ratFields)
def decodeCR (bits : List Bool) : Option CRInput := do
  let n :: fields ← wireDecode bits | none
  if n < 0 then none else do
    let (r, rest) ← readRat fields
    let qs ← readRats rest
    return ⟨n.toNat, qs, r⟩

def matrixInput {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (r : ℚ) : CRInput :=
  ⟨n, (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => B i j)), r⟩

end EuclideanCRHardness.Covering


