-- Prove2me | Definitions.Def_HardyCapsetBooleanVerifier20261020
-- name    : HardyCapsetBooleanVerifier20261020
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-20T16:17:25.155991+00:00
-- url     : https://prove2.me/theorems/d9c1dc4f-0f5f-4a09-9096-2f33a593eb0b
-- title:
--   HardyCapsetBooleanVerifier20261020
-- statement:
--   Boolean evaluation of all geometric blocking witnesses, row patterns, sparse covers and strict integer costs. The packed-data variant reads the same explicit pair witnesses directly.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBinaryStorage20261020
set_option autoImplicit false
namespace HardyCapset20261020.Cert

def lineB (a b c : ℕ) : Bool :=
  (List.range 8).all (fun i => (digit a i + digit b i + digit c i) % 3 == 0)

def fixedB (c : Certificate) (a : ℕ) : Bool :=
  decide (a < baseArray.size) && !(dotCode c.normal (baseAt a) == c.level)

def blockB (c : Certificate) (q : ℕ) (ab : ℕ × ℕ) : Bool :=
  if ab.1 < baseArray.size then
    if ab.1 = ab.2 then fixedB c ab.1 && (q == baseAt ab.1)
    else fixedB c ab.1 && fixedB c ab.2 && !(baseAt ab.1 == baseAt ab.2) &&
      lineB (baseAt ab.1) (baseAt ab.2) q
  else decide (ab.1 - baseArray.size < c.pool.size) &&
    (entry c.pool (ab.1 - baseArray.size) == q)

def edgeB (c : Certificate) (r : Row) (e : Edge) : Bool :=
  decide (e.left < r.vars.size) && decide (e.right < r.vars.size) &&
  fixedB c e.anchor && !(rowPoint c r e.left == rowPoint c r e.right) &&
  lineB (rowPoint c r e.left) (rowPoint c r e.right) (baseAt e.anchor)

def tripleB (c : Certificate) (r : Row) (e : Triple) : Bool :=
  decide (e.first < r.vars.size) && decide (e.second < r.vars.size) &&
  decide (e.third < r.vars.size) &&
  !(rowPoint c r e.first == rowPoint c r e.second) &&
  !(rowPoint c r e.first == rowPoint c r e.third) &&
  !(rowPoint c r e.second == rowPoint c r e.third) &&
  lineB (rowPoint c r e.first) (rowPoint c r e.second) (rowPoint c r e.third)

def assignments : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (assignments n).flatMap (fun xs => [false :: xs, true :: xs])

def readBit (xs : List Bool) (i : ℕ) : Bool := xs[i]?.getD false

def legalB (r : Row) (xs : List Bool) : Bool :=
  r.edges.toList.all (fun e => !(readBit xs e.left && readBit xs e.right)) &&
  r.triples.toList.all (fun e =>
    !(readBit xs e.first && readBit xs e.second && readBit xs e.third))

def selectedCost (r : Row) (xs : List Bool) : ℕ :=
  ((List.range r.vars.size).map (fun i => if readBit xs i then entry r.coeff i else 0)).sum

def patternB (r : Row) : Bool :=
  (assignments r.vars.size).all (fun xs => !legalB r xs || decide (selectedCost r xs ≤ r.bound))

def rowB (c : Certificate) (r : Row) : Bool :=
  (r.coeff.size == r.vars.size) &&
  r.vars.toList.all (fun j => decide (j < c.pool.size)) &&
  r.edges.toList.all (edgeB c r) && r.triples.toList.all (tripleB c r) && patternB r

def localCoverB (c : Certificate) (j : ℕ) : Bool :=
  let l := c.coverRows[j]!.toList
  decide l.Nodup && l.all (fun r => decide (r < c.rows.size)) &&
    decide (c.denominator ≤ (l.map (fun r => c.rows[r]!.weight * coefficient c.rows[r]! j)).sum)

def verifyB (c : Certificate) : Bool :=
  decide (c.normal < 6561) && decide (c.level < 3) && decide (0 < c.denominator) &&
  c.pool.toList.all (fun q => decide (q < 6561)) &&
  (c.blockers.size == 6561) &&
  (List.range 6561).all (fun q => blockB c q c.blockers[q]!) &&
  c.rows.toList.all (rowB c) && (c.coverRows.size == c.pool.size) &&
  (List.range c.pool.size).all (localCoverB c) &&
  decide (cost c < c.denominator * (deletedCount c + 1))

def verifyDataB (c : Certificate) (chunks : Array Nat) : Bool :=
  decide (c.normal < 6561) && decide (c.level < 3) && decide (0 < c.denominator) &&
  c.pool.toList.all (fun q => decide (q < 6561)) &&
  (6561 == 6561) &&
  (List.range 6561).all (fun q => blockB c q (binaryPair chunks q)) &&
  c.rows.toList.all (rowB c) && (c.coverRows.size == c.pool.size) &&
  (List.range c.pool.size).all (localCoverB c) &&
  decide (cost c < c.denominator * (deletedCount c + 1))

end HardyCapset20261020.Cert


