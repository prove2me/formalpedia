-- Prove2me | Definitions.Def_DetDLP_F9A2_BMul
-- name    : DetDLP_F9A2_BMul
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T03:06:48.738366+00:00
-- url     : https://prove2.me/theorems/1445a080-df47-46c0-8e00-2373d83c89e1
-- title:
--   Uniform multiplication of residual coefficient tables
-- statement:
--   A single bit-string algorithm parses the modulus, dimensions, monic relation and two row-major coefficient tables. It computes all entries of the truncated product using modular companion shifts.
-- source:
--   DetDLP F9A2-v2, uniform multiplication wire specification

import Definitions.Def_DetDLP_W5_M6Sort
import Definitions.Def_DetDLP_ResidualScalarOracle
import Definitions.Def_DetDLP_W1_Queries

set_option autoImplicit false
namespace DetDLP.F9A2
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP_W1_Queries (first more)

/-- One row for each successive z power, with the U index varying fastest. -/
def flatten {ell d : ℕ} (a : Fin ell → Fin d → ℕ) : List ℕ :=
  (List.ofFn fun r : Fin ell => List.ofFn (a r)).flatten

/-- Shift by U and eliminate the leading term using the monic relation. -/
def step (m : ℕ) (D c v : List ℕ) := D.map fun k =>
  (m + (0 :: v).getD k 0 - v.getD (D.length-1) 0 * c.getD k 0 % m) % m

/-- A fuel list provides a unary bound on the power. -/
def power (m : ℕ) (D c fuel : List ℕ) :=
  if m = 0 then [] else fuel.foldl (fun v _ => step m D c v)
    (D.map fun k => if k = 0 then 1 else 0)

def rowsum (I : List ℕ) (g : ℕ → ℕ) := (I.map g).sum

def coeff (m : ℕ) (E D c a b : List ℕ) (t k : ℕ) :=
  (rowsum E fun r => rowsum E fun s => if r+s = t then
    rowsum D fun i => rowsum D fun j =>
      a.getD (r*D.length+i) 0 * b.getD (s*D.length+j) 0 *
        (power m D c ((D++D).take (i+j))).getD k 0 else 0) % m

def table (m : ℕ) (E D c a b : List ℕ) :=
  E.flatMap fun t => D.map fun k => coeff m E D c a b t k

/-- One wire program for every modulus, truncation order, and degree. -/
def bMulRaw (w : List Bool) : List Bool :=
  let w₁ := more w
  let w₂ := more w₁
  let w₃ := more w₂
  let w₄ := more w₃
  let w₅ := more w₄
  encodeNatListBin (table (Groundwork.PolyT.bval (first w))
    (List.range (first w₁).length) (List.range (first w₂).length)
    (w5_M6Sort.decode (first w₃)) (w5_M6Sort.decode (first w₄)) (w5_M6Sort.decode (first w₅)))

end DetDLP.F9A2


