-- Prove2me | Definitions.Def_DetDLP_D2_Greedy
-- name    : DetDLP_D2_Greedy
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:20:10.88597+00:00
-- url     : https://prove2.me/theorems/c3b392a8-43d1-4abe-b81a-c343f5f44bba
-- title:
--   Boundary-balanced greedy palette scan on encoded graphs
-- statement:
--   Fix vertex colors in index order, minimizing an integer-scaled edge and boundary pair-collision score at each vertex. The score counts oriented endpoint matches and coordinate-wise host matches. Palette enumeration is explicitly bounded by an input field. The output uses coordinate-major order.
-- source:
--   Liu–Zhang–Ren, Deterministic Discrete Logarithms (revised), Section 5.1, Lemma 5.1.

import Definitions.Def_DetDLP_D2_TerminalLabeling
import Definitions.Def_DetDLP_W1_Queries
import Definitions.Def_DetDLP_W5_M6Sort

set_option autoImplicit false
namespace DetDLP.D2.Greedy
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP_W1_Queries
abbrev Edge := ℕ × ℕ

def lastField (x : W) := first (more (more (more x)))

def oriented (s : List Bool) (ep : List ℕ) (j : ℕ) : Edge :=
  let u := ep.getD (2*j) 0
  let v := ep.getD (2*j+1) 0
  if s.getD u false then (v,u) else (u,v)

/-- `p` lists the labels of the already assigned vertices, in vertex order. This
is `radix` times the chance that the projections of two labels agree. -/
def factor (p : List ℕ) (radix place u v : ℕ) :=
  if u = v then radix else if u < p.length ∧ v < p.length then
    if p.getD u 0 / place % radix = p.getD v 0 / place % radix then radix else 0
  else 1

def total {α : Type} (xs : List α) (f : α → ℕ) := (xs.map f).sum

def edgeCost (p : List ℕ) (q : ℕ) (es : List Edge) :=
  total es fun e => total es fun f => factor p q 1 e.1 f.1 * factor p q 1 e.2 f.2

def legCost (p : List ℕ) (places hosts : List ℕ) :=
  total places fun k => total hosts fun u => total hosts fun v => factor p 64 k u v

def energy (p : List ℕ) (q : ℕ) (es : List Edge) (places hosts : List ℕ) (w v : ℕ) :=
  64*w*edgeCost p q es + q*q*v*legCost p places hosts

def best (cost : ℕ → ℕ) (palette : List ℕ) :=
  palette.foldl (fun i j => if cost j < cost i then j else i) 0

def maxOn {α : Type} (xs : List α) (f : α → ℕ) := (xs.map f).foldl max 0

def solve (vertices palette places hosts : List ℕ) (es : List Edge) :=
  let τ := maxOn hosts (fun j => hosts.count j)
  let Δ := maxOn vertices (fun j => (es.filter (fun e => e.1 == j || e.2 == j)).length)
  let w := max 1 (hosts.length * τ)
  let v := es.length * Δ
  vertices.foldl (fun p _ => p ++ [best (fun g => energy (p++[g]) palette.length es places hosts w v) palette]) []

/-- Both input-controlled ranges are bounded on all words, not just valid graph encodings. -/
def run (x : W) : W :=
  let gr := first x
  let sides := third gr
  let ep := w5_M6Sort.decode (lastField gr)
  let es := (List.range (ep.length / 2)).map (oriented sides ep)
  let palette := List.range (third x).length
  let places := (List.range (min (Groundwork.PolyT.bval (second x)) (third x).length)).map fun i => 64^i
  let vertices := List.range sides.length
  let p := solve vertices palette places (w5_M6Sort.decode (lastField x)) es
  encodeNatListBin (places.flatMap fun k => p.map fun g => g / k % 64)

end DetDLP.D2.Greedy


