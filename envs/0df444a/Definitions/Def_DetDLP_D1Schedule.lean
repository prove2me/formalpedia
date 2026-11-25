-- Prove2me | Definitions.Def_DetDLP_D1Schedule
-- name    : DetDLP_D1Schedule
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:14:01.565808+00:00
-- url     : https://prove2.me/theorems/5a02b96f-b56d-49cb-9e93-2ed417cb762f
-- title:
--   Uniform binary generator for the Appendix D recursion schedule
-- statement:
--   Given a scale, edge count and maximum degree, the generator chooses either direct contraction or a schedule with geometrically decreasing widths. The raw generator reads the scale and graph from the framed instance, counts incidences, and returns the framed schedule over the polynomial X.

import Definitions.Def_DetDLP_D1Radius
import Definitions.Def_DetDLP_W1_Queries
import Definitions.Def_DetDLP_W5_M6Sort

set_option autoImplicit false
namespace DetDLP.D1
open AppendixD4 Groundwork OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace DetDLP_W1_Queries

def threshold (C : ℕ) := 2^48 * (C+2)^4
def rootScan (r : ℕ) := ((List.range r).filter fun j => (j+1)*(j+1) ≤ r).length
def horizon (b r : ℕ) := b / max 1 (rootScan r) + 1
def fuel (m : ℕ) := m.bits.length + 1
def depth (m H : ℕ) := ((List.range (fuel m)).filter fun d => H < m / 8^(min d (fuel m))).length
def width (m r d : ℕ) := (r / 131072) / 2^(min d (fuel m))
def widths (m r D : ℕ) := (List.range D).map (width m r)
def shift (us : List ℕ) (d : ℕ) := 2 * (us.take (d+1)).sum
def kappa (m : ℕ) := 4 * (m.bits.length + 2)
def trivialSchedule (nE : ℕ) : Schedule := ⟨nE,0,0,0,Fin.elim0,Fin.elim0,1⟩
def fullSchedule (b r m H : ℕ) : Schedule :=
  let D := depth m H
  ⟨H,0,D,b/2^r,fun d => width m r d.val,fun d => shift (widths m r D) d.val,kappa m⟩
def makeSchedule (C b nE deg : ℕ) : Schedule :=
  let r := radiusScan (b,deg)
  let H := horizon b r
  if r < threshold C ∨ nE ≤ H then trivialSchedule nE else fullSchedule b r (C*b) H

def field4 (w : List Bool) := third (more w)
def peak (ns : List ℕ) := ns.foldl max 0
def degreeRaw (graph : List Bool) :=
  let es := w5_M6Sort.decode (field4 graph)
  peak ((List.range (third graph).length).map fun v => es.count v)
def scheduleWord (H D cap k : ℕ) (us as_ : List ℕ) := Encoding.encodeList id
  [encodeNatListBin [H,0,D,cap,k],encodeNatListBin us,encodeNatListBin as_,[false]]
def scheduleCore (C b nE deg : ℕ) :=
  let r := radiusScan (b,deg)
  let H := horizon b r
  let m := C*b
  let D := depth m H
  let us := widths m r D
  if r < threshold C ∨ nE ≤ H then scheduleWord nE 0 0 1 [] [] else
    scheduleWord H D (b/2^r) (kappa m) us ((List.range D).map (shift us))
def scheduleRaw (C : ℕ) (w : List Bool) :=
  let g := second w
  scheduleCore C (PolyT.bval (third w)) (PolyT.bval (second g)) (degreeRaw g)

end DetDLP.D1


