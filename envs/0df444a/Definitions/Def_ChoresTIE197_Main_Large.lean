-- Prove2me | Definitions.Def_ChoresTIE197_Main_Large
-- name    : ChoresTIE197_Main_Large
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T02:17:19.176645+00:00
-- url     : https://prove2.me/theorems/b123cda1-e711-42ea-9e1e-02319b7c0fc7
-- title:
--   Normalized costs, all hard-agent cases and the large-n mechanism
-- statement:
--   Each cost row is divided by the derived lower bound $L_i=\max\{c_i(M)/n,c_{i,(1)},2c_{i,(n+1)}\}$. The normalized row determines its excess, $\Gamma_i$, and hard set $Q=\{i:\Gamma_i>39/20\}$. No property of these quantities is supplied as a hypothesis.
--
--   The intermediate matrix is uniform for $Q=\varnothing$. For at least two hard agents, public consecutive pairs and at most one final triple exchange the fractions prescribed on pp.19–20. All pairs share one selection bit; a triple has an independent uniform three-way selection. When exactly one agent is hard, transfers use the strict $47/50$ threshold, $\Delta=1/(n(n-1))$, and the computed helper parameters $a_j,b$. The PDF's term $(3/100)n$ lies inside the helper sum defining the numerator of $b$.
--
--   The complete mechanism publicly pads to more than $n$ chores, normalizes, samples one of the one, two, three or six intermediate matrices, applies the operational sorted-slot rounding, and removes dummies. Feasibility, denominator positivity, uniform average fractions and the $197/100$ bound are conclusions to prove.
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), §§4.2–4.6, printed p.23, PDF p.23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Rounding

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

def lowerBound {n m : ℕ} (c : Profile n m) (i : Fin n) : ℝ :=
  max (cost (c i) univ / n) (max (kth (c i) 1) (2 * kth (c i) (n+1)))

def normalized {n m : ℕ} (c : Profile n m) : Profile n m :=
  fun i e => c i e / Real.toNNReal (lowerBound c i)

def excess {n m : ℕ} (c : Profile n m) (i : Fin n) : ℝ :=
  cost (c i) (top (c i) n) - n * kth (c i) (n+1)

def gamma {n m : ℕ} (c : Profile n m) (i : Fin n) : ℝ :=
  kth (c i) 1 + (cost (c i) univ - excess c i) / n

def hard {n m : ℕ} (c : Profile n m) : Finset (Fin n) :=
  univ.filter (fun i => (39:ℝ)/20 < gamma c i)

def smallTop {n m : ℕ} (c : Profile n m) (i : Fin n) := top (c i) (n/4)

def pairFraction {n m : ℕ} (c : Profile n m) (selected other i : Fin n) (e : Fin m) : ℝ :=
  if e ∈ smallTop c selected ∪ smallTop c other then
    if i = selected then 2/(n:ℝ) else 0
  else if i = selected then 1/(2*(n:ℝ)) else 3/(2*(n:ℝ))

def tripleFraction {n m : ℕ} (c : Profile n m) (a b d i : Fin n) (e : Fin m) : ℝ :=
  let U := smallTop c a ∪ smallTop c b
  let V := smallTop c a ∪ smallTop c d
  if i = a then 3/(2*(n:ℝ))*((if e ∈ U then 1 else 0)+(if e ∈ V then 1 else 0))
  else if i = b then 3/(2*(n:ℝ))*(if e ∉ U then 1 else 0)
  else 3/(2*(n:ℝ))*(if e ∉ V then 1 else 0)

/-- Public consecutive pairs and, for odd hard-set size, one final triple.
The same selection bit is shared by all pairs. -/
def grouped {n m : ℕ} [NeZero n] (c : Profile n m) (s : ℕ) : Fraction n m :=
  let Q := (hard c).sort (· ≤ ·)
  let hasTriple := Q.length % 2 = 1
  let pairEnd := Q.length - if hasTriple then 3 else 0
  let member := fun t => Q[t]?.getD 0
  fun i e =>
    if i ∉ hard c then 1/(n:ℝ)
    else
      let pos := Q.idxOf i
      if hasTriple ∧ pairEnd ≤ pos then
        let t := s % 3
        tripleFraction c (member (pairEnd+t)) (member (pairEnd+(t+1)%3))
          (member (pairEnd+(t+2)%3)) i e
      else
        let bit := (if hasTriple then s/3 else s) % 2
        let start := 2*(pos/2)
        pairFraction c (member (start+bit)) (member (start+(1-bit))) i e

def singletonH {n m : ℕ} (c : Profile n m) (a : Fin n) : Finset (Fin m) :=
  univ.filter (fun e => (47:ℝ)/50 < (c a e : ℝ))

def helperA {n m : ℕ} (c : Profile n m) (a j : Fin n) : ℝ :=
  let t := ((singletonH c a) ∩ top (c j) n).card
  (t:ℝ) / ((n:ℝ)-t)

/-- The PDF p.21 places 0.03*n INSIDE the helper sum. -/
def helperB {n m : ℕ} (c : Profile n m) (a : Fin n) : ℝ :=
  let H := singletonH c a
  (∑ j ∈ univ.erase a, (cost (c a) H - helperA c a j * cost (c a) (top (c j) n \ H)
    + (3:ℝ)/100*n)) /
  (∑ j ∈ univ.erase a, cost (c a) (univ \ (top (c j) n ∪ H)))

def transfer {n m : ℕ} (c : Profile n m) (a j : Fin n) (e : Fin m) : ℝ :=
  let Δ := 1/((n:ℝ)*((n:ℝ)-1))
  if e ∈ singletonH c a then Δ
  else if e ∈ top (c j) n then -helperA c a j*Δ else -helperB c a*Δ

def singletonFraction {n m : ℕ} (c : Profile n m) (a : Fin n) (s : ℕ) : Fraction n m :=
  let sign : ℝ := if s % 2 = 0 then 1 else -1
  fun i e => 1/(n:ℝ) + sign *
    (if i = a then ∑ j ∈ univ.erase a, transfer c a j e else -transfer c a i e)

def intermediateCount {n m : ℕ} (c : Profile n m) : ℕ :=
  let q := (hard c).card
  if q = 0 then 1 else if q = 1 then 2 else
    if q % 2 = 0 then 2 else if q = 3 then 3 else 6

def intermediate {n m : ℕ} [NeZero n] (c : Profile n m) (s : ℕ) : Fraction n m :=
  if (hard c).card = 0 then fun _ _ => 1/(n:ℝ)
  else if (hard c).card = 1 then
    singletonFraction c (firstBy (hard c) (fun i => i.val) 0) s
  else grouped c s

/-- Section 4.6's sampler, all three hard-set cases, followed by sorted slots. -/
def largePadded {n m : ℕ} [NeZero n] : Mechanism n m := fun reports =>
  let c := normalized reports
  (uniformChoice (range (intermediateCount c)) 0).bind
    (fun s => roundSlots c (intermediate c s))

def mechanism4 {n m : ℕ} [NeZero n] : Mechanism n m := fun c =>
  (largePadded (pad (n+1-m) c)).map unpad

end ChoresTIE197.Main


