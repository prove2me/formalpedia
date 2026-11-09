-- Prove2me | Definitions.Def_EuclideanCRHardness_Covering_Parity
-- name    : EuclideanCRHardness_Covering_Parity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:17.908826+00:00
-- url     : https://prove2.me/theorems/1e27e70b-f6af-4837-92a0-e848727dbaa7
-- title:
--   Weighted and unweighted three-variable sign equations
-- statement:
--   An equation names three variable occurrences and a right-hand sign $c$. It is satisfied when $x_ax_bx_d=c$. Occurrences may repeat. An unweighted instance lists such equations; a weighted instance lists equation–rational-weight pairs. A valid weighted list is nonempty, has in-range variable occurrences, has nonnegative weights, and its weights sum to one.
--
--   The unweighted optimum counts satisfied occurrences of equations. The weighted optimum maximizes their total rational weight over all sign assignments. Both lists have explicit binary codecs, which preserve repeated equations and repeated variables.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), Theorem 3.2 and §3 conventions, printed p. 5 / PDF p. 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf

import Definitions.Def_EuclideanCRHardness_Covering_Signed
import Definitions.Def_EuclideanCRHardness_Covering_Quadratic

namespace EuclideanCRHardness.Covering

structure Equation where
  a : ℕ
  b : ℕ
  d : ℕ
  rhs : Bool
  deriving DecidableEq
structure ParityInstance where
  n : ℕ
  eqs : List Equation
  deriving DecidableEq
structure WeightedParity where
  n : ℕ
  eqs : List (Equation × ℚ)
  deriving DecidableEq

def Equation.Valid (n : ℕ) (e : Equation) : Prop := e.a < n ∧ e.b < n ∧ e.d < n

def Equation.Sat {n : ℕ} (e : Equation) (s : Fin n → Bool) : Bool :=
  (((atSign s e.a == atSign s e.b) == atSign s e.d) == e.rhs)

def ParityInstance.Valid (P : ParityInstance) : Prop := ∀ e ∈ P.eqs, e.Valid P.n

def WeightedParity.Valid (P : WeightedParity) : Prop :=
  P.eqs ≠ [] ∧ (∀ e ∈ P.eqs, e.1.Valid P.n ∧ 0 ≤ e.2) ∧ (P.eqs.map Prod.snd).sum = 1

def parityScore (P : ParityInstance) (s : Fin P.n → Bool) : ℕ := (P.eqs.filter (fun e => e.Sat s)).length

def parityOpt (P : ParityInstance) : ℕ := Finset.univ.sup (parityScore P)

def weightedScore (P : WeightedParity) (s : Fin P.n → Bool) : ℚ :=
  (P.eqs.map (fun e => if e.1.Sat s then e.2 else 0)).sum
noncomputable def weightedOpt (P : WeightedParity) : ℝ :=
  sSup (Set.range (fun s : Fin P.n → Bool => (weightedScore P s : ℝ)))

def eqFields (e : Equation) : List ℤ := [e.a,e.b,e.d,if e.rhs then 1 else -1]
def readEq : List ℤ → Option (Equation × List ℤ)
  | a::b::d::c::rest =>
      if a < 0 ∨ b < 0 ∨ d < 0 ∨ (c ≠ 1 ∧ c ≠ -1) then none
      else some (⟨a.toNat,b.toNat,d.toNat,c == 1⟩,rest)
  | _ => none

def readEqs : ℕ → List ℤ → Option (List Equation × List ℤ)
  | 0, xs => some ([],xs)
  | k+1, xs => do
      let (e,rest) ← readEq xs
      let (es,tail) ← readEqs k rest
      return (e::es,tail)
def readWeightedEqs : ℕ → List ℤ → Option (List (Equation × ℚ) × List ℤ)
  | 0, xs => some ([],xs)
  | k+1, xs => do
      let (e,rest) ← readEq xs
      let (q,rest') ← readRat rest
      let (es,tail) ← readWeightedEqs k rest'
      return ((e,q)::es,tail)

def encodeParity (P : ParityInstance) : List Bool :=
  wireEncode ([(P.n : ℤ),(P.eqs.length : ℤ)] ++ P.eqs.flatMap eqFields)
def encodeWeighted (P : WeightedParity) : List Bool :=
  wireEncode ([(P.n : ℤ),(P.eqs.length : ℤ)] ++ P.eqs.flatMap (fun e => eqFields e.1 ++ ratFields e.2))
def decodeParity (bits : List Bool) : Option ParityInstance := do
  let n::k::rest ← wireDecode bits | none
  if n < 0 ∨ k < 0 then none else do
    let (es,tail) ← readEqs k.toNat rest
    if tail.isEmpty then some ⟨n.toNat,es⟩ else none

def decodeWeighted (bits : List Bool) : Option WeightedParity := do
  let n::k::rest ← wireDecode bits | none
  if n < 0 ∨ k < 0 then none else do
    let (es,tail) ← readWeightedEqs k.toNat rest
    if tail.isEmpty then some ⟨n.toNat,es⟩ else none

end EuclideanCRHardness.Covering


