-- Prove2me | Definitions.Def_SmoothedPlanted_FFK_Encoding
-- name    : SmoothedPlanted_FFK_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:32:34.397369+00:00
-- url     : https://prove2.me/theorems/9972fe42-6a5e-4a1d-ad6b-17905d0ac0ca
-- title:
--   Finite binary encoding of the algorithm input
-- statement:
--   The observable input consists of $n,k,d$ and the constraint relations, where $d=\lfloor\Delta\rfloor_+$. Encode the integers in binary, each terminated by a third alphabet symbol, then append the $n^2q^2$ Boolean relation entries in row-major order. Diagonal entries are fixed unrestricted constraints; retaining them and both orientations is harmless quadratic padding. The exact length is $|\mathrm{bits}(n)|+|\mathrm{bits}(k)|+|\mathrm{bits}(d)|+3+n^2q^2$. The encoding is injective: the headers delimit the integers and the table determines each pair relation. An output is a Boolean list, with bit $i$ indicating membership of vertex $i$; the goal requires exactly $n$ output bits. The alphabet size is fixed before choosing the machine. No hidden model parameter is an input.
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Finite binary encoding of the algorithm input, printed p. 24 (PDF p. 26), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_CSP
import Mathlib.Computability.TuringMachine.Computable

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

/-- Observable input only: no planted set, assignment, Pi, δ, κ or η. -/
structure RecoveryInput (q : ℕ) where
  n : ℕ
  k : ℕ
  budget : ℕ
  labels : CSP (Fin n) q
/-- Binary digits over a three-symbol alphabet, terminated by symbol 2. -/
def encodeNat (n : ℕ) : List (Fin 3) :=
  (n.bits.map (fun b => if b then 1 else 0)) ++ [2]
/-- Row-major relation bits and explicit binary integer headers. -/
def encodeInput {q : ℕ} (x : RecoveryInput q) : List (Fin 3) :=
  encodeNat x.n ++ encodeNat x.k ++ encodeNat x.budget ++
  (List.finRange x.n).flatMap (fun i => (List.finRange x.n).flatMap (fun j =>
    (List.finRange q).flatMap (fun a => (List.finRange q).map (fun b =>
      if allows x.labels i j a b then 1 else 0))))
/-- The output bit at index i indicates membership of variable i. -/
def outputSet (n : ℕ) (bits : List Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => bits[i.val]?.getD false)

end SmoothedPlanted.FFK


