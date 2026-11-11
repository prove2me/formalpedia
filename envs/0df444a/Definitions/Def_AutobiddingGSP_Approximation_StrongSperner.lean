-- Prove2me | Definitions.Def_AutobiddingGSP_Approximation_StrongSperner
-- name    : AutobiddingGSP_Approximation_StrongSperner
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:26:56.988104+00:00
-- url     : https://prove2.me/theorems/ec04f322-0983-4d50-895d-7ae5e88e8f59
-- title:
--   The 2D Strong Sperner search problem
-- statement:
--   An instance is $b\ge1$ and a Boolean circuit $C$ (published `ConstrSOSP.Circuit`: ∧, ∨, ¬, gates in topological order) with $2b$ inputs and two outputs, read as a labeling $C:\{0,\dots,2^b-1\}^2\to\{0,1\}^2$ (input: the bits of $p_1$ then of $p_2$, most significant first), satisfying for every point and coordinate $i$: $p_i=0\Rightarrow C_i(p)=1$ and $p_i=2^b-1\Rightarrow C_i(p)=0$. An answer is two points $p,q$ with $\|p-q\|_\infty\le1$ and $C_i(p)\ne C_i(q)$ for both $i$.
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Definition 6.1, p. 25 (PDF 25)

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_ConstrSOSP_Circuit
import Definitions.Def_ConstrSOSP_Circuit_eval
import Definitions.Def_ConstrSOSP_encCircuit

namespace AutobiddingGSP.Approximation

open QAlgorithms.LocalHamiltonian

/-- A Boolean circuit (the public `ConstrSOSP.Circuit`: ∧, ∨ of fan-in two and ¬, gates in
topological order) with `2b` input bits and two output bits: every gate reads earlier wires, there
are exactly two output wires, and they exist. -/
def SSCircuitWF (b : ℕ) (C : ConstrSOSP.Circuit) : Prop :=
  C.n = 2 * b ∧
    (∀ k (hk : k < C.gates.length),
      match C.gates[k] with
      | ConstrSOSP.Gate.andG i j => i < C.n + k ∧ j < C.n + k
      | ConstrSOSP.Gate.orG i j => i < C.n + k ∧ j < C.n + k
      | ConstrSOSP.Gate.notG i => i < C.n + k) ∧
    C.outs.length = 2 ∧ ∀ o ∈ C.outs, o < C.n + C.gates.length

/-- The `b` bits of a grid coordinate `p ∈ {0, …, 2^b − 1}`, most significant first. -/
def gridBits (b p : ℕ) : List Bool := (List.range b).map (fun j => p.testBit (b - 1 - j))

/-- The labeling `C_i(p) ∈ {0, 1}` (`true` = 1) of the point `p = (p₁, p₂)`, `i ∈ {0, 1}` for the
paper's `i ∈ {1, 2}`: output bit `i` of `C` on the input bits of `p₁` followed by those of `p₂`
(Definition 6.1, p. 25). -/
def ssLabel (b : ℕ) (C : ConstrSOSP.Circuit) (p : ℕ × ℕ) (i : Fin 2) : Bool :=
  (C.eval (gridBits b p.1 ++ gridBits b p.2)).getD i.val false

/-- The boundary conditions of Definition 6.1 (p. 25): for every grid point `p` and coordinate `i`,
`p_i = 0 ⟹ C_i(p) = 1` and `p_i = 2^b − 1 ⟹ C_i(p) = 0`. -/
def SSBoundary (b : ℕ) (C : ConstrSOSP.Circuit) : Prop :=
  ∀ p : ℕ × ℕ, p.1 < 2 ^ b → p.2 < 2 ^ b → ∀ i : Fin 2,
    ((if i.val = 0 then p.1 else p.2) = 0 → ssLabel b C p i = true) ∧
    ((if i.val = 0 then p.1 else p.2) = 2 ^ b - 1 → ssLabel b C p i = false)

/-- **2D Strong Sperner** (Definition 6.1, p. 25), as a finite-string search problem. An instance
is `b ≥ 1` and a Boolean circuit `C` with `2b` input bits and two output bits satisfying the
boundary conditions, written `encBin b ++ encCircuit C`. An answer is two grid points
`p, q ∈ {0, …, 2^b − 1}²` with `‖p − q‖_∞ ≤ 1` and `C_i(p) ≠ C_i(q)` for **both** `i`, written
`encBin p₁ ++ encBin p₂ ++ encBin q₁ ++ encBin q₂`. -/
def StrongSperner2D : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (b : ℕ) (C : ConstrSOSP.Circuit), 1 ≤ b ∧ SSCircuitWF b C ∧ SSBoundary b C ∧
    s = encBin b ++ ConstrSOSP.encCircuit C
  answer s t := ∃ (b : ℕ) (C : ConstrSOSP.Circuit), 1 ≤ b ∧ SSCircuitWF b C ∧ SSBoundary b C ∧
    s = encBin b ++ ConstrSOSP.encCircuit C ∧
    ∃ p q : ℕ × ℕ, p.1 < 2 ^ b ∧ p.2 < 2 ^ b ∧ q.1 < 2 ^ b ∧ q.2 < 2 ^ b ∧
      Nat.dist p.1 q.1 ≤ 1 ∧ Nat.dist p.2 q.2 ≤ 1 ∧
      (∀ i : Fin 2, ssLabel b C p i ≠ ssLabel b C q i) ∧
      t = encBin p.1 ++ encBin p.2 ++ encBin q.1 ++ encBin q.2

end AutobiddingGSP.Approximation


