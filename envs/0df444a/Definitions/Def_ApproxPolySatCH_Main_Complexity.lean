-- Prove2me | Definitions.Def_ApproxPolySatCH_Main_Complexity
-- name    : ApproxPolySatCH_Main_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:08:10.305017+00:00
-- url     : https://prove2.me/theorems/607a0ef6-2b7a-4d29-9abe-614ba2a76d43
-- title:
--   Finite-machine polynomial time, strict majority and the counting hierarchy
-- statement:
--   A language is a set of finite binary words. A machine is the published finite multitape oracle Turing machine, with its auxiliary and guess tapes empty. Writing, movement and construction of queries take physical machine steps. A clock has the form $c(N+1)^d$, with its constants fixed before the input. Fair random bits occupy a polynomial-length read-only tape. All branches halt with a Boolean output within the clock.
--
--   The polynomial-time class is the deterministic oracle-machine class. PP uses strict majority among all seeds of the specified length, and
--   $$C_0P=P,\qquad C_{j+1}P=\bigcup_{A\in C_jP}PP^A,\qquad CH=\bigcup_{j\ge0}C_jP.$$
--   Randomized reductions have two-sided error at most $1/3$. Function reductions write their outputs on the charged output tape.
--
--   This interface expresses ordinary uniform bit complexity and gives no access to algebraic coefficients beyond the encoded input.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), §§2–5, pp.7,14,23–26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf

import Mathlib
import Definitions.Def_NKtLB_Machine

set_option autoImplicit false

namespace ApproxPolySatCH.Main
abbrev Word := List Bool
abbrev Language := Set Word

def clock (c d N : ℕ) : ℕ := c * (N + 1) ^ d

noncomputable def Run (M : NKtLB.Machine) (A : Language) (x r : Word) (t : ℕ) :=
  M.run A ⟨x, [], [], r⟩ t

def Outputs (M : NKtLB.Machine) (A : Language) (x r : Word) (t : ℕ) (b : Bool) : Prop :=
  M.HaltsWith A ⟨x, [], [], r⟩ t (NKtLB.bitsSym [b])

def TotalClock (M : NKtLB.Machine) (A : Language) (c d a b : ℕ) : Prop :=
  ∀ x : Word, ∀ r : Fin (clock a b x.length) → Bool,
    ∃ z : Bool, Outputs M A x (List.ofFn r) (clock c d x.length) z

noncomputable def acceptingSeeds (M : NKtLB.Machine) (A : Language) (x : Word)
    (t q : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun r : Fin q → Bool => Outputs M A x (List.ofFn r) t true)).card

def InOracleP (A L : Language) : Prop :=
  ∃ (M : NKtLB.Machine) (c d : ℕ), ∀ x : Word, ∃ z : Bool,
    Outputs M A x [] (clock c d x.length) z ∧ (z = true ↔ x ∈ L)

def InOraclePP (A L : Language) : Prop :=
  ∃ (M : NKtLB.Machine) (c d a b : ℕ), TotalClock M A c d a b ∧
    ∀ x : Word, x ∈ L ↔ 2 ^ clock a b x.length <
      2 * acceptingSeeds M A x (clock c d x.length) (clock a b x.length)

def CHLevel : ℕ → Language → Prop
  | 0, L => InOracleP ∅ L
  | j + 1, L => ∃ A : Language, CHLevel j A ∧ InOraclePP A L

def InCH (L : Language) : Prop := ∃ j : ℕ, CHLevel j L

/-- Two-sided error at most one third; every branch halts within the fixed clock. -/
def RandomizedDecider (M : NKtLB.Machine) (A L : Language) (c d a b : ℕ) : Prop :=
  TotalClock M A c d a b ∧ ∀ x : Word,
    let yes := acceptingSeeds M A x (clock c d x.length) (clock a b x.length)
    (x ∈ L → 2 * 2 ^ clock a b x.length ≤ 3 * yes) ∧
    (x ∉ L → 3 * yes ≤ 2 ^ clock a b x.length)

def RandomizedTuringReduction (L A : Language) : Prop :=
  ∃ (M : NKtLB.Machine) (c d a b : ℕ), RandomizedDecider M A L c d a b

/-- A function must be computed on the ordinary charged output tape. -/
def FunctionInP (f : Word → Word) : Prop :=
  ∃ (M : NKtLB.Machine) (c d : ℕ), ∀ x : Word,
    M.Computes (clock c d x.length) x (f x)

def ManyOneReduction (L A : Language) : Prop :=
  ∃ f : Word → Word, FunctionInP f ∧ ∀ x, x ∈ L ↔ f x ∈ A
end ApproxPolySatCH.Main


