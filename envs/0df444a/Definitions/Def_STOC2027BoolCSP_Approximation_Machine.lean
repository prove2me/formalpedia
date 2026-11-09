-- Prove2me | Definitions.Def_STOC2027BoolCSP_Approximation_Machine
-- name    : STOC2027BoolCSP_Approximation_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:18.475023+00:00
-- url     : https://prove2.me/theorems/65bf578c-e02d-4175-a6c0-7b070063eac8
-- title:
--   Finite randomized bit machines, bounded halting, and the law of a seed function
-- statement:
--   A **finite randomized bit machine** is a multi-stack Turing machine in Mathlib's `Turing.FinTM2` model with finitely many stacks, labels and internal states, a finite alphabet on every stack, a bit alphabet on its input stack and its output stack, and one further stack holding the random tape: a finite word of unbiased bits, of which the top is read next. A deterministic computation is a run on the empty tape.
--
--   The machine is started with the input word on its input stack and the random tape on its tape stack, all other stacks empty. It **halts within $T$ steps with output $w$** if after at most $T$ applications of its transition function it reaches a configuration with no current label and its output stack then reads $w$. Runs are deterministic, so this output is unique.
--
--   For a rational-valued function $s\mapsto Z(s)$ of $b$ random bits, its **law** is the probability measure on $\mathbb R$ that puts mass $2^{-b}$ on $Z(s)$ for every $s\in\{0,1\}^b$.
--
--   This is the ordinary finite-string randomized Turing computation of Section 7: time is the number of machine steps, and randomness is a finite word of unbiased bits whose length is part of the resource bound.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 12 (PDF 15), Section 7 (implementation on a randomized Turing machine with finitely many random bits)

import Mathlib

namespace STOC2027BoolCSP.Approximation

/-- A finite randomized bit machine: Mathlib's multi-stack Turing machine `Turing.FinTM2`
(finitely many stacks, labels and internal states), with every stack alphabet finite, a bit
alphabet on the input stack `k₀` and on the output stack `k₁`, and one further stack `kCoin`
holding the unread part of the random tape (its top is the next unbiased bit). A deterministic
computation is a run with the empty random tape. -/
structure CoinMachine where
  tm : Turing.FinTM2
  finiteAlphabet : ∀ k : tm.K, Finite (tm.Γ k)
  inputAlphabet : tm.Γ tm.k₀ ≃ Bool
  outputAlphabet : tm.Γ tm.k₁ ≃ Bool
  kCoin : tm.K
  coin_ne_input : kCoin ≠ tm.k₀
  coin_ne_output : kCoin ≠ tm.k₁
  coinAlphabet : tm.Γ kCoin ≃ Bool

namespace CoinMachine

/-- The initial configuration on an input word and a random tape: the input on stack `k₀` (first
bit on top), the tape on stack `kCoin` (first bit on top), all other stacks empty. -/
def initCfg (M : CoinMachine) (input tape : List Bool) : M.tm.Cfg where
  l := some M.tm.main
  var := M.tm.initialState
  stk k :=
    if h₀ : k = M.tm.k₀ then h₀ ▸ input.map M.inputAlphabet.symm
    else if hc : k = M.kCoin then hc ▸ tape.map M.coinAlphabet.symm
    else []

/-- The configuration after `s` steps of the machine's own transition function `step`
(`none` once the run has stepped past a halting configuration). -/
def cfgAt (M : CoinMachine) (input tape : List Bool) (s : ℕ) : Option M.tm.Cfg :=
  (fun o => o.bind M.tm.step)^[s] (some (M.initCfg input tape))

/-- On this input and random tape the machine reaches a halting configuration (no current
label) within `T` steps, and its output stack then reads `out` (top first). Runs are
deterministic, so the halting configuration, and hence `out`, is unique. -/
def HaltsWithin (M : CoinMachine) (input tape : List Bool) (T : ℕ) (out : List Bool) : Prop :=
  ∃ (s : ℕ) (c : M.tm.Cfg), s ≤ T ∧ M.cfgAt input tape s = some c ∧ c.l = none ∧
    (c.stk M.tm.k₁).map M.outputAlphabet = out

end CoinMachine

/-- The law on `ℝ` of a rational-valued function of `b` unbiased random bits: the image of the
uniform distribution on `{0,1}^b` (each seed has mass `2^{-b}`). -/
noncomputable def seedLaw (b : ℕ) (out : (Fin b → Bool) → ℚ) : MeasureTheory.Measure ℝ :=
  ∑ s : Fin b → Bool, ((2 : ENNReal) ^ b)⁻¹ • MeasureTheory.Measure.dirac ((out s : ℚ) : ℝ)

end STOC2027BoolCSP.Approximation


