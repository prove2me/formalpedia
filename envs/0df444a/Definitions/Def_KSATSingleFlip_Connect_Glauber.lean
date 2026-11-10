-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_Glauber
-- name    : KSATSingleFlip_Connect_Glauber
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:06:40.240917+00:00
-- url     : https://prove2.me/theorems/4dae628b-f313-46fb-8fcd-779f5e8c4327
-- title:
--   Glauber dynamics on a formula driven by a shared update sequence
-- statement:
--   Section 7.1 (p. 51): at each step choose a variable uniformly and resample its value uniformly among the values keeping $\Psi$ satisfied; coupled walks use the same update sequence. An update is a pair $(v,b)\in V\times\mathrm{Bool}$; the update sequence is i.i.d. uniform. `glauberStep Ψ x (v,b)` sets $v$ to $b$ if that keeps $\Psi$ satisfied, else to $\neg b$ if that does, else leaves $x$ (never the case from a satisfying assignment). If both values are allowed the new value is the fair bit $b$; if one is allowed it is that one — exactly the uniform resampling, and coupled walks reading the same $(v,b)$ make the same choice whenever their allowed sets agree. `glauberRun` runs a list of updates, `glauberState Ψ x s` the $t$ updates $s : \mathrm{Fin}\ t\to V\times\mathrm{Bool}$.
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), §7.1 step (2), printed p. 51 (PDF 53); Lemma 7.7 (p. 55)

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_Model

noncomputable section

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-! # Glauber dynamics driven by a shared update sequence

Wang, Yin, Yu, Zhang (2026), arXiv:2611.05981, §7.1 (printed p. 51, step (2)): "At each step, we
choose a variable uniformly at random and, keeping all other variables fixed, resample its value
uniformly subject to satisfying Φ_i. All walks use the same random update sequence."

An update is a pair `(v, b)`; the update sequence is i.i.d. uniform on `V × Bool`. The update sets
`v` to `b` if that keeps `Ψ` satisfied, and otherwise to `!b` if that does (if both values are
allowed the new value is the uniform bit `b`; if one is allowed it is that one). From a satisfying
assignment the current value of `v` is always allowed, so the walk stays in `Ω_Ψ` and this is
exactly the uniform resampling of `v` among its allowed values. -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- One Glauber update `(v, b)` on `Ψ` from `x`. -/
def glauberStep (Ψ : GFormula V) (x : V → Bool) (u : V × Bool) : V → Bool :=
  if FSat (Function.update x u.1 u.2) Ψ then Function.update x u.1 u.2
  else if FSat (Function.update x u.1 (!u.2)) Ψ then Function.update x u.1 (!u.2)
  else x

/-- The state after running the updates `seq` (in order) on `Ψ` from `x`. -/
def glauberRun (Ψ : GFormula V) (x : V → Bool) (seq : List (V × Bool)) : V → Bool :=
  seq.foldl (glauberStep Ψ) x

/-- The `t`-step Glauber state on `Ψ` from `x` under the update sequence `s : Fin t → V × Bool`. -/
def glauberState {t : ℕ} (Ψ : GFormula V) (x : V → Bool) (s : Fin t → V × Bool) : V → Bool :=
  glauberRun Ψ x (List.ofFn s)

end KSATSingleFlip.Connect


