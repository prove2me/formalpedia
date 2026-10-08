-- Prove2me | Definitions.Def_ZhengFedergruenSS_Algorithm_Run
-- name    : ZhengFedergruenSS_Algorithm_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:23.909997+00:00
-- url     : https://prove2.me/theorems/7ee10561-f123-43de-bd46-763c2c0cab6b
-- title:
--   §3, Algorithm (p. 659): the Zheng–Federgruen search for an optimal (s, S) policy as a step function
-- statement:
--   This module encodes the algorithm of §3 (p. 659), started at a minimum point $y^*$ of $G$:
--
--   $$\begin{aligned}
--   &\textbf{Step 0.}\ s:=y^*;\ S_0:=y^*;\ \textbf{repeat } s:=s-1 \textbf{ until } c(s,S_0)\le G(s);\\
--   &\qquad s_0:=s;\ c^0:=c(s_0,S_0);\ S^0:=S_0;\ S:=S^0+1;\\
--   &\textbf{Step 1.}\ \textbf{while } G(S)\le c^0 \textbf{ do}\\
--   &\qquad \textbf{if } c(s,S)<c^0 \textbf{ then } \{S^0:=S;\ \textbf{while } c(s,S^0)\le G(s+1) \textbf{ do } s:=s+1;\ c^0:=c(s,S^0)\};\\
--   &\qquad S:=S+1.
--   \end{aligned}$$
--
--   The state consists of $s$, $S$, $S^0$, $c^0$ and a phase (Step 0, the outer test of Step 1, the inner loop of Step 1, or terminated). One elementary step does the following.
--
--   1. *Step 0*: decrease $s$ by one. If now $c(s,y^*)\le G(s)$, set $c^0:=c(s,y^*)$, $S^0:=y^*$, $S:=y^*+1$ and pass to Step 1.
--   2. *Outer test*: if $G(S)\le c^0$, then either $c(s,S)<c^0$, in which case set $S^0:=S$ and enter the inner loop, or else set $S:=S+1$. If $G(S)>c^0$, terminate.
--   3. *Inner loop*: if $c(s,S^0)\le G(s+1)$, set $s:=s+1$. Otherwise set $c^0:=c(s,S^0)$ and $S:=S+1$, and return to the outer test.
--   4. A terminated state stays terminated.
--
--   The run with budget $n$ returns $(s,S^0,c^0)$ if the algorithm has terminated within $n$ elementary steps, and nothing otherwise.
--
--   **Formalization Note.** The repeat–until loop of Step 0 decrements before it tests, so the first level tested is $y^*-1$. The tests keep the paper's weak and strict inequalities exactly. The variables $S$ and $c^0$ hold placeholder values ($y^*$ and $0$) before Step 0 assigns them, and no step reads them earlier. The run never reports an output it has not reached by terminating.
-- source:
--   Zheng and Federgruen, Finding Optimal (s, S) Policies Is About As Simple As Evaluating a Single Policy, Oper. Res. 39(4):654–665 (1991), DOI 10.1287/opre.39.4.654, p. 659, §3, Algorithm

import Mathlib
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model

namespace ZhengFedergruenSS.Algorithm

/-- Where the algorithm of §3 (p. 659) is: in the `Repeat` loop of Step 0, at the test of the
outer `While` loop of Step 1, inside the inner `While` loop of Step 1, or terminated. -/
inductive Phase
  | step0
  | outer
  | inner
  | done
  deriving DecidableEq

/-- The variables of the algorithm (p. 659): the reorder level `s`, the order-up-to level `S` under
examination, the incumbent order-up-to level `S⁰` (here `S0`) and the incumbent cost `c⁰`
(here `c0`), together with the current `phase`. -/
structure AlgState where
  s : ℤ
  S : ℤ
  S0 : ℤ
  c0 : ℝ
  phase : Phase

/-- The state on entering Step 0 from a minimum point `y*` of `G`: `s := y*`, `S₀ := y*`.
`S` and `c⁰` are not yet assigned (they are set at the end of Step 0); they hold the placeholder
values `y*` and `0`, which no step reads before Step 0 overwrites them. -/
def init (ystar : ℤ) : AlgState :=
  ⟨ystar, ystar, ystar, 0, Phase.step0⟩

/-- One elementary step of the algorithm of §3, p. 659:
```
Step 0. s := y*; S₀ := y*;
  Repeat s := s − 1 until c(s, S₀) ≦ G(s);
  s₀ := s; c⁰ := c(s₀, S₀); S⁰ := S₀; S := S⁰ + 1;
Step 1. While G(S) ≦ c⁰ do
  begin If c(s, S) < c⁰
    then begin S⁰ := S.
      While c(s, S⁰) ≦ G(s + 1) do s := s + 1;
      c⁰ = c(s, S⁰);
      end;
    S := S + 1;
  end.
```
* `step0`: decrement `s` (the `Repeat` body runs before its test); if then `c(s, y*) ≤ G(s)`, set
  `c⁰ := c(s, y*)`, `S⁰ := y*`, `S := y* + 1` and go to the outer loop.
* `outer`: if `G(S) ≤ c⁰`, then: if `c(s, S) < c⁰`, set `S⁰ := S` and enter the inner loop;
  otherwise `S := S + 1`. If `G(S) > c⁰`, terminate.
* `inner`: if `c(s, S⁰) ≤ G(s + 1)`, set `s := s + 1`; otherwise set `c⁰ := c(s, S⁰)`,
  `S := S + 1` and return to the outer test.
* `done` is absorbing. -/
noncomputable def step (p : ℕ → ℝ) (K : ℝ) (G : ℤ → ℝ) (ystar : ℤ) (σ : AlgState) : AlgState :=
  match σ.phase with
  | Phase.step0 =>
      if c p K G (σ.s - 1) ystar ≤ G (σ.s - 1) then
        ⟨σ.s - 1, ystar + 1, ystar, c p K G (σ.s - 1) ystar, Phase.outer⟩
      else
        ⟨σ.s - 1, σ.S, σ.S0, σ.c0, Phase.step0⟩
  | Phase.outer =>
      if G σ.S ≤ σ.c0 then
        if c p K G σ.s σ.S < σ.c0 then
          ⟨σ.s, σ.S, σ.S, σ.c0, Phase.inner⟩
        else
          ⟨σ.s, σ.S + 1, σ.S0, σ.c0, Phase.outer⟩
      else
        ⟨σ.s, σ.S, σ.S0, σ.c0, Phase.done⟩
  | Phase.inner =>
      if c p K G σ.s σ.S0 ≤ G (σ.s + 1) then
        ⟨σ.s + 1, σ.S, σ.S0, σ.c0, Phase.inner⟩
      else
        ⟨σ.s, σ.S + 1, σ.S0, c p K G σ.s σ.S0, Phase.outer⟩
  | Phase.done => σ

/-- The algorithm started at the minimum point `y*` and run for `n` elementary steps:
`some (s, S⁰, c⁰)` if it has terminated within `n` steps, with final values `s`, `S⁰`, `c⁰`, and
`none` if it has not terminated yet. The run never returns an output it has not reached by
terminating. -/
noncomputable def run (p : ℕ → ℝ) (K : ℝ) (G : ℤ → ℝ) (ystar : ℤ) (n : ℕ) :
    Option (ℤ × ℤ × ℝ) :=
  let σ := (step p K G ystar)^[n] (init ystar)
  if σ.phase = Phase.done then some (σ.s, σ.S0, σ.c0) else none

end ZhengFedergruenSS.Algorithm


