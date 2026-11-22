-- Prove2me | Definitions.Def_SKHessianAscent_Sampler
-- name    : SKHessianAscent_Sampler
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-22T19:55:09.652451+00:00
-- url     : https://prove2.me/theorems/f26ebb8e-2496-4918-9b35-1c6b777d7031
-- title:
--   Samplers on the unit-cost real RAM with Gaussian samples: input layout, output law, running time, Hamming wedges
-- statement:
--   This file fixes what it means for a program to sample from a law on $\{\pm1\}^n$ in a given time, on the published `PolySampIso` real RAM: exact arithmetic $+,-,\times,\div$ on real registers, rational literals, indirect memory through integer pointers, comparisons, $\sqrt{\cdot}$, $\exp$, $\log$, a draw of $N(0,1)$, a draw of $\mathrm{Exp}(1)$, and `halt`; every executed instruction costs one step.
--
--   **Input.** `initState n mem` is the initial state with pointer $p[0]=n$, all other pointers and all registers $0$, and memory `mem`.
--
--   - `samplerMem β A` (input of a sampler for $\mu_{\beta A}$): $M[0]=\beta$ and $M[1+i\,n+j]=A_{ij}$ for $0\le i,j<n$.
--   - `wedgeMem β' ε y A` (input of a wedge sampler): $M[0]=\beta'$, $M[1]=\varepsilon$, $M[2+i]=y_i$, $M[2+n+i\,n+j]=A_{ij}$.
--
--   Every other memory cell is $0$.
--
--   **Output.** `spinOut n s` reads a configuration from a state $s$: spin $j$ is $+1$ if $M[-1-j]>0$ and $-1$ otherwise. `outLaw P n s₀` is the output law of program $P$ started at $s_0$,
--   $$\mathrm{outLaw}(\sigma)=\Pr_{\text{streams}}\big[\text{the state at the halting time encodes }\sigma\big],$$
--   the probability being over the machine's two random streams (i.i.d. $N(0,1)$ and i.i.d. $\mathrm{Exp}(1)$).
--
--   **Running time.** `HaltsWithin P s₀ T` says that on every pair of streams the run of $P$ from $s_0$ has halted after at most $T$ steps.
--
--   **Wedges (p. 6).** `hamming` is the Hamming distance $d$ on $\{\pm1\}^n$, `signSpin y` is $\mathrm{sign}(y)$, and `wedgeLaw p σ₀ r` is the law $p$ conditioned on the Hamming ball $B(\sigma_0,r)=\{x:d(x,\sigma_0)\le r\}$:
--   $$p|_{B(\sigma_0,r)}(x)=\frac{p(x)\,\mathbf 1[d(x,\sigma_0)\le r]}{p(B(\sigma_0,r))}.$$
--
--   These conventions are used by the goal (Theorem 1.1) and by desideratum (d6).
--
--   **Formalization Note** The paper names no machine; its algorithm takes the real matrix $A$ as input, draws Gaussians and evaluates $\tanh$, $\log$ and matrix inverses, so "polynomial time" is read on a unit-cost real RAM. Because every memory cell decodes to a spin, the output law of a program that halts almost surely is a probability mass function. The running-time predicate ranges over all streams, not only almost all. `signSpin` uses $\mathrm{sign}(0)=+1$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Theorem 1.1 p. 1 ("in polynomial time"), desideratum (d6) p. 6, Algorithm 2 p. 6

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_PolySampIso_Machine
import Definitions.Def_SKHessianAscent_Model

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory
open scoped BigOperators

namespace SKHessianAscent

/-!
# Samplers on the unit-cost real RAM with Gaussian samples

H. Lee, J. S. Sandhu, J. Shi, *Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick
model at β < 1*, Theorem 1.1 (p. 1: "gives a sample ... in polynomial time") and desideratum (d6)
(p. 6: "a poly(n, log(1/ε))-time algorithm to sample").

**Formalization Note.** The paper names no machine. Its algorithm takes the real matrix `A` as
input, draws standard Gaussians, and evaluates `tanh`, `log` and matrix inverses, so "polynomial
time" is read on a unit-cost real RAM. The machine is the published `PolySampIso` real RAM:
exact `+ − × ÷`, rational literals (`Admissible`), indirect memory through integer pointers,
comparisons, `√`, `exp`, `log`, a draw of `N(0,1)`, a draw of `Exp(1)`, and `halt`; every executed
instruction costs one step. This file fixes only the input and output conventions.

* **Input.** Pointer `p[0] = n`; all other pointers and all registers are `0`. For a sampler of
  `μ_{βA}` (`samplerMem`): `M[0] = β` and `M[1 + i·n + j] = A i j`. For a wedge sampler
  (`wedgeMem`): `M[0] = β'`, `M[1] = ε`, `M[2 + i] = y i`, `M[2 + n + i·n + j] = A i j`. Every
  other memory cell is `0`.
* **Output.** At the halting time, spin `j` is `+1` if `M[−1 − j] > 0` and `−1` otherwise
  (`spinOut`), so every halted state encodes a configuration.
* **Output law.** `outLaw P n s₀ σ` is the probability, over the two random streams of the
  machine (`PolySampIso.tape`), that the run of `P` from `s₀` outputs `σ`.
* **Running time.** `HaltsWithin P s₀ T`: on every pair of streams, the run has halted after at
  most `T` steps.
-/

noncomputable section

/-- The initial state with input memory `mem` and pointer `p[0] = n`. -/
def initState (n : ℕ) (mem : ℤ → ℝ) : PolySampIso.State :=
  ⟨⟨0, fun _ => 0, fun q => if q = 0 then (n : ℤ) else 0, mem⟩, 0, 0, false, 0⟩

/-- Input memory of a sampler for `μ_{βA}`: `M[0] = β`, `M[1 + i·n + j] = A i j`. -/
def samplerMem {n : ℕ} (β : ℝ) (A : Fin n → Fin n → ℝ) : ℤ → ℝ := fun a =>
  (if a = 0 then β else 0) +
    ∑ i : Fin n, ∑ j : Fin n, if a = 1 + (i : ℤ) * (n : ℤ) + (j : ℤ) then A i j else 0

/-- Input memory of a wedge sampler: `M[0] = β'`, `M[1] = ε`, `M[2 + i] = y i`,
`M[2 + n + i·n + j] = A i j`. -/
def wedgeMem {n : ℕ} (β' ε : ℝ) (y : Fin n → ℝ) (A : Fin n → Fin n → ℝ) : ℤ → ℝ := fun a =>
  (if a = 0 then β' else 0) + (if a = 1 then ε else 0) +
    (∑ i : Fin n, if a = 2 + (i : ℤ) then y i else 0) +
    ∑ i : Fin n, ∑ j : Fin n,
      if a = 2 + (n : ℤ) + (i : ℤ) * (n : ℤ) + (j : ℤ) then A i j else 0

/-- The configuration encoded by a state: spin `j` is `+1` iff `M[−1 − j] > 0`. -/
def spinOut (n : ℕ) (s : PolySampIso.State) : Spin n :=
  fun j => decide (0 < s.core.mem (-1 - (j : ℤ)))

/-- The output law of program `P` started from `s₀`: the probability, under the tape measure,
that the state at the halting time encodes `σ`. -/
def outLaw (P : PolySampIso.Program) (n : ℕ) (s₀ : PolySampIso.State) : Spin n → ℝ :=
  fun σ => (PolySampIso.tape
    {ω | spinOut n (PolySampIso.run P s₀ ω (PolySampIso.haltTime P s₀ ω)) = σ}).toReal

/-- On every pair of random streams, the run of `P` from `s₀` has halted within `T` steps. -/
def HaltsWithin (P : PolySampIso.Program) (s₀ : PolySampIso.State) (T : ℝ) : Prop :=
  ∀ ω : PolySampIso.Streams, ∃ t : ℕ, (t : ℝ) ≤ T ∧ (PolySampIso.run P s₀ ω t).halted = true

/-- Hamming distance on `{±1}^n`. -/
def hamming {n : ℕ} (x z : Spin n) : ℕ := (Finset.univ.filter fun i => x i ≠ z i).card

/-- `sign(y) ∈ {±1}^n`, with `sign(0) = +1`. -/
def signSpin {n : ℕ} (y : Fin n → ℝ) : Spin n := fun i => decide (0 ≤ y i)

/-- The law `p` conditioned on the Hamming ball `B(σ₀, r) = {x : d(x, σ₀) ≤ r}` (p. 6):
`p|_{B(σ₀,r)}(x) = p(x) 1[d(x,σ₀) ≤ r] / p(B(σ₀, r))`. -/
def wedgeLaw {n : ℕ} (p : Spin n → ℝ) (σ₀ : Spin n) (r : ℝ) : Spin n → ℝ := fun x =>
  if (hamming x σ₀ : ℝ) ≤ r then
    p x / ∑ z : Spin n, if (hamming z σ₀ : ℝ) ≤ r then p z else 0
  else 0

end

end SKHessianAscent


