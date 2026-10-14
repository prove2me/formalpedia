-- Prove2me | Definitions.Def_MFIrrev_Equilibrium_TwoStateChain
-- name    : MFIrrev_Equilibrium_TwoStateChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:23:48.609757+00:00
-- url     : https://prove2.me/theorems/233b196c-f068-48a2-a3d6-f563b5a6791d
-- title:
--   §2, (2.1), p. 5 — two-state continuous-time Markov chain with generator [[−p₁, p₁], [p₂, −p₂]], its stationary law π and transition function exp(tP)
-- statement:
--   Fix switching intensities $p_1, p_2$ and the **generator matrix**
--   $$P=\begin{pmatrix}-p_1 & p_1\\ p_2 & -p_2\end{pmatrix},\qquad \pi=(\pi_1,\pi_2)=\Big(\frac{p_2}{p_1+p_2},\ \frac{p_1}{p_1+p_2}\Big).$$
--   Its **transition function** $e^{tP}$ has the closed form
--   $$\big(e^{tP}\big)_{ij}=\pi_j+\big(\mathbb 1_{\{i=j\}}-\pi_j\big)\,e^{-(p_1+p_2)t},\qquad t\ge 0,$$
--   which is the identity at $t=0$ and has derivative $P$ at $t=0$.
--
--   On a probability space $(\Omega,\mathcal F,\mathbb P)$ with a filtration $\mathbb F=(\mathcal F_t)_{t\ge0}$, a process $\varepsilon=(\varepsilon_t)_{t\ge0}$ with values in the two states is a **two-state continuous-time Markov chain with generator $P$** with respect to $\mathbb F$ if
--
--   1. $\varepsilon$ is $\mathbb F$-adapted;
--   2. every path is right-constant: from every time $t$ it stays at $\varepsilon_t$ for a positive length of time;
--   3. every path has finitely many jump times in every bounded interval $[0,T]$;
--   4. (Markov property) for all $s,t\ge0$ and every state $j$,
--   $$\mathbb P\big(\varepsilon_{s+t}=j\,\big|\,\mathcal F_s\big)=\big(e^{tP}\big)_{\varepsilon_s j}\quad\text{almost surely.}$$
--
--   This is the regime process of Aïd, Basei and Ferrari's model: in state $i$ the chain waits an exponential time with rate $p_i$ and then switches to the other state, and $\pi$ is its stationary distribution.
--
--   **Formalization Note.** The two states are `Fin 2`; index `0` is the paper's state 1 and index `1` its state 2. The chain is pinned by its closed-form transition function instead of a matrix exponential. A jump time is a time $t$ such that the path takes a different value at times arbitrarily close before $t$. The object is general (any rates $p$) and does not depend on the rest of the model.
-- source:
--   Aïd, Basei & Ferrari, A Stationary Mean-Field Equilibrium Model of Irreversible Investment in a Two-Regime Economy, arXiv:2305.00541v1, p. 5, (2.1) and the paragraph after it

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MFIrrev.Equilibrium

/-- Stationary distribution `π = (p₂/(p₁+p₂), p₁/(p₁+p₂))` of the two-state generator
`[[-p₁, p₁], [p₂, -p₂]]` (Aïd–Basei–Ferrari, (2.1)). The state index `0` is the paper's state 1 and
the index `1` is its state 2. -/
noncomputable def twoStatePi (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![p 1 / (p 0 + p 1), p 0 / (p 0 + p 1)]

/-- Transition function `exp(tP)_{ij}` of the two-state generator `P = [[-p₁, p₁], [p₂, -p₂]]`, in
closed form: `π_j + (𝟙{i = j} − π_j) e^{−(p₁+p₂)t}`. At `t = 0` it is the identity and its
`t`-derivative at `0` is `P`. -/
noncomputable def twoStateTrans (p : Fin 2 → ℝ) (t : ℝ) (i j : Fin 2) : ℝ :=
  twoStatePi p j + ((if i = j then 1 else 0) - twoStatePi p j) * Real.exp (-(p 0 + p 1) * t)

/-- `ε` is a continuous-time Markov chain on the two states `Fin 2` with generator
`P = [[-p₀, p₀], [p₁, -p₁]]` (in Lean's 0-based indexing) with respect to the filtration `ℱ`:
1. `ε` is `ℱ`-adapted;
2. every path is right-constant: from each time it stays put for a positive time;
3. every path has finitely many jump times in every bounded interval `[0, T]` (a jump time is a
   time `t` such that `ε` takes a different value at times arbitrarily close before `t`);
4. Markov property with transition function `exp(tP)`: for all `s, t ≥ 0` and every state `j`,
   `P(ε_{s+t} = j | ℱ_s) = exp(tP)_{ε_s, j}` almost surely. -/
def IsTwoStateChain {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
    (p : Fin 2 → ℝ) (ε : ℝ≥0 → Ω → Fin 2) : Prop :=
  (∀ t, Measurable[ℱ t] (ε t)) ∧
  (∀ (ω : Ω) (t : ℝ≥0), ∃ h : ℝ≥0, 0 < h ∧ ∀ s, t ≤ s → s < t + h → ε s ω = ε t ω) ∧
  (∀ (ω : Ω) (T : ℝ≥0),
    {t : ℝ≥0 | t ≤ T ∧ ∀ h : ℝ≥0, 0 < h → ∃ s, s < t ∧ t < s + h ∧ ε s ω ≠ ε t ω}.Finite) ∧
  (∀ (s t : ℝ≥0) (j : Fin 2),
    P[(ε (s + t) ⁻¹' {j}).indicator (fun _ => (1 : ℝ)) | ℱ s]
      =ᵐ[P] fun ω => twoStateTrans p (t : ℝ) (ε s ω) j)

end MFIrrev.Equilibrium


