-- Prove2me | Definitions.Def_SampleMLS_ExpMoment_MLS
-- name    : SampleMLS_ExpMoment_MLS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:50:53.441522+00:00
-- url     : https://prove2.me/theorems/f29d995a-d675-428a-8748-ee5b82dba663
-- title:
--   Conditions (2), Algorithm 3.4 (MLS-θ) as the law of its trial loop, and the notation of Lemma 3.8
-- statement:
--   Algorithm 3.4 and (2), p. 16 (PDF 18); Lemma 3.8, p. 18 (PDF 20); "computed in time $N^{O(1)}$" for the real parameters, p. 16.
--
--   - `PolyApproximable U f`: a real parameter $f(I,k)$ is computed in time $N^{O(1)}$: one deterministic program outputs, on $(I,k)$ with $k\le n$ and a precision $j$, a rational within $2^{-j}$ of $f(I,k)$ in time $(N+j+2)^c$.
--   - $x=\psi n+\log_2\Gamma$ (`xParam`), $M_{t,\theta}=4\kappa\Gamma(\Theta+1)2^{\psi n-\theta}$ (`Mtt`, real).
--   - **(2)** (`Cond2 = CapOK ∧ TrialsOK`): an integer cap $\Theta\ge0$ with $x+1\le\Theta\le x+3$, and trial counts with $M_{t,\theta}\le m_{t,\theta}\le 2M_{t,\theta}+1$ for $t\in\{0,\dots,k\}$, $\theta\in\{0,\dots,\Theta\}$ (counts are naturals; (2) forces them positive).
--   - $q_\theta$ (`qCount`): the number of $X\in\binom{S}{t}$ with $g(X)\le\theta$.
--   - **Algorithm 3.4** (`mlsLaw U g acc k Θ m`): the law of the answer of the trial loop. The trials are listed (`trialList`): for $t=0,\dots,k$ and $\theta=0,\dots,\Theta$, the pair $(t,\theta)$ $m_{t,\theta}$ times. A trial (`trialLaw`) draws $X$ uniformly from $\binom{U}{t}$, independently of all other trials, and succeeds iff $g(X)\le\theta$ and the extension call on $X$ accepts (`acc X`). The answer is yes as soon as a trial succeeds and no after all fail (`loopLaw`).
--   - Lemma 3.8 notation: $2^{-\xi}$ for $\xi\in[0,\infty]$ with $2^{-\infty}=0$ (`twoNeg`), and $\Pr[\xi\le\theta]$ for an integer $\theta$ (`probLe`, the measure of $\{\xi<\infty,\ \xi\le\theta\}$, empty for $\theta<0$).
-- source:
--   Gaspers, Monotone Local Search with Sample-Dependent Running Times, arXiv:2611.01774 (sha256 da381dca…), Algorithm 3.4 and (2), p. 16 (PDF 18); Lemma 3.8, p. 18 (PDF 20)

import Mathlib
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_SampleMLS_ExpMoment_Model
import Definitions.Def_SampleMLS_ExpMoment_SetSystem

set_option autoImplicit false

open scoped ENNReal

namespace SampleMLS.ExpMoment

noncomputable section

open Classical

/-!
# Conditions (2), Algorithm 3.4 (MLS-θ) as a law, and the notation of Lemma 3.8

S. Gaspers, *Monotone Local Search with Sample-Dependent Running Times*, arXiv:2611.01774
(sha256 da381dca…), Algorithm 3.4 and (2), p. 16 (PDF 18); Lemma 3.8, p. 18 (PDF 20).

**Formalization Note.** `log` is `Real.logb 2`; `x = ψn + log Γ` and `M_{t,θ} = 4κΓ(Θ+1)2^{ψn−θ}`
are real (`M_{t,θ}` does not depend on `t`). The cap `Θ` is an integer; trial counts are naturals
(condition (2) forces `m_{t,θ} ≥ M_{t,θ} > 0`). The law of Algorithm 3.4 is the law of its trial loop:
the trials are listed (sample size `t = 0, …, k`, threshold `θ = 0, …, Θ`, each pair `m_{t,θ}` times),
each trial draws `X` uniformly from `(U choose t)` independently and succeeds when `g(X) ≤ θ` and the
extension call accepts `X` (the predicate `acc`), and the answer is yes iff some trial succeeds.
Lemma 3.8's `2^{−ξ}` for `ξ ∈ [0, ∞]` is `twoNeg ξ` with `2^{−∞} = 0`, and `Pr[ξ ≤ θ]` for an integer
`θ` (possibly negative) is the measure of `{ξ < ∞, ξ ≤ θ}`.
-/

/-- A real parameter `f(I, k)` "computed from `(I, k)` in time `N^{O(1)}`": one deterministic program
that, on `(I, k)` with `k ≤ n` and a precision `j`, outputs a rational within `2^{-j}` of `f(I, k)`
in time `(N + j + 2)^c`. -/
def PolyApproximable (U : List Bool → Finset ℕ) (f : List Bool → ℕ → ℝ) : Prop :=
  ∃ (R : PDSEquiv.Program) (c : ℕ), ∀ (I : List Bool) (k : ℕ), k ≤ (U I).card → ∀ j : ℕ,
    DetComputes R (encIk I k ++ [j]) (((I.length + j + 2) ^ c : ℕ) : ℝ≥0∞) (ApproxOut (f I k) j)

/-- `x = ψn + log Γ`. -/
def xParam (ψ Γ : ℝ) (n : ℕ) : ℝ := ψ * (n : ℝ) + Real.logb 2 Γ

/-- `M_{t,θ} = 4κΓ(Θ + 1) 2^{ψn − θ}`. -/
def Mtt (κ Γ ψ : ℝ) (n : ℕ) (Θ θ : ℤ) : ℝ :=
  4 * κ * Γ * ((Θ : ℝ) + 1) * (2 : ℝ) ^ (ψ * (n : ℝ) - (θ : ℝ))

/-- The cap part of (2): an integer `Θ ≥ 0` with `x + 1 ≤ Θ ≤ x + 3`. -/
def CapOK (ψ Γ : ℝ) (n : ℕ) (Θ : ℤ) : Prop :=
  0 ≤ Θ ∧ xParam ψ Γ n + 1 ≤ (Θ : ℝ) ∧ (Θ : ℝ) ≤ xParam ψ Γ n + 3

/-- The trial-count part of (2): `M_{t,θ} ≤ m_{t,θ} ≤ 2M_{t,θ} + 1` for `t ∈ {0, …, k}` and
`θ ∈ {0, …, Θ}`. -/
def TrialsOK (ψ Γ κ : ℝ) (n k : ℕ) (Θ : ℤ) (m : ℕ → ℤ → ℕ) : Prop :=
  ∀ t ≤ k, ∀ θ : ℤ, 0 ≤ θ → θ ≤ Θ →
    Mtt κ Γ ψ n Θ θ ≤ (m t θ : ℝ) ∧ (m t θ : ℝ) ≤ 2 * Mtt κ Γ ψ n Θ θ + 1

/-- Condition (2) on the cap `Θ` and the trial counts `m_{t,θ}`. -/
def Cond2 (ψ Γ κ : ℝ) (n k : ℕ) (Θ : ℤ) (m : ℕ → ℤ → ℕ) : Prop :=
  CapOK ψ Γ n Θ ∧ TrialsOK ψ Γ κ n k Θ m

/-- `q_θ`: the number of `X ∈ (S choose t)` with `g(X) ≤ θ`. -/
def qCount (gk : Finset ℕ → ℝ) (S : Finset ℕ) (t : ℕ) (θ : ℤ) : ℕ :=
  ((S.powersetCard t).filter fun X => gk X ≤ (θ : ℝ)).card

/-- One trial of the pair `(t, θ)`: draw `X` uniformly from `(U choose t)`; it succeeds iff
`g(X) ≤ θ` and the extension call on `X` accepts. (No `t`-subset exists only for `t > |U|`, which the
algorithm never uses since `t ≤ k ≤ n`.) -/
def trialLaw (U : Finset ℕ) (gk : Finset ℕ → ℝ) (acc : Finset ℕ → Prop) (t : ℕ) (θ : ℤ) :
    PMF Bool :=
  if h : (U.powersetCard t).Nonempty then
    (PMF.uniformOfFinset (U.powersetCard t) h).map fun X => decide (gk X ≤ (θ : ℝ) ∧ acc X)
  else PMF.pure false

/-- The trials of Algorithm 3.4 in order: for `t = 0, …, k` and `θ = 0, …, Θ`, the pair `(t, θ)`
repeated `m_{t,θ}` times. -/
def trialList (k : ℕ) (Θ : ℤ) (m : ℕ → ℤ → ℕ) : List (ℕ × ℤ) :=
  (List.range (k + 1)).flatMap fun t =>
    (List.range (Θ.toNat + 1)).flatMap fun j => List.replicate (m t (j : ℤ)) (t, (j : ℤ))

/-- The law of the answer of a list of independent trials: yes as soon as one succeeds, no after all
of them fail. -/
def loopLaw (U : Finset ℕ) (gk : Finset ℕ → ℝ) (acc : Finset ℕ → Prop) :
    List (ℕ × ℤ) → PMF Bool
  | [] => PMF.pure false
  | (t, θ) :: rest =>
      (trialLaw U gk acc t θ).bind fun b => if b then PMF.pure true else loopLaw U gk acc rest

/-- Algorithm 3.4 (MLS-θ) on an instance with universe `U`, `g(X) = g(I, X, k)`, extension answers
`acc`, size bound `k`, cap `Θ` and trial counts `m`: the law of its answer (`true` = yes). -/
def mlsLaw (U : Finset ℕ) (gk : Finset ℕ → ℝ) (acc : Finset ℕ → Prop) (k : ℕ) (Θ : ℤ)
    (m : ℕ → ℤ → ℕ) : PMF Bool :=
  loopLaw U gk acc (trialList k Θ m)

/-- `2^{−ξ}` for `ξ ∈ [0, ∞]`, with `2^{−∞} = 0`. -/
def twoNeg (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = ⊤ then 0 else (2 : ℝ≥0∞) ^ (-(x.toReal))

/-- `Pr[ξ ≤ θ]` for an integer `θ`: the measure of `{ω | ξ ω < ∞ ∧ ξ ω ≤ θ}` (empty for `θ < 0`). -/
def probLe {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (ξ : Ω → ℝ≥0∞)
    (θ : ℤ) : ℝ≥0∞ :=
  μ {ω | ξ ω ≠ ⊤ ∧ (ξ ω).toReal ≤ (θ : ℝ)}

end

end SampleMLS.ExpMoment


