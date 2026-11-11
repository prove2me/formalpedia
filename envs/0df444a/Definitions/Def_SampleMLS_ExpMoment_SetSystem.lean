-- Prove2me | Definitions.Def_SampleMLS_ExpMoment_SetSystem
-- name    : SampleMLS_ExpMoment_SetSystem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:49:57.13046+00:00
-- url     : https://prove2.me/theorems/c3a45b7d-4e3e-4bff-be63-e590d6764274
-- title:
--   Implicit set systems, Φ-Extension, running-time exponents (Definitions 3.1–3.2), exponential moments, the generating function and condition (⋆) (Definition 3.3)
-- statement:
--   Definitions 3.1–3.3, p. 15 (PDF 17), and condition (⋆) of Theorem 3.5, p. 17 (PDF 19). "In time $N^{O(1)}$" means within $(N+2)^c$ for one constant $c$ fixed before the instance.
--
--   - **Φ-Extension** (`extYes U F X k`): some $Y\subseteq U\setminus X$ with $|X|+|Y|\le k$ has $X\cup Y\in F$ (the page's $|Y|\le k-|X|$ over the integers; the answer is no for $k<|X|$).
--   - **Implicit set system** (Definition 3.1, `IsImplicitSetSystem U F`): every instance $I\in\{0,1\}^*$ has a universe $U_I$ (a finite set of naturals, the codes in which it is listed) with $n=|U_I|\le N=|I|$ and a family $F_I$ of subsets of $U_I$; a deterministic program lists $U_I$ (each element once) and one decides membership of a subset of $U_I$ in $F_I$, both in time $N^{O(1)}$.
--   - **Solving Φ-Extension** (`SolvesExtension U F A`): $A$ is deterministic and on every input $(I,X,k)$ with $X\subseteq U_I$, $k\ge 0$, halts and answers yes exactly when `extYes`.
--   - **Running-time exponent** (Definition 3.2, `IsRunningTimeExponent U A g`): for $X\subseteq U_I$ and $k\ge|X|$, $g(I,X,k)\in[0,\infty)$ is real; the comparison $g(I,X,k)\le\theta$ is decided by one deterministic program for integer thresholds $0\le\theta\le(N+2)^a$ in time $(N+2)^{c(a)}$; and $A$ runs in time $2^{g(I,X,k)}(N+2)^c$ on every such input, including samples in no solution.
--   - **Exponential moments and generating function** (Definition 3.3), for $g(X)=g(I,X,k)$ with $I,k$ fixed: $\mu_t(S)=\sum_{X\in\binom{S}{t}}2^{-g(X)}$ and $W_S(y)=\sum_{t=0}^{k}\mu_t(S)\,y^t$, $k=|S|$ (with $y^0=1$, the page's $0^0=1$).
--   - `maxMoment g U S` $=\max_{0\le t\le k}\mu_t(S)/\binom{n}{t}$ and **(⋆)** (`Star g U S ψ Γ`): $\max_{0\le t\le k}\mu_t(S)/\binom{n}{t}\ge 2^{-\psi n}/\Gamma$, $n=|U|$.
-- source:
--   Gaspers, Monotone Local Search with Sample-Dependent Running Times, arXiv:2611.01774 (sha256 da381dca…), Definitions 3.1–3.3, p. 15 (PDF 17); (⋆), p. 17 (PDF 19)

import Mathlib
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_SampleMLS_ExpMoment_Model

set_option autoImplicit false

open scoped ENNReal

namespace SampleMLS.ExpMoment

noncomputable section

open PDSEquiv

open Classical

/-!
# Implicit set systems, Φ-Extension, running-time exponents and exponential moments

S. Gaspers, *Monotone Local Search with Sample-Dependent Running Times*, arXiv:2611.01774
(sha256 da381dca…), §3.1, Definitions 3.1–3.3, p. 15 (PDF 17), and "Comparisons with thresholds",
p. 15.

**Formalization Note.** An instance is a binary string `I : List Bool`, `N = I.length`. Universe
elements are natural numbers (the codes in which `U_I` is listed); `U I : Finset ℕ` and the solutions
`F I : Set (Finset ℕ)`. "In time `N^{O(1)}`" is `(N + 2)^c` for one constant `c` fixed
before the instance (`+ 2` only keeps the bound positive at `N ≤ 1`). Programs are those of
`SampleMLS.ExpMoment.Model` on `PDSEquiv.Machine`. A running-time exponent is real-valued; "g can be
computed in time `N^{O(1)}`" is read, as the paragraph "Comparisons with thresholds" does, as a
polynomial-time decision of `g(I, X, k) ≤ θ`, here for nonnegative integer thresholds `θ` of value
at most `(N + 2)^a`, with one program and, for each `a`, one exponent. Once `I` and `k` are fixed, the
moments are written for `g(X) = g(I, X, k)`, a function `gk : Finset ℕ → ℝ`; `2^{-g}` is `Real.rpow`,
and Lean's `y ^ 0 = 1` matches the page's `0^0 = 1`.
-/

/-- Φ-Extension, for one instance (universe `U`, solutions `F`): `X` lies in a solution with at most
`k` elements, i.e. some `Y ⊆ U \ X` with `|X| + |Y| ≤ k` (the page's `|Y| ≤ k − |X|` over the integers,
so the answer is no when `k < |X|`) has `X ∪ Y ∈ F`. -/
def extYes (U : Finset ℕ) (F : Set (Finset ℕ)) (X : Finset ℕ) (k : ℕ) : Prop :=
  ∃ Y ⊆ U \ X, X.card + Y.card ≤ k ∧ X ∪ Y ∈ F

/-- Definition 3.1: an implicit set system. Every instance `I` has a universe `U I` with
`n = |U I| ≤ N = |I|` and a family `F I` of subsets of `U I`; `U I` can be listed (each element once)
and membership of a subset of `U I` in `F I` decided in time `N^{O(1)}`. -/
def IsImplicitSetSystem (U : List Bool → Finset ℕ) (F : List Bool → Set (Finset ℕ)) : Prop :=
  (∀ I, (U I).card ≤ I.length) ∧ (∀ I, ∀ S ∈ F I, S ⊆ U I) ∧
  (∃ (L : Program) (c : ℕ), ∀ I,
     DetComputes L (encI I) (((I.length + 2) ^ c : ℕ) : ℝ≥0∞)
       (fun o => o.Nodup ∧ o.toFinset = U I)) ∧
  (∃ (D : Program) (c : ℕ), ∀ I, ∀ S ⊆ U I,
     DetComputes D (encISet I S) (((I.length + 2) ^ c : ℕ) : ℝ≥0∞)
       (fun o => o = if S ∈ F I then yesOut else noOut))

/-- `A` is a deterministic algorithm solving Φ-Extension: on every input `(I, X, k)` with `X ⊆ U_I`
and every integer `k ≥ 0` it halts and answers yes exactly when `X` lies in a solution of `I` with
at most `k` elements. -/
def SolvesExtension (U : List Bool → Finset ℕ) (F : List Bool → Set (Finset ℕ)) (A : Program) :
    Prop :=
  IsDeterministic A ∧ ∀ I, ∀ X ⊆ U I, ∀ k : ℕ,
    runTime A noOracle (encIXk I X k) < ⊤ ∧
    OutputsSatisfy A noOracle (encIXk I X k)
      (fun o => o = if extYes (U I) (F I) X k then yesOut else noOut)

/-- Definition 3.2: `g` is a running-time exponent for `A`. On inputs `(I, X, k)` with `X ⊆ U_I` and
`k ≥ |X|`: `g(I, X, k) ∈ [0, ∞)`; the comparison `g(I, X, k) ≤ θ` with an integer threshold is
decided in time `N^{O(1)}` (one program; for thresholds at most `(N + 2)^a`, one exponent `c` per
`a`); and `A` runs in time `2^{g(I,X,k)} N^{O(1)}` on every such input, including samples contained in
no solution. -/
def IsRunningTimeExponent (U : List Bool → Finset ℕ) (A : Program)
    (g : List Bool → Finset ℕ → ℕ → ℝ) : Prop :=
  (∀ I, ∀ X ⊆ U I, ∀ k : ℕ, X.card ≤ k → 0 ≤ g I X k) ∧
  (∃ G : Program, ∀ a : ℕ, ∃ c : ℕ, ∀ I, ∀ X ⊆ U I, ∀ k : ℕ, X.card ≤ k →
     ∀ θ : ℕ, θ ≤ (I.length + 2) ^ a →
       DetComputes G (encIXk I X k ++ [θ]) (((I.length + 2) ^ c : ℕ) : ℝ≥0∞)
         (fun o => o = if g I X k ≤ (θ : ℝ) then yesOut else noOut)) ∧
  (∃ c : ℕ, ∀ I, ∀ X ⊆ U I, ∀ k : ℕ, X.card ≤ k →
     runTime A noOracle (encIXk I X k) ≤
       ENNReal.ofReal ((2 : ℝ) ^ g I X k * ((I.length : ℝ) + 2) ^ c))

/-- Definition 3.3: the exponential moment `µ_t(S) = ∑_{X ∈ (S choose t)} 2^{-g(X)}`. -/
def mu (gk : Finset ℕ → ℝ) (S : Finset ℕ) (t : ℕ) : ℝ :=
  ∑ X ∈ S.powersetCard t, (2 : ℝ) ^ (-(gk X))

/-- Definition 3.3: the generating function `W_S(y) = ∑_{t=0}^{k} µ_t(S) y^t`, `k = |S|`. -/
def W (gk : Finset ℕ → ℝ) (S : Finset ℕ) (y : ℝ) : ℝ :=
  ∑ t ∈ Finset.range (S.card + 1), mu gk S t * y ^ t

/-- `max_{0 ≤ t ≤ k} µ_t(S) / (n choose t)` with `k = |S|`, `n = |U|`. -/
def maxMoment (gk : Finset ℕ → ℝ) (U S : Finset ℕ) : ℝ :=
  (Finset.range (S.card + 1)).sup' ⟨0, by simp⟩
    (fun t => mu gk S t / ((U.card.choose t : ℕ) : ℝ))

/-- Condition (⋆) of Theorem 3.5: `max_{0 ≤ t ≤ k} µ_t(S) / (n choose t) ≥ 2^{-ψn} / Γ`. -/
def Star (gk : Finset ℕ → ℝ) (U S : Finset ℕ) (ψ Γ : ℝ) : Prop :=
  (2 : ℝ) ^ (-(ψ * (U.card : ℝ))) / Γ ≤ maxMoment gk U S

end

end SampleMLS.ExpMoment


