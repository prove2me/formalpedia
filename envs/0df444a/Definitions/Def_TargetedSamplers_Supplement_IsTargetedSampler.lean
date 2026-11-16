-- Prove2me | Definitions.Def_TargetedSamplers_Supplement_IsTargetedSampler
-- name    : TargetedSamplers_Supplement_IsTargetedSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:12:59.672971+00:00
-- url     : https://prove2.me/theorems/80ad3c0f-643d-49bb-a45d-fea59504f206
-- title:
--   Targeted samplers and targeted hitters
-- statement:
--   Let $R,M,T:\mathbb N\to\mathbb N$ and $\epsilon,\delta:\mathbb N\to\mathbb R$. A map $\mathrm{tarSamp}$ sends an input $x\in\{0,1\}^n$ and a random string $r\in\{0,1\}^{R(n)}$ to a list of $D$ samples $\mathrm{tarSamp}(x,r)_1,\dots,\mathrm{tarSamp}(x,r)_D\in\{0,1\}^{M(n)}$. A **$T$-time algorithm** $A(x,y)$ is a deterministic program that, on every $x$ and every $y\in\{0,1\}^{M(|x|)}$, halts within time $T(|x|)$ (up to an additive constant) and outputs one bit.
--
--   $\mathrm{tarSamp}$ is an **$(\epsilon,\delta)$-targeted sampler against $T$-time algorithms** (randomness complexity $R$, sample complexity $D$) if for every $T$-time algorithm $A$ and all but finitely many $x$,
--   $$\Pr_{r\in\{0,1\}^{R(n)}}\Big[\Big|\mathop{\mathbb E}_{y\in\{0,1\}^{M(n)}}[A(x,y)]-\mathop{\mathbb E}_{s\in[D]}[A(x,\mathrm{tarSamp}(x,r)_s)]\Big|\le\epsilon(n)\Big]\ge1-\delta(n).$$
--
--   It is an **$(\epsilon,\delta)$-targeted hitter** if instead, with probability at least $1-\delta(n)$ over $r$: whenever $\mathbb E_y[A(x,y)]\ge\epsilon(n)$, some sample $s$ has $A(x,\mathrm{tarSamp}(x,r)_s)=1$.
--
--   Targeted samplers are the paper's central object: a sampler that sees the input $x$ only has to fool algorithms running on $x$, and can therefore have far fewer samples than a general sampler.
--
--   **Formalization Note** $\epsilon$ and $\delta$ are functions of the input length $n$ (Definition 1.2 writes $\epsilon(T)$ and $\delta(T')$). A $T$-time algorithm runs within $T(n)+K$ steps of the base RAM, for every constant $K$; it gets $x$ on its input tape and $y$ on its random-access tape. "All but finitely many $x$" is a finite set of inputs over all lengths. The mean over an empty sample list is $0$.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 1.2, pp.2–3 (pdf pp.4–5), Remark 1.5, p.4 (pdf p.6)

import Mathlib
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_coinProb

namespace TargetedSamplers.Supplement

/-- `A` is a deterministic `T`-time test on samples of length `M` with additive slack `K`: on every
input `x` and every string `y` of length `M(|x|)`, the program `A`, given `x` on its input tape and
`y` on its random-access second tape, halts within time `T(|x|) + K` and outputs one bit `A(x, y)`.
These are the "`T`-time algorithms `A(x, y)`" a targeted sampler must fool (Chen, Doron, Ebtehaj,
Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, Definition 1.2, p.2–3). -/
def IsTimedTest (A : Program) (M T : ℕ → ℕ) (K : ℕ) : Prop :=
  ∀ x y : List Bool, y.length = M x.length →
    ∃ b : Bool, A.RunsIn ⟨x, y, [], noOracle⟩ (T x.length + K) (some [b])

/-- `A(x, y) = 1`. -/
def Accepts (A : Program) (x y : List Bool) : Prop := A.Outputs ⟨x, y, [], noOracle⟩ (some [true])

/-- `E_{y ∈ {0,1}^{M(|x|)}}[A(x, y)]`. -/
noncomputable def uniformMean (A : Program) (M : ℕ → ℕ) (x : List Bool) : ℝ :=
  coinProb (M x.length) (fun y => Accepts A x y)

open Classical in
/-- `E_{s ∈ [D]}[A(x, S_s)]` for the multiset of samples `S` (a list of `D` strings): the fraction of
samples `y` with `A(x, y) = 1` (`0` when `S` is empty). -/
noncomputable def sampleMean (A : Program) (x : List Bool) (S : List (List Bool)) : ℝ :=
  ((S.countP fun y => decide (Accepts A x y) : ℕ) : ℝ) / (S.length : ℝ)

/-- `samp : {0,1}ⁿ × {0,1}^{R(n)} → ({0,1}^{M(n)})^D` is an `(ϵ, δ)`-targeted sampler against
`T`-time algorithms with randomness complexity `R` and sample length `M` (Definition 1.2,
pp.2–3): every sample `samp(x, r)_s` has length `M(|x|)`, and for every deterministic `T`-time
algorithm `A` and all but finitely many inputs `x`, with probability at least `1 − δ(|x|)` over
`r ∈ {0,1}^{R(|x|)}`,
`|E_{y}[A(x, y)] − E_{s ∈ [D]}[A(x, samp(x, r)_s)]| ≤ ϵ(|x|)`.

**Formalization Note** `samp x r` is the list of the `D` samples; the sample complexity is its
length. The accuracy `ϵ` and error `δ` are functions of the input length `n` (in Definition 1.2
they are written `ϵ(T)`, `δ(T′)`, functions of `T(n)` and `T′(n)`). "`T`-time algorithm" is time
`T(n) + K` on the base RAM, for every constant `K` (the class of algorithms to fool is not shrunk).
"All but finitely many `x`" is a finite set of inputs over all lengths. -/
def IsTargetedSampler (samp : List Bool → List Bool → List (List Bool)) (R M T : ℕ → ℕ)
    (ϵ δ : ℕ → ℝ) : Prop :=
  (∀ x r : List Bool, r.length = R x.length → ∀ y ∈ samp x r, y.length = M x.length) ∧
  ∀ (K : ℕ) (A : Program), IsTimedTest A M T K →
    {x : List Bool | ¬ (1 - δ x.length ≤ coinProb (R x.length) (fun r =>
      |uniformMean A M x - sampleMean A x (samp x r)| ≤ ϵ x.length))}.Finite

/-- `samp` is an `(ϵ, δ)`-targeted hitter against `T`-time algorithms with randomness complexity
`R` and sample length (output length) `M` (Remark 1.5, p.4–5: Definition 1.2 with Eq. (1.1)
replaced by "if `E_y[A(x, y)] ≥ ϵ(T)` then there is `s ∈ [D]` with `A(x, tarSamp(x, r)_s) = 1`"):
every sample has length `M(|x|)`, and for every deterministic `T`-time algorithm `A` and all but
finitely many `x`, with probability at least `1 − δ(|x|)` over `r`, if `E_y[A(x, y)] ≥ ϵ(|x|)` then
some sample `y ∈ samp(x, r)` has `A(x, y) = 1`.

**Formalization Note** Conventions as in `IsTargetedSampler`. -/
def IsTargetedHitter (samp : List Bool → List Bool → List (List Bool)) (R M T : ℕ → ℕ)
    (ϵ δ : ℕ → ℝ) : Prop :=
  (∀ x r : List Bool, r.length = R x.length → ∀ y ∈ samp x r, y.length = M x.length) ∧
  ∀ (K : ℕ) (A : Program), IsTimedTest A M T K →
    {x : List Bool | ¬ (1 - δ x.length ≤ coinProb (R x.length) (fun r =>
      ϵ x.length ≤ uniformMean A M x → ∃ y ∈ samp x r, Accepts A x y))}.Finite

end TargetedSamplers.Supplement


