-- Prove2me | Definitions.Def_PrivLearn_SQSim_LocalAlg
-- name    : PrivLearn_SQSim_LocalAlg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:16.197816+00:00
-- url     : https://prove2.me/theorems/4304009f-b350-4114-a481-babe543c8f4e
-- title:
--   Statistical difference (p. 8), local randomizers with discrete output (Definition 5.1) and ε-local algorithms (Definitions 5.2, 5.3)
-- statement:
--   1. **Statistical difference** (p. 8). For two probability mass functions $\mu,\nu$ on a discrete space $O$,
--
--   $$\mathrm{SD}(\mu,\nu)=\max_{S\subseteq O}\,\bigl|\mu(S)-\nu(S)\bigr| .$$
--
--   The same formula is used when one of the two is a sub-probability mass function (an algorithm that may fail to stop); the missing mass then counts towards the difference.
--
--   2. **Local randomizer with discrete output** (Definition 5.1). A map $R$ assigning to each input $u\in D$ a probability mass function $R(u)$ on a set $W$ is an **$\varepsilon$-local randomizer** if
--
--   $$\Pr[R(u)=w]\le e^{\varepsilon}\Pr[R(u')=w]\qquad\text{for all }u,u'\in D,\ w\in W .$$
--
--   3. **$\varepsilon$-local algorithm making $t$ queries** (Definitions 5.2, 5.3). The algorithm $A$ accesses a database $z\in D^n$ only through the LR oracle: at its $k$-th call ($k=1,\dots,t$), having received answers $a_1,\dots,a_{k-1}$, it chooses an index $i_k\in[n]$ and an $\varepsilon_k$-local randomizer $R_k$ (all three may depend on $a_1,\dots,a_{k-1}$) and receives a fresh sample $a_k\sim R_k(z_{i_k})$. Along every answer sequence and for every index $i$, the budgets $\varepsilon_k$ of the calls on $i$ sum to at most $\varepsilon$. The output is a function of $(a_1,\dots,a_t)$. The algorithm is **noninteractive** if the indices, randomizers and budgets do not depend on earlier answers.
--
--   4. **Output distribution on i.i.d. data.** On a fixed database $z$, the answer sequence $a$ has probability $\prod_{k}\Pr[R_k(z_{i_k})=a_k]$ (each call uses fresh coins). When the entries of $z$ are drawn i.i.d. from a distribution $P$ on $D$, the probability that $A$ outputs $o$ is
--
--   $$\Pr[A\text{ outputs }o]=\sum_{a:\ \mathrm{out}(a)=o}\ \mathbb E_{z\sim P^n}\Bigl[\prod_{k=1}^t\Pr[R_k(z_{i_k})=a_k]\Bigr].$$
--
--   These are the objects simulated in §5.1.2: an SQ algorithm must reproduce $A$'s output distribution on i.i.d. data without seeing the data.
--
--   **Formalization Note.** Randomizers have discrete output: `R u` is a `PMF W`, which is what the simulation needs (it uses the point probabilities $\Pr[R(z_i)=w]$). For such randomizers the pointwise condition is equivalent to the set form of Definition 5.1 with the discrete σ-algebra. Calls are indexed $0,\dots,t-1$ and database entries $0,\dots,n-1$. The map $u\mapsto\Pr[R(u)=w]$ is required to be measurable, so that $\mathbb E_{z_i\sim P}\Pr[R(z_i)=w]$ is meaningful. The budget is required along every answer sequence, including sequences of probability $0$; an algorithm that violates it only on impossible sequences can be modified there without changing its output distribution. The algorithm's own coins are modeled as calls to $0$-local randomizers that ignore their input, and a randomized output map as such a call followed by a deterministic one. The statistical difference is valued in $[0,\infty]$; for each $S$ the expression $(a-b)+(b-a)$ with truncated subtraction is $|a-b|$.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 8 (§2, statistical difference), p. 19 (Definitions 5.1, 5.2, 5.3), p. 21 (Lemma 5.8, i.i.d. database)

import Mathlib

namespace PrivLearn.SQSim

open MeasureTheory

/-- §2 (p. 8): the statistical difference `max_{S ⊆ Out} |μ(S) − ν(S)|` of two (sub-)probability
mass functions on a discrete space `Out`, valued in `[0, ∞]`. For each `S`, `(a - b) + (b - a)` in
`ℝ≥0∞` is `|a − b|` (one of the two truncated differences is `0`). -/
noncomputable def statDiff {Out : Type*} (μ ν : Out → ENNReal) : ENNReal :=
  ⨆ S : Set Out,
    ((∑' o, S.indicator μ o) - ∑' o, S.indicator ν o) +
      ((∑' o, S.indicator ν o) - ∑' o, S.indicator μ o)

/-- Definition 5.1 (p. 19), pointwise form for a randomizer with discrete output: `R` is an
ε-local randomizer if `Pr[R(u) = w] ≤ e^ε Pr[R(u′) = w]` for all `u, u′ ∈ Dom` and all `w ∈ W`.
The law of `R(u)` is the probability mass function `R u`. -/
def IsLocalRandomizerPMF {Dom W : Type*} (R : Dom → PMF W) (ε : ℝ) : Prop :=
  ∀ u u' : Dom, ∀ w : W, R u w ≤ ENNReal.ofReal (Real.exp ε) * R u' w

/-- The first `k` answers `(a_0, …, a_{k−1})` of an answer sequence `a : Fin t → W`. -/
def histPrefix {W : Type*} {t : ℕ} (a : Fin t → W) (k : Fin t) : Fin k → W :=
  fun j => a ⟨j, j.isLt.trans k.isLt⟩

/-- Definitions 5.2 and 5.3 (p. 19): an (interactive) ε-local algorithm on databases
`z ∈ Domⁿ` that makes `t` queries to the LR oracle `LR_z`. Before its `k`-th query (`k = 0, …, t−1`)
it has seen the answers `a : Fin k → W` to its earlier queries and chooses, as a function of them,
an index `idx k a` of the database, an `eps k a`-local randomizer `R k a`, and receives a sample of
`R k a (z (idx k a))`. Along every answer sequence the budgets spent on each index `i` sum to at
most `ε`. The output is `out` of the `t` answers. -/
structure LocalAlg (Dom W Out : Type*) [MeasurableSpace Dom] (n t : ℕ) (ε : ℝ) where
  /-- the database index of the `k`-th LR-oracle call -/
  idx : (k : Fin t) → (Fin k → W) → Fin n
  /-- the local randomizer of the `k`-th call -/
  R : (k : Fin t) → (Fin k → W) → Dom → PMF W
  /-- the privacy parameter of the `k`-th randomizer -/
  eps : (k : Fin t) → (Fin k → W) → ℝ
  /-- `Pr[R(u) = w]` is a measurable function of the input `u` -/
  measurable_R : ∀ k a w, Measurable fun u => R k a u w
  /-- each `R k a` is an `eps k a`-local randomizer -/
  isLocal : ∀ k a, IsLocalRandomizerPMF (R k a) (eps k a)
  /-- Definition 5.3: for every index `i`, `ε_1 + ⋯ + ε_k ≤ ε` over the calls on `i` -/
  budget : ∀ (a : Fin t → W) (i : Fin n),
    ∑ k ∈ Finset.univ.filter (fun k => idx k (histPrefix a k) = i), eps k (histPrefix a k) ≤ ε
  /-- the output, a function of the answers -/
  out : (Fin t → W) → Out

namespace LocalAlg

variable {Dom W Out : Type*} [MeasurableSpace Dom] {n t : ℕ} {ε : ℝ}

/-- Definition 5.3 (p. 19): a local algorithm is noninteractive if it prepares all its LR-oracle
queries before receiving any answers: the index, the randomizer and its budget of every call do not
depend on earlier answers. -/
def IsNoninteractive (A : LocalAlg Dom W Out n t ε) : Prop :=
  ∀ (k : Fin t) (a a' : Fin k → W), A.idx k a = A.idx k a' ∧ A.R k a = A.R k a' ∧
    A.eps k a = A.eps k a'

/-- The probability that `A`, run on the fixed database `z`, receives the answer sequence `a`:
the LR oracle draws each answer from `R k (a|k) (z (idx k (a|k)))` with fresh coins. -/
noncomputable def transcriptMass (A : LocalAlg Dom W Out n t ε) (z : Fin n → Dom)
    (a : Fin t → W) : ENNReal :=
  ∏ k : Fin t, A.R k (histPrefix a k) (z (A.idx k (histPrefix a k))) (a k)

/-- A's output distribution when the database `z` has `n` entries drawn i.i.d. from `P`
(Lemma 5.8): `Pr[A outputs o] = Σ_{a : out a = o} E_{z ∼ Pⁿ} Pr[A receives a on z]`. -/
noncomputable def iidOutputLaw (A : LocalAlg Dom W Out n t ε) (P : Measure Dom) [SigmaFinite P]
    (o : Out) : ENNReal :=
  ∑' a : Fin t → W, {a : Fin t → W | A.out a = o}.indicator
    (fun a => ∫⁻ z, A.transcriptMass z a ∂(Measure.pi fun _ : Fin n => P)) a

end LocalAlg

end PrivLearn.SQSim


