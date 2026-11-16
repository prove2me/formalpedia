-- Prove2me | Definitions.Def_AcceptSubcube_Supplement_RandApproxOn
-- name    : AcceptSubcube_Supplement_RandApproxOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:49:02.110591+00:00
-- url     : https://prove2.me/theorems/c4ac1204-af8e-4f25-8c26-5e161c9d019a
-- title:
--   Randomized and deterministic polynomial-time approximation on an instance family; expected cost; the ratio of Theorem 1.4
-- statement:
--   Let $\mathcal D$ be a family of instances and $\rho$ a ratio (a real number for each instance).
--
--   1. A **randomized polynomial-time $\rho$-approximation on $\mathcal D$ succeeding with probability at least $p_0$** is a polynomial-time machine reading an instance $\mathcal I$ and a coin string, with coin strings of length $p(|\mathcal I|)$ for a fixed polynomial $p$, such that on every $\mathcal I\in\mathcal D$
--   $$\Pr_w\big[C_{\mathcal I}(Y_w)\le\rho(\mathcal I)\,\mathrm{OPT}(\mathcal I)\big]\ge p_0 ,$$
--   where $Y_w$ is the output on coin string $w$, drawn uniformly.
--   2. A **randomized polynomial-time $\rho$-approximation in expectation on $\mathcal D$**: the same, with $\mathbb E_w[C_{\mathcal I}(Y_w)]\le\rho(\mathcal I)\,\mathrm{OPT}(\mathcal I)$, the expectation being the average over the $2^N$ coin strings of length $N=p(|\mathcal I|)$.
--   3. A **deterministic polynomial-time $\rho$-approximation on $\mathcal D$**: a polynomial-time machine on the instance alone with $C_{\mathcal I}(Y)\le\rho(\mathcal I)\,\mathrm{OPT}(\mathcal I)$ on every $\mathcal I\in\mathcal D$.
--
--   The ratio of Theorem 1.4 is
--   $$A\,\mathrm{OPT}\ (k=2),\qquad A\sqrt{\log(\mathrm{OPT}+2)}\,\mathrm{OPT}\ (k=3),\qquad A\big(n/\log(n+2)\big)^{k-3}\mathrm{OPT}\ (k\ge4).$$
--
--   These notions are the hypotheses of the hardness theorems; outside $\mathcal D$ the machine is unconstrained.
--
--   **Formalization Note** The machine model is that of the published `theorem_1_1`: Mathlib's `Turing.TM2ComputableInPolyTime` over the published encoders `encInstCoins`/`encInst` and `encAssign`, outputs read as assignments by `asg`, probabilities as exact fractions of coin strings (`coinProb`). Natural logarithms.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 7.2, p.35 (probability p₀ or expectation); Theorem 1.2, p.5; Theorem 1.4, p.6

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_encInst
import Definitions.Def_AcceptSubcube_coinFrac

namespace AcceptSubcube.Supplement

open AcceptSubcube

/-- **Average over fair coins**: the mean of `f` over the `2^N` coin strings of length `N`. -/
noncomputable def coinAvg (N : ℕ) (f : List Bool → ℝ) : ℝ :=
  (∑ w : Fin N → Bool, f (List.ofFn w)) / 2 ^ N

/-- **Expected cost** `E[C_I(Y)]` of the output of `alg` on `I`, coin strings of length
`p(|enc I|)` drawn uniformly. -/
noncomputable def expCost (I : GInst) (p : Polynomial ℕ) (alg : GInst × List Bool → List Bool) :
    ℝ :=
  coinAvg (p.eval (encInst I).length) (fun w => (cost I (asg I (alg (I, w))) : ℝ))

/-- **A randomized polynomial-time `ρ`-approximation on the instances `D`, succeeding with
probability at least `p₀`**: a TM2 polynomial-time machine on (instance, coin string) and a coin
length polynomial `p` such that on every `I` with `D I` the output `Y` satisfies
`C_I(Y) ≤ ρ(I)·OPT(I)` for at least a `p₀` fraction of the coin strings of length `p(|enc I|)`.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 7.2, p.35: "If a randomized
polynomial-time algorithm outputs, on every instance of C, an assignment Y with
P[C_I(Y) ≤ c N^{e−ε} OPT(I)] ≥ p₀"; Theorem 1.2, p.5 ("succeeding with a fixed positive
probability").

**Formalization Note.** The machine model is that of the published `theorem_1_1`
(`Turing.TM2ComputableInPolyTime` over `encInstCoins`, output read by `asg`); the probability is the
exact fraction of coin strings (`coinProb`). `D` is the family of instances on which the algorithm
is assumed to work; outside it the machine is unconstrained. -/
def RandApproxOn (D : GInst → Prop) (ρ : GInst → ℝ) (p₀ : ℝ) : Prop :=
  ∃ (p : Polynomial ℕ) (alg : GInst × List Bool → List Bool),
    Nonempty (Turing.TM2ComputableInPolyTime encInstCoins encAssign alg) ∧
    ∀ I : GInst, D I →
      p₀ ≤ coinProb I p (fun w => (cost I (asg I (alg (I, w))) : ℝ) ≤ ρ I * (OPT I : ℝ))

/-- **A randomized polynomial-time `ρ`-approximation in expectation on `D`**:
`E[C_I(Y)] ≤ ρ(I)·OPT(I)` on every `I` with `D I` (Lemma 7.2, p.35: "or with
E[C_I(Y)] ≤ c N^{e−ε} OPT(I)"). Same machine model as `RandApproxOn`. -/
def RandApproxExpOn (D : GInst → Prop) (ρ : GInst → ℝ) : Prop :=
  ∃ (p : Polynomial ℕ) (alg : GInst × List Bool → List Bool),
    Nonempty (Turing.TM2ComputableInPolyTime encInstCoins encAssign alg) ∧
    ∀ I : GInst, D I → expCost I p alg ≤ ρ I * (OPT I : ℝ)

/-- **A deterministic polynomial-time `ρ`-approximation on `D`**: a TM2 polynomial-time machine on
the instance alone whose output satisfies `C_I(Y) ≤ ρ(I)·OPT(I)` on every `I` with `D I`
(Theorem 1.2, p.5: "For deterministic algorithms the conclusions are P = NP"). -/
def DetApproxOn (D : GInst → Prop) (ρ : GInst → ℝ) : Prop :=
  ∃ alg : GInst → List Bool,
    Nonempty (Turing.TM2ComputableInPolyTime encInst encAssign alg) ∧
    ∀ I : GInst, D I → (cost I (asg I (alg I)) : ℝ) ≤ ρ I * (OPT I : ℝ)

/-- **The guarantee of Theorem 1.4** (Cai, Jiang, Liu, STOC 2027 submission, manuscript sha256
66626baf…, Theorem 1.4, p.6): `A·OPT` (`k = 2`), `A √log(OPT + 2) · OPT` (`k = 3`),
`A (n/log(n + 2))^{k−3} · OPT` (`k ≥ 4`); natural logarithms (p.9). -/
noncomputable def ratio14 (k : ℕ) (A : ℝ) (I : GInst) : ℝ :=
  if k = 2 then A * (OPT I : ℝ)
  else if k = 3 then A * Real.sqrt (Real.log ((OPT I : ℝ) + 2)) * (OPT I : ℝ)
  else A * ((I.n : ℝ) / Real.log ((I.n : ℝ) + 2)) ^ (k - 3) * (OPT I : ℝ)

end AcceptSubcube.Supplement


