-- Prove2me | Definitions.Def_MLManagesComplexity_CompIndist
-- name    : MLManagesComplexity_CompIndist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:35.486973+00:00
-- url     : https://prove2.me/theorems/f031fa85-3bd2-404f-aaab-3040e2596f0d
-- title:
--   Computational indistinguishability against polynomial-size probabilistic circuits
-- statement:
--   A **probabilistic circuit** $A$ reads an input $x$ followed by uniformly random coin bits; $\Pr[A(x)=1]$ is the probability over the coins that it outputs the single bit $1$ (a circuit with the wrong number of inputs always rejects). For a distribution $D$ on $\{0,1\}^n$, $\Pr_{x\sim D}[A(x)=1]=\sum_x D(x)\Pr[A(x)=1]$.
--
--   A family $A=(A_n)$ of probabilistic circuits has **polynomial size** if for one constant $c$ every $A_n$ is well formed and has size (inputs, coin inputs included, plus gates) at most $(n+2)^c$.
--
--   Two distribution families $D=(D_n)$ and $D'=(D'_n)$ on $\{0,1\}^n$ are **computationally indistinguishable** if for every polynomial-size family $A$ of probabilistic circuits there is a negligible function $\nu$ (which may depend on $A$) such that for all $n$
--
--   $$
--   \Bigl|\Pr_{x\sim D_n}[A_n(x)=1]-\Pr_{x\sim D'_n}[A_n(x)=1]\Bigr|\ \le\ \nu(n).
--   $$
--
--   This is the hypothesis of Theorem 6.1 and the security condition of a cryptographic pseudorandom generator.
--
--   **Formalization Note** "P/poly algorithm" is read as a nonuniform family of probabilistic circuits, as in §3.3 ("probabilistic P/poly algorithms") and the proof of Theorem 6.1; for nonuniform families, fixing the best coins at each length gives a deterministic family of no larger size and at least the same advantage, so the notion coincides with the deterministic one. Probabilistic circuits are the published `PPADSIS.SubexpSIS.ProbCircuit`.
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Theorem 6.1, p.10 (PDF p.11); §3.3, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Adversary
import Definitions.Def_MLManagesComplexity_Negligible
import Definitions.Def_MLManagesComplexity_lexCDF

set_option autoImplicit false

open PPADSIS.SubexpSIS AutoregressiveCompression.Main

namespace MLManagesComplexity

/-- `Pr[A(x) = 1]`: the probability, over its uniform coins, that the probabilistic circuit `A`
outputs the one-bit string `1` on input `x ∈ {0,1}^n` (a run with the wrong input arity rejects). -/
noncomputable def accept (A : ProbCircuit) {n : ℕ} (x : Fin n → Bool) : ℝ :=
  A.prob (List.ofFn x) (fun y => y = [true])

/-- `Pr_{x∼D}[A(x) = 1]`: the acceptance probability of `A` on a sample of `D`, over the sample
and the coins of `A`. -/
noncomputable def acceptUnder (A : ProbCircuit) {n : ℕ} (D : PMF (Fin n → Bool)) : ℝ :=
  ∑ x, mass D x * accept A x

/-- A family `A = (Aₙ)` of probabilistic circuits has **polynomial size**: one exponent `c`
with every `Aₙ` well formed and of size (inputs, coin inputs included, plus gates) at most
`(n+2)^c`. -/
def PolySizeDist (A : ℕ → ProbCircuit) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, (A n).circ.WF ∧ (A n).circ.size ≤ (n + 2) ^ c

/-- Two families `D, D'` of distributions on `{0,1}^n` are **computationally
indistinguishable** (Fortnow, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…),
Theorem 6.1, printed p.10, PDF p.11: "for every P/poly algorithm A,
|Pr_{x∼D}[A(x) = 1] − Pr_{x∼D′}[A(x) = 1]| ≤ negl(n)"; §3.3, printed p.5, PDF p.6: "for all
probabilistic P/poly algorithms A"): for every polynomial-size family `A` of probabilistic
circuits there is a negligible `ν` (depending on `A`) with
`|Pr_{x∼Dₙ}[Aₙ(x) = 1] − Pr_{x∼D'ₙ}[Aₙ(x) = 1]| ≤ ν(n)` for every `n`.

**Formalization Note** A "P/poly algorithm" is a nonuniform family of probabilistic Boolean
circuits (published `PPADSIS.SubexpSIS.ProbCircuit`: input followed by uniform coins), the coins
counted in the size. Since the family is nonuniform, fixing the best coins at each `n` gives a
deterministic family of no larger size and at least the same advantage, so the notion is the same
as with deterministic circuits. -/
def CompIndist (D D' : DistFamily) : Prop :=
  ∀ A : ℕ → ProbCircuit, PolySizeDist A →
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ n : ℕ, |acceptUnder (A n) (D n) - acceptUnder (A n) (D' n)| ≤ ν n

end MLManagesComplexity


