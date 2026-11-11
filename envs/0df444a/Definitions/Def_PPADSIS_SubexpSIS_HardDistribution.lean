-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_HardDistribution
-- name    : PPADSIS_SubexpSIS_HardDistribution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:47:45.230199+00:00
-- url     : https://prove2.me/theorems/5f46842e-f285-4049-832c-2ac173bb9efa
-- title:
--   Hard distributions of a search problem (p. 21)
-- statement:
--   Let a search problem have instances $I$ with descriptions $\mathrm{desc}(I)$, a promise, and a solution relation between an instance and an output string. A distribution $D(1^\lambda)$ over instances is **hard** (p. 21) if
--
--   1. it is sampled in polynomial time: $D$ is one probabilistic polynomial-time algorithm that reads $1^\lambda$ and polynomially many coins;
--   2. for all sufficiently large $\lambda$, every output of $D(1^\lambda)$ is the description of an instance satisfying the promise;
--   3. for every polynomial-size adversary $A$ there is a negligible $\delta$ with
--   $$\Pr\bigl[A_\lambda(x)\text{ is a solution of }x \;:\; x\leftarrow D(1^\lambda)\bigr]\le\delta(\lambda)\qquad\text{for every }\lambda,$$
--   the probability over the sampler's and the adversary's coins. An output $x$ that describes no instance has no solution.
--
--   The paper: "A distribution $D(1^\lambda)$ over RSVL instances, sampled in polynomial time, is hard if, for all sufficiently large $\lambda$, it is supported on instances satisfying the promise, and every adversary $A$ outputs a solution to $D(1^\lambda)$ with probability at most $\mathrm{negl}(\lambda)$. Hard distributions for EOML are defined analogously."
--
--   **Formalization Note** "$\le\mathrm{negl}(\lambda)$" is read as a negligible bound $\delta$ chosen after the adversary and holding at every $\lambda$; since a negligible function may be large at finitely many $\lambda$, this is the same as a bound for all large $\lambda$.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 21, paragraph after Definition 3.2

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Negligible
import Definitions.Def_PPADSIS_SubexpSIS_Adversary

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

/-- A **hard distribution** of a search problem (Choudhuri, *PPAD Hardness from SIS*, STOC 2027
submission (manuscript sha256 17abad73…), p. 21: "A distribution D(1^λ) over RSVL instances,
sampled in polynomial time, is hard if, for all sufficiently large λ, it is supported on instances
satisfying the promise, and every adversary A outputs a solution to D(1^λ) with probability at most
negl(λ). Hard distributions for EOML are defined analogously.").

The problem has instances `α` with descriptions `enc`, a promise, and a solution relation `sol I y`
between an instance and an output string. The distribution is given by one sampler `D` that reads
`1^λ` and polynomially many coins:
1. `D` is probabilistic polynomial time;
2. for all sufficiently large `λ`, every output of `D(1^λ)` is the description of an instance
   satisfying the promise;
3. for every polynomial-size adversary `A` there is a negligible `δ` with
   `Pr[A_λ(x) is a solution of x : x ← D(1^λ)] ≤ δ(λ)` for every `λ`, the probability over the
   sampler's and the adversary's coins. An output `x` that describes no instance has no
   solution. -/
def IsHardDistribution {α : Type} (enc : α → List Bool) (promise : α → Prop)
    (sol : α → List Bool → Prop) (D : CoinAlg unary) : Prop :=
  D.IsPPT ∧
  (∃ lam₀ : ℕ, ∀ lam ≥ lam₀, ∀ x, D.InSupport lam x → ∃ I : α, x = enc I ∧ promise I) ∧
  ∀ A : Adversary, A.PolySize → ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ lam : ℕ,
    coinAvg (D.numCoins lam) (fun c =>
      A.prob lam (D.run lam (List.ofFn c))
        (fun y => ∃ I : α, D.run lam (List.ofFn c) = enc I ∧ sol I y)) ≤ δ lam

end PPADSIS.SubexpSIS


