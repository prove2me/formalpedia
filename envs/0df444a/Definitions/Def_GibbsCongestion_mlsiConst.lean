-- Prove2me | Definitions.Def_GibbsCongestion_mlsiConst
-- name    : GibbsCongestion_mlsiConst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:20.871378+00:00
-- url     : https://prove2.me/theorems/7f77aa2a-4a21-46cc-a275-c57b2340727d
-- title:
--   Modified log-Sobolev constant $\rho(P)$
-- statement:
--   The **modified log-Sobolev constant** of a Markov chain $P$ on a finite set $\Omega$ with distribution $\pi$ is
--   $$\rho(P)=\inf\Big\{\frac{\mathcal E_P(f,\log f)}{\mathrm{Ent}_\pi(f)}:\ f:\Omega\to\mathbb R_{\ge0},\ \mathrm{Ent}_\pi(f)\ne0\Big\}.$$
--   Lower bounds on $\rho$ bound the mixing time; the proof of Theorem 4.4 bounds $\rho$ of the relaxed logit dynamics through the constants of its projection and restriction chains.
--
--   **Formalization Note** The value lies in the extended reals, so an empty index set (for instance a one-state chain) gives $+\infty$. The infimum is taken over strictly positive $f$: for $f\ge0$ with a zero, $\mathcal E_P(f,\log f)=+\infty$ as soon as the chain moves between the zero set of $f$ and its support, and otherwise the ratio is a limit of ratios at positive functions, so the infimum is the same. Lean's convention $\log0=0$ would otherwise let such $f$ change it.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, App. A, p.25

import Mathlib
import Definitions.Def_GibbsCongestion_dirichletForm
import Definitions.Def_GibbsCongestion_entropy

namespace GibbsCongestion

/-- The **modified log-Sobolev constant**
`ρ(P) = inf { E_P(f, log f) / Ent_π(f) : f : Ω → ℝ≥0, Ent_π(f) ≠ 0 }`
(Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, App. A, p.25).

**Formalization Note** The value lies in `EReal`, so the infimum over an empty index set is `⊤`
(`+∞`), as for a one-state chain. The infimum runs over strictly positive `f`. For `f ≥ 0` with a
zero, the paper's `E_P(f, log f)` is `+∞` as soon as the chain moves between the zero set of `f`
and its support, and otherwise is a limit of values at positive functions, so the two infima
agree; Lean's convention `Real.log 0 = 0` would instead let such `f` change the infimum. -/
noncomputable def mlsiConst {Ω : Type*} [Fintype Ω] (P : Matrix Ω Ω ℝ) (π : Ω → ℝ) : EReal :=
  ⨅ f : {f : Ω → ℝ // (∀ x, 0 < f x) ∧ entropy π f ≠ 0},
    ((dirichletForm P π f.1 (fun x => Real.log (f.1 x)) / entropy π f.1 : ℝ) : EReal)

end GibbsCongestion


