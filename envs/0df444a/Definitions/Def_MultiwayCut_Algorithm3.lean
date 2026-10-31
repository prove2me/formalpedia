-- Prove2me | Definitions.Def_MultiwayCut_Algorithm3
-- name    : MultiwayCut_Algorithm3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:25.176998+00:00
-- url     : https://prove2.me/theorems/239f1e42-4ca1-4b3e-99f7-9f422c79cc81
-- title:
--   Algorithm 3: the $p$-mixture of exponential clocks and CKR on the transformed simplex
-- statement:
--   **Algorithm 3** (§3.2, p.5), on input points $\{\mathbf u\}\subseteq\Delta_k$, a map $f:\Delta_k\to[0,1]^k$ and $p\in[0,1]$: with probability $p$ execute the exponential clocks algorithm on $\{\mathbf u\}$; with probability $1-p$ execute CKR on $\{f(\mathbf u)\}$.
--
--   Its separation probability is
--   $$\mathrm{sep}_{3}(\mathbf u,\mathbf v)=p\cdot\mathrm{sep}_{\exp}(\mathbf u,\mathbf v)+(1-p)\cdot\mathrm{sep}_{\mathrm{CKR}}(f(\mathbf u),f(\mathbf v)),$$
--   and the **expected weight of the cut** on an embedding $x$ of an instance is
--   $$\mathrm{cost}_3(x)=\sum_{e=(u,v)\in E} w_e\,\mathrm{sep}_3(x_u,x_v).$$
--
--   **Formalization Note** By linearity of expectation the expected cut weight is the weighted sum of the edges' separation probabilities; it is defined as that sum.
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, §3.2, p.5, Algorithm 3

import Mathlib
import Definitions.Def_MultiwayCut_Instance
import Definitions.Def_MultiwayCut_ExpClocks
import Definitions.Def_MultiwayCut_CKR

namespace MultiwayCut

variable {V : Type*} {k : ℕ} [NeZero k]

/-- **Separation probability of Algorithm 3**, Buchbinder, Schwartz & Weizman, *Simplex
Transformations and the Multiway Cut Problem*, manuscript of Nov. 1, 2016, §3.2, p.5: with
probability `p` run the exponential clocks algorithm (Algorithm 1) on `{u}`, with probability
`1 − p` run CKR (Algorithm 2) on the transformed points `{f(u)}`. The probability that `u` and `v`
receive different labels is `p · Pr_exp[u, v separated] + (1 − p) · Pr_CKR[f(u), f(v) separated]`. -/
noncomputable def alg3Sep (p : ℝ) (f : (Fin k → ℝ) → Fin k → ℝ) (u v : Fin k → ℝ) : ℝ :=
  p * sepExp u v + (1 - p) * sepCKR (f u) (f v)

/-- **Expected weight of the cut produced by Algorithm 3** (§3.2, p.5) on the embedding `x`:
`Σ_{e=(u,v)∈E} w_e · Pr[g(u) ≠ g(v)]`.

**Formalization Note.** By linearity of expectation the expected cut weight is the
weighted sum of the separation probabilities of the edges' endpoints; it is defined directly
as that sum. -/
noncomputable def alg3Cost (I : Instance V k) (p : ℝ) (f : (Fin k → ℝ) → Fin k → ℝ)
    (x : V → Fin k → ℝ) : ℝ :=
  ∑ e ∈ I.E, I.w e * alg3Sep p f (x e.1) (x e.2)

end MultiwayCut


