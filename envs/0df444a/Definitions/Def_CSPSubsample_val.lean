-- Prove2me | Definitions.Def_CSPSubsample_val
-- name    : CSPSubsample_val
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:18:22.334428+00:00
-- url     : https://prove2.me/theorems/be9300cb-0c4f-48a7-935d-1f42ffe10a34
-- title:
--   Value $\mathrm{val}(\phi)=n^{-k}\sum_{w\in W}P_w(\phi|_w)$ and optimum $\mathrm{OPT}$
-- statement:
--   For a $k$-CSP instance on $n$ variables, the **value** of an assignment $\phi\in[q]^n$ is
--   $$
--   \mathrm{val}(\phi)=\frac{1}{n^k}\sum_{w\in W}P_w(\phi|_w),
--   $$
--   and the **optimum** is $\mathrm{OPT}=\max_{\phi\in[q]^n}\mathrm{val}(\phi)$.
--
--   The normalization is the power $n^k$, although $|W|=n(n-1)\cdots(n-k+1)$; the paper adopts this convention because it simplifies the proofs, so the largest possible value is $n(n-1)\cdots(n-k+1)/n^k$, which tends to $1$ for $k=o(n)$.
--
--   **Formalization Note** $\mathrm{OPT}$ is a supremum over the finite set of assignments, attained whenever an assignment exists ($q\ge1$ or $n=0$). For $q=0$ and $n\ge1$ there is no assignment and Lean returns $0$.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Definition 2.1 and the definition of OPT, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_CSPSubsample_Instance

set_option autoImplicit false

namespace CSPSubsample

/-- The **value** of an assignment `ϕ ∈ [q]^n`,
`val(ϕ) = (1/n^k) ∑_{w ∈ W} P_w(ϕ|_w)` (arXiv:2608.00203 (PDF sha256 fd9ae011…), Definition 2.1,
p.5 = PDF p.7).

**Formalization Note** The normalization is the *power* `n^k`, not the number `n(n−1)⋯(n−k+1)`
of tuples, as the paper states ("we normalize by n^k even though |W| = n^{\underline k}", p.5).
`ϕ|_w` is `ϕ ∘ w`. -/
noncomputable def val {n k q : ℕ} (I : Instance n k q) (ϕ : Fin n → Fin q) : ℝ :=
  (∑ w : Fin k ↪ Fin n, I.P w (ϕ ∘ w)) / (n : ℝ) ^ k

/-- `OPT = max_{ϕ ∈ [q]^n} val(ϕ)` (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.5 = PDF p.7).

**Formalization Note** Written as `⨆` over the finite type of assignments; for `q ≥ 1` or
`n = 0` the type is nonempty and the supremum is attained, i.e. it is the maximum. For `q = 0`,
`n ≥ 1` there is no assignment and Lean returns `0`. -/
noncomputable def OPT {n k q : ℕ} (I : Instance n k q) : ℝ :=
  ⨆ ϕ : Fin n → Fin q, val I ϕ

end CSPSubsample


