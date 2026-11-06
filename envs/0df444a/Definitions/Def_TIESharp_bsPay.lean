-- Prove2me | Definitions.Def_TIESharp_bsPay
-- name    : TIESharp_bsPay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:55.374591+00:00
-- url     : https://prove2.me/theorems/9fa572a9-7c33-4e05-819b-9463f82549d1
-- title:
--   Bounded-Square expected per-job payment $\pi_{ij}(t)$
-- statement:
--   The expected per-job payment of the Bounded-Square mechanism to machine $i$ for job $j$ is
--   $$\pi_{ij}(t)=t_{ij}\,q_{ij}(t)+\int_{t_{ij}}^{\infty}q_{ij}(u,t_{-ij})\,du,$$
--   where only entry $(i,j)$ varies in the integral; machine $i$'s expected payment is $\sum_j\pi_{ij}(t)$.
--
--   **Formalization Note.** The integral is a Bochner integral over $(t_{ij},\infty)$; Theorem 3.3 states separately that its integrand is integrable, so it is never a junk zero.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §3.2, p.10; (5.1), p.22

import Mathlib
import Definitions.Def_TIESharp_bsCol
import Definitions.Def_TIESharp_bsProb

set_option autoImplicit false

namespace TIESharp

/-- The **expected per-job payment** of the Bounded-Square mechanism (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §3.2, p.10, and (5.1), p.22):
`π_ij(t) = t_ij q_ij(t) + ∫_{t_ij}^∞ q_ij(u, t_{-ij}) du`, "where only entry (i, j) varies in the
integral". Machine `i`'s expected payment is `Σ_j π_ij(t)`.

**Formalization Note.** The integrand replaces entry `i` of column `t_{·j}` by `u`
(`Function.update`). The integral is a Bochner integral over `(t_ij, ∞)`; its integrability is a
separate clause of Theorem 3.3 (`TIESharp.theorem_3_3`), so it is not a junk zero. -/
noncomputable def bsPay {n m : ℕ} (t : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  t i j * bsProb t i j +
    ∫ u in Set.Ioi (t i j), bsCol (Function.update (fun k => t k j) i u) i

end TIESharp


