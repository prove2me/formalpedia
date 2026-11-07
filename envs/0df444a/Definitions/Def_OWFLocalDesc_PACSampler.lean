-- Prove2me | Definitions.Def_OWFLocalDesc_PACSampler
-- name    : OWFLocalDesc_PACSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:34.16044+00:00
-- url     : https://prove2.me/theorems/60057aea-4152-455f-8e44-139b9dece514
-- title:
--   PAC-style samplable distribution (Definition 2.6)
-- statement:
--   A **PAC-style samplable distribution** $D=(\mu,Q)$ consists of a point sampler and a concept sampler, both polynomial time.
--
--   1. The point sampler $\mu(1^n;\rho)$ uses a tape $\rho$ of length $r_\mu(n)$ and outputs an $n$-bit point.
--   2. The concept sampler $Q(1^n;r)$ uses a tape $r$ of length $q(n)$ and outputs a deterministic concept program $c_r$, whose value $c_r(z)\in\{0,1\}$ on an $n$-bit query $z$ is computed within a polynomial number of steps.
--
--   The tape lengths $r_\mu$ and $q$ are polynomial schedules. A dataset of $m$ points is drawn by choosing $r$ uniformly, drawing $x_1,\dots,x_m$ independently from $\mu$, and setting $y_i=c_r(x_i)$.
--
--   **Formalization Note** Polynomial schedules are the published `QuantumPRC.EffPoly` (polynomially bounded, $1^n\mapsto1^{f(n)}$ polynomial time). The concept sampler and the evaluation of $c_r$ are one polynomial-time map $(1^n,r,z)\mapsto c_r(z)$ (first output bit, $0$ if none): producing $c_r$ in polynomial time and evaluating it within a polynomial $\tau_Q(n)$ steps is the same, so $\tau_Q$ is not a separate field. The helpers `point` and `concept` read $\mu(1^n;\rho)$ and $c_r(z)$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.6, p.13

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QuantumPRC_IsPolyFamily
set_option autoImplicit false

namespace OWFLocalDesc

/-- **PAC-style samplable distribution (Definition 2.6).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
Definition 2.6, p.13: "A PAC-style samplable distribution D = (µ, Q) consists of a point sampler µ
and a concept sampler Q. Both samplers run in polynomial time, and their fixed tape-length schedules
are polynomial-time computable. The point sampler µ(1^n; ρ) uses a tape of length r_µ(n), a fixed
polynomial schedule, and outputs an n-bit point. The concept sampler Q(1^n; r) uses a tape of length
q(n), a fixed polynomial schedule, and outputs a deterministic concept program c_r. The concept
evaluation c_r(z) takes at most τ_Q(n) steps for every r, z of the indicated lengths, where τ_Q is
a fixed polynomial schedule."

**Formalization Note.**
1. Polynomial schedules are the published `QuantumPRC.EffPoly`: polynomially bounded, and
   `1ⁿ ↦ 1^{f(n)}` is polynomial-time.
2. `μ` maps the code of `(1ⁿ, ρ)` to the point; `conc` maps the code of `(1ⁿ, r, z)` to
   `c_r(z)` (its first output bit, `0` if none). Producing `c_r` from `(1ⁿ, r)` in polynomial time
   and evaluating it within a polynomial `τ_Q(n)` steps is the same as a polynomial-time map
   `(1ⁿ, r, z) ↦ c_r(z)`; `τ_Q` is therefore not a separate field. -/
structure PACSampler where
  /-- The point-sampler tape length `r_µ`. -/
  rμ : ℕ → ℕ
  /-- The concept-sampler tape length `q`. -/
  q : ℕ → ℕ
  /-- The point sampler, on the code of `(1ⁿ, ρ)`. -/
  μ : List Bool → List Bool
  /-- Concept evaluation, on the code of `(1ⁿ, r, z)`. -/
  conc : List Bool → List Bool
  rμ_sched : QuantumPRC.EffPoly rμ
  q_sched : QuantumPRC.EffPoly q
  μ_poly : CookPvsNP.PolyTimeComputable μ
  conc_poly : CookPvsNP.PolyTimeComputable conc
  /-- The point sampler outputs an `n`-bit point. -/
  μ_length : ∀ (n : ℕ) (ρ : Fin (rμ n) → Bool),
    (μ (QuantumPRC.tupleCode [QuantumPRC.unary n, List.ofFn ρ])).length = n

/-- The point `µ(1ⁿ; ρ) ∈ {0,1}ⁿ`. -/
def PACSampler.point (D : PACSampler) (n : ℕ) (ρ : Fin (D.rμ n) → Bool) : Fin n → Bool :=
  fun i => (D.μ (QuantumPRC.tupleCode [QuantumPRC.unary n, List.ofFn ρ])).getD i false

/-- The concept value `c_r(z)`. -/
def PACSampler.concept (D : PACSampler) (n : ℕ) (r : Fin (D.q n) → Bool) (z : Fin n → Bool) :
    Bool :=
  (D.conc (QuantumPRC.tupleCode [QuantumPRC.unary n, List.ofFn r, List.ofFn z])).headD false

end OWFLocalDesc


