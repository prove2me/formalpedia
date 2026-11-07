-- Prove2me | Definitions.Def_GuardedSSSP_LogHierarchy
-- name    : GuardedSSSP_LogHierarchy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:00.814487+00:00
-- url     : https://prove2.me/theorems/9399d349-2c94-43d9-be40-6bd07406dace
-- title:
--   Regularized iterated logarithms $L_i$, the factors $f_d$, the product $\Phi$, and $\log^*_2$
-- statement:
--   For real $x\ge0$ and integers $i\ge1$, $d\ge0$, define
--
--   $$L_1(x)=\log_2(2+x),\qquad L_{i+1}(x)=\log_2(4+L_i(x)),$$
--
--   $$f_d(x)=\Big(\prod_{i=1}^{d}L_i(x)^{2^{-i}}\Big)\big(L_{d+1}(x)L_{d+2}(x)\big)^{2^{-(d+1)}},\qquad \Phi(x)=\prod_{i\ge1}L_i(x)^{2^{-i}}.$$
--
--   Also $\psi(y)=\log_2(4+y)$, so that $L_{i+1}=\psi\circ L_i$, and $\log^*_2x$ is the least number of binary logarithms needed to bring $x$ to a value at most one.
--
--   $\Phi(K)$ is the factor by which the running time of Theorem 1.1 exceeds the benchmark $K$, and $f_d$ is the factor achieved by a fixed generation $d$ of the paper's hierarchy.
--
--   **Formalization Note** $L_0$ is an unused placeholder with value $0$. Real powers are `Real.rpow`; every $L_i(x)\ge1$ for $x\ge0$. $\Phi(x)$ is written as $\exp\big(\sum_{i\ge1}2^{-i}\log L_i(x)\big)$, an absolutely convergent series for $x\ge0$, instead of an infinite product whose junk value could hide non-convergence. $\log^*_2x$ is an infimum over $\mathbb N$ and equals $0$ for $x\le1$.
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), §3.1, displays (9)–(11), p.6 (PDF p.7); §3.2, p.7 (PDF p.8); §7, p.14 (PDF p.15)

import Mathlib

namespace GuardedSSSP

/-!
# The regularized iterated logarithms `L_i`, the factors `f_d`, the product `Φ`, and `log*₂`

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), §3.1, displays (9)–(11), p.6 (PDF p.7); §3.2, p.7 (PDF p.8);
§7, p.14 (PDF p.15). For `x ≥ 0` and integers `d ≥ 0`:

* `L₁(x) = log₂(2 + x)` and `L_{i+1}(x) = log₂(4 + L_i(x))` (9);
* `f_d(x) = (∏_{i=1}^{d} L_i(x)^{2^{−i}}) · (L_{d+1}(x) L_{d+2}(x))^{2^{−(d+1)}}` (10);
* `Φ(x) = ∏_{i≥1} L_i(x)^{2^{−i}}` (11);
* `ψ(y) = log₂(4 + y)` (§7, p.14);
* `log*₂ x`, "the least number of binary logarithms needed to reach a value at most one" (§3.2, p.7).

**Formalization Note.**
* `L i x` is the paper's `L_i(x)` for `i ≥ 1`. The value `L 0 x = 0` is a placeholder that no statement of
  the mission uses.
* Powers with real exponents are `Real.rpow`. On `x ≥ 0` every `L_i(x) ≥ 1`, so all bases are positive.
* `Φ(x)` is written as `exp(∑_{i≥1} 2^{−i} log L_i(x))`. The series converges absolutely for `x ≥ 0`, so
  this is the infinite product (11); a `tprod`, whose junk value `1` would hide non-convergence, is not
  used. Lemma 7.2 states that the partial products converge to this value.
* `logStar x = sInf {k | (log₂)^[k] x ≤ 1}` over `ℕ`, a real argument. It is `0` for `x ≤ 1`; the mission
  only uses it at arguments `x > 1`, where the set is nonempty.
-/

/-- The regularized iterated logarithm `L_i(x)`, display (9). Index `0` is an unused placeholder. -/
noncomputable def L : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, x => Real.logb 2 (2 + x)
  | (i + 2), x => Real.logb 2 (4 + L (i + 1) x)

/-- `ψ(y) = log₂(4 + y)` (§7, p.14), so that `L_{i+1} = ψ ∘ L_i`. -/
noncomputable def psi (y : ℝ) : ℝ := Real.logb 2 (4 + y)

/-- The generation-`d` factor `f_d(x)`, display (10). -/
noncomputable def f (d : ℕ) (x : ℝ) : ℝ :=
  (∏ i ∈ Finset.Icc 1 d, L i x ^ ((2 : ℝ) ^ (-(i : ℝ)))) *
    (L (d + 1) x * L (d + 2) x) ^ ((2 : ℝ) ^ (-((d : ℝ) + 1)))

/-- The regularized iterated-logarithm product `Φ(x) = ∏_{i≥1} L_i(x)^{2^{−i}}`, display (11), written as
the exponential of the absolutely convergent series of logarithms. -/
noncomputable def Phi (x : ℝ) : ℝ :=
  Real.exp (∑' i : ℕ, (2 : ℝ) ^ (-((i : ℝ) + 1)) * Real.log (L (i + 1) x))

/-- `log*₂ x`: the least number of binary logarithms needed to bring `x` to a value at most one. -/
noncomputable def logStar (x : ℝ) : ℕ := sInf {k : ℕ | (Real.logb 2)^[k] x ≤ 1}

end GuardedSSSP


