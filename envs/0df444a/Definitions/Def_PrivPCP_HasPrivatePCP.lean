-- Prove2me | Definitions.Def_PrivPCP_HasPrivatePCP
-- name    : PrivPCP_HasPrivatePCP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:04.553488+00:00
-- url     : https://prove2.me/theorems/9723b744-0209-428c-b58a-3ddf85194f89
-- title:
--   Circuit-SAT has a private PCP with the parameters of Corollary 8.3
-- statement:
--   For a constant $C$, an arity $k$ and a product-expansion constant $\rho$, **Circuit-SAT has a private PCP with the parameters of Corollary 8.3** if there are functions $M(n)$, $q(n)$ and one private-PCP system such that
--
--   1. the prover is polynomial-time samplable;
--   2. the verifier is probabilistic polynomial time, nonadaptive, and reads at most $C\,k\,M(n)^{1/k}$ positions;
--   3. for every $n\ge 1$: $M(n)\le n\log(n+1)\,e^{Ck\log k}$, $q(n)$ is prime and $q(n)\le M(n)^6$;
--   4. completeness is perfect and the soundness error is at most $1-e^{-Ck}$;
--   5. the system is $\nu$-private for
--   $$\nu(n)=\frac{e^{-C(k^3+k^2\log(1/\rho))}}{\log(n+1)}.$$
--
--   This packages the conclusion of Corollary 8.3, with the $O(\cdot)$ written as the one constant $C$.
--
--   **Formalization Note** $\log$ is the natural logarithm.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Corollary 8.3, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_PrivPCP_PrivPCPSys

namespace PrivPCP

/-- **Circuit-SAT has a private PCP with the parameters of Corollary 8.3**, for the absolute constant `C`, the
arity `k` and the product-expansion constant `ρ` (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC 2027
submission manuscript (sha256 c2cac1e0…), Corollary 8.3, p.46; Definition 8.2, p.46). There are a proof length
`M(n)`, a prime alphabet size `q(n)` and one private-PCP system such that:
1. the prover is polynomial-time samplable;
2. the verifier is PPT, nonadaptive, and reads at most `C k M^{1/k}` positions;
3. for every `n ≥ 1`: `M(n) ≤ n log(n+1) e^{C k log k}`, `q(n)` is prime and `q(n) ≤ M(n)^6`;
4. completeness is perfect and the soundness error is at most `1 − e^{−Ck}`;
5. it is `ν`-private for `ν(n) = e^{−C(k³ + k² log(1/ρ))} / log(n+1)`.

**Formalization Note** `log` is the natural logarithm. The `O(·)` of Corollary 8.3 are all the one constant
`C`; the theorem fixes `C` before `k`, `ρ` and `n`. -/
def HasPrivatePCP (C : ℝ) (k : ℕ) (ρ : ℝ) : Prop :=
  ∃ (M q : ℕ → ℕ) (Sys : PrivPCPSys M q),
    Sys.Samplable ∧
    Sys.Efficient (fun n => C * k * (M n : ℝ) ^ ((1 : ℝ) / k)) ∧
    Sys.IsNonadaptive ∧
    (∀ n : ℕ, 1 ≤ n →
      (M n : ℝ) ≤ n * Real.log (n + 1) * Real.exp (C * k * Real.log k) ∧
      (q n).Prime ∧ (q n : ℝ) ≤ (M n : ℝ) ^ 6) ∧
    Sys.Complete ∧
    Sys.Sound (fun _ => 1 - Real.exp (-(C * k))) ∧
    Sys.Private (fun n => Real.exp (-(C * (k ^ 3 + k ^ 2 * Real.log (1 / ρ)))) / Real.log (n + 1))

end PrivPCP


