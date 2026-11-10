-- Prove2me | Definitions.Def_PPSLattice_Params_Valid
-- name    : PPSLattice_Params_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:36:18.401365+00:00
-- url     : https://prove2.me/theorems/df9128f9-ff12-429d-a548-53330735442f
-- title:
--   Valid parameters for Construction 4.6
-- statement:
--   Relative to the exponent $c$ of $\|\mathbf H_{f,x}\|\le m^{c(d+1)}$, parameters are **valid** if for all $\lambda$ and $N\ge1$:
--
--   1. $q$ is prime, $n\ge1$, $\chi\ge1$;
--   2. $n\le(\lambda+\lceil\log N\rceil+2)^a$ and $\chi\le(n+2)^a$ for a constant $a$;
--   3. $n,q,\chi,\tilde\chi,B$ are computable in polynomial time from $(1^\lambda,N)$;
--   4. (error smudging) for every $k$, for all large $\lambda$ and every $N\ge1$, $\lambda^k\chi\lceil\log N\rceil\sqrt m\, m^{c(d_{\max}(N)+1)}\le\tilde\chi$;
--   5. (correctness) for every $k$, for all large $\lambda$ and every $N\ge1$, $\lambda^k\cdot\lambda(4B+2)\le q$.
--
--   **Formalization Note** "$\lambda^{\omega(1)}$" is read as "eventually at least $\lambda^k$ for every $k$", uniformly in $N$ (the adversary chooses $N$); "$m^{\mathrm{polylog}(N)}$" is replaced by $m^{c(d_{\max}+1)}$, the quantity the noise analysis bounds. No lower bound on $B$ is imposed: the security analysis uses $B$ only through $\lambda(4B+2)/q$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.3, Parameters, p.20; Lemmas 4.18, 4.20, p.28; Claim 4.10, p.23

import Mathlib
import Definitions.Def_PPSLattice_Params
import Definitions.Def_PPSLattice_dmax
import Definitions.Def_PPSLattice_encBin
import Definitions.Def_PPSLattice_PolyTimeOn
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- **Valid parameters for Construction 4.6**, relative to the exponent `c` of the homomorphic
computation bound `‖H_{f,x}‖ ≤ m^{c(d+1)}`: for all `λ` and `N ≥ 1`,
1. `q` is prime, `n ≥ 1`, `χ ≥ 1`;
2. `n ≤ (λ + ⌈log N⌉ + 2)^a` and `χ ≤ (n + 2)^a` for one constant `a` (`n = poly(λ, log N)`, `χ = poly(n)`);
3. `n, q, χ, χ̃, B` are computed in polynomial time from `(1^λ, N in binary)`, in binary;
4. (error smudging) for every `k`, for all large `λ` and every `N ≥ 1`:
   `λ^k · χ · ⌈log N⌉ · √m · m^{c(d_max(N)+1)} ≤ χ̃`, with `d_max(N)` the largest depth of `f_S`, `S ⊆ [N]`;
5. (correctness) for every `k`, for all large `λ` and every `N ≥ 1`: `λ^k · λ · (4B + 2) ≤ q`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.3, Parameters, p.20 ("n = poly(λ, log N), χ = poly(n)", "χ̃ > λ^{ω(1)} · χ · ⌈log N⌉ ·
m^{polylog(N)} (Error smudging)", "B = χ · χ̃ · ⌈log N⌉ · m^{polylog(N)} (Accumulated error)",
"q > λ^{ω(1)} · λ · (4B + 2) (Correctness)"); Lemma 4.18, p.28 ("‖e^⊤H_{S,i*}G^{-1}(P)‖ ≤
√m⌈log N⌉χm^{O(d_f)}"); Lemma 4.20, p.28; Claim 4.10, p.23.

**Formalization Note.** "`λ^{ω(1)}`" is read as "eventually at least `λ^k` for every `k`", uniformly in `N`
(the adversary chooses `N`); "`m^{polylog(N)}`" is replaced by the quantity `m^{c(d_max(N)+1)}` that the
noise analysis bounds, which is at most `m^{polylog(N)}` since `d_max(N) = O(log N)`. No lower bound on `B`
is imposed: the security analysis uses `B` only through `λ(4B + 2)/q` (Lemma 4.20); the printed value of
`B` serves the correctness of Construction 4.6, which is not part of this definition. -/
def Params.Valid (P : Params) (c : ℕ) : Prop :=
  (∀ lam N, 1 ≤ N → (P.q lam N).Prime ∧ 1 ≤ P.n lam N ∧ 1 ≤ P.chi lam N) ∧
    (∃ a : ℕ, ∀ lam N, 1 ≤ N →
      P.n lam N ≤ (lam + Nat.clog 2 N + 2) ^ a ∧ P.chi lam N ≤ (P.n lam N + 2) ^ a) ∧
    (∀ f ∈ [P.n, P.q, P.chi, P.chit, P.B],
      PolyTimeOn (fun a : ℕ × ℕ => BeyondDS.tup [encNat a.1, encBin a.2])
        (fun a => encBin (f a.1 a.2))) ∧
    (∀ k : ℕ, ∃ lam0 : ℕ, ∀ lam ≥ lam0, ∀ N ≥ 1,
      (lam : ℝ) ^ k * P.chi lam N * Nat.clog 2 N * Real.sqrt (P.m lam N) *
          (P.m lam N : ℝ) ^ (c * (dmax N + 1)) ≤ P.chit lam N) ∧
    ∀ k : ℕ, ∃ lam0 : ℕ, ∀ lam ≥ lam0, ∀ N ≥ 1,
      (lam : ℝ) ^ k * lam * (4 * P.B lam N + 2) ≤ P.q lam N

end PPSLattice


