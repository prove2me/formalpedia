-- Prove2me | Definitions.Def_PPSLattice_LWERegime
-- name    : PPSLattice_LWERegime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:22.635912+00:00
-- url     : https://prove2.me/theorems/496da770-5f4f-45f3-a8e1-23a061673685
-- title:
--   LWE parameters with sub-exponential modulus-to-noise ratio
-- statement:
--   For an exponent $\varepsilon$ and functions $q,\chi:\mathbb N\to\mathbb N$ of the LWE dimension $n$, the family $(n,q(n),\chi(n))$ has **sub-exponential modulus-to-noise ratio** if
--
--   1. $q(n)$ is prime for every $n$;
--   2. $1\le\chi(n)\le(n+2)^c$ for a constant $c$ ($\chi=\mathrm{poly}(n)$);
--   3. $q(n)/\chi(n)\ge 2^{n^\varepsilon}$ for every $n$;
--   4. the binary codes of $q(n)$ and $\chi(n)$ are computed from $1^n$ in polynomial time.
--
--   The paper's parameter paragraph sets "$\chi=n$, $q$ to be a prime of size $2^{\mathrm{poly}(\lambda,\log N)}$", which "will yield $q/\chi=2^{\tilde O(n^\epsilon)}$ for any $\epsilon<1/2$ which would require LWE with sub-exponential modulus-to-noise ratio".
--
--   **Formalization Note** One family is fixed; the goal theorem quantifies over all such families, so its scheme must work with whichever family is hard. No upper bound on $q$ is imposed beyond the computability of its binary code ($\log q\le\mathrm{poly}(n)$).
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.3, Parameters, p.20; Corollary 4.30, p.31

import Mathlib
import Definitions.Def_PPSLattice_encBin
import Definitions.Def_PPSLattice_PolyTimeOn
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- **LWE parameters with sub-exponential modulus-to-noise ratio**, indexed by the dimension `n`:
for an exponent `ε`, a modulus `q(n)` and a Gaussian width `χ(n)`,
1. `q(n)` is prime for every `n`;
2. `1 ≤ χ(n) ≤ (n + 2)^c` for one constant `c` (`χ = poly(n)`);
3. `q(n)/χ(n) ≥ 2^{n^ε}` for every `n`;
4. `q(n)` and `χ(n)`, in binary, are computed from `1^n` in polynomial time.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.3, Parameters, p.20 ("χ = poly(n)", "q to be a prime of size 2^{poly(λ,log N)}", "This will
yield q/χ = 2^{Õ(n^ε)} for any ε < 1/2 which would require LWE with sub-exponential modulus-to-noise
ratio"); Corollary 4.30, p.31.

**Formalization Note.** This is the reading of "LWE with sub-exponential modulus-to-noise ratio":
one family `(q, χ)` with ratio at least `2^{n^ε}`. No upper bound on `q` is imposed beyond the
polynomial-time computability of its binary code (which gives `log q ≤ poly(n)`). The goal theorem
quantifies over every such family, so the scheme must work with whichever family is hard. -/
def LWERegime (ε : ℝ) (q χ : ℕ → ℕ) : Prop :=
  (∀ n, (q n).Prime) ∧ (∀ n, 1 ≤ χ n) ∧ (∃ c : ℕ, ∀ n, χ n ≤ (n + 2) ^ c) ∧
    (∀ n : ℕ, (2 : ℝ) ^ ((n : ℝ) ^ ε) ≤ (q n : ℝ) / (χ n : ℝ)) ∧
    PolyTimeOn (fun n : ℕ => encNat n) (fun n => encBin (q n)) ∧
    PolyTimeOn (fun n : ℕ => encNat n) (fun n => encBin (χ n))

end PPSLattice


