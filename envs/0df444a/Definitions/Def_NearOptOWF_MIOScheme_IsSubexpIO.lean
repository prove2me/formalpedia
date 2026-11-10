-- Prove2me | Definitions.Def_NearOptOWF_MIOScheme_IsSubexpIO
-- name    : NearOptOWF_MIOScheme_IsSubexpIO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:54.144928+00:00
-- url     : https://prove2.me/theorems/e2043c18-b024-46ed-a455-5082a799e95d
-- title:
--   Sub-exponentially secure indistinguishability obfuscator
-- statement:
--   An obfuscator $i\mathcal O$ is a **sub-exponentially secure indistinguishability obfuscator** if:
--
--   1. **PPT:** it uses polynomially many coins in $\lambda + n + |C|$, and one machine computes the description of $i\mathcal O(1^\lambda, C; \rho)$ from $(1^\lambda, C, \rho)$ in polynomial time;
--   2. **Correctness:** for every $\lambda$, every circuit $C$ and every coin string, $i\mathcal O(1^\lambda, C; \rho)$ and $C$ are functionally equivalent;
--   3. **Indistinguishability:** there is $\delta > 0$ such that for every polynomial $p$ and all sufficiently large $\lambda$: for every pair of functionally equivalent circuits $C_0, C_1$ with $n \le p(\lambda)$ inputs and equal size $|C_0| = |C_1| \le p(\lambda)$, and every distinguisher circuit $D$ of size at most $p(\lambda)$,
--   $$
--   \bigl|\Pr[D(i\mathcal O(C_0)) = 1] - \Pr[D(i\mathcal O(C_1)) = 1]\bigr| \le 2^{-\lambda^\delta}.
--   $$
--
--   This is the obfuscation hypothesis of Theorem 4.1 and Lemma 3.6.
--
--   **Formalization Note** Distinguishers are non-uniform polynomial-size circuits reading the description of the obfuscated circuit (Definition 3.4 allows "PPT (resp. polynomial-size)", and the proof of Claim 4.7 invokes "the (non-uniform) sub-exponential security of iO"). The two circuits have equal size: the paper realizes this by padding, and without it no obfuscator could exist, since a distinguisher can read the size. The paper's "at most poly($\epsilon$) advantage" with $\epsilon = 2^{-\lambda^\delta}$ is written as the bound $2^{-\lambda^\delta}$ itself; the existential $\delta$ absorbs the polynomial.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.4, p.9 (PDF p.11); §3 "ε-security", p.8 (PDF p.10)

import Mathlib
import Definitions.Def_NearOptOWF_MIOScheme
import Definitions.Def_NearOptOWF_FunEquiv
import Definitions.Def_NearOptOWF_accepts
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_LaconicBarrier_coinAvg

namespace NearOptOWF

open LaconicBarrier

/-- `O` is a **sub-exponentially secure indistinguishability obfuscator** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.4,
p.9 (PDF p.11), with "ε-security" and "sub-exponentially secure", §3, p.8 (PDF p.10)):

1. *PPT*: polynomially many coins, and one machine computes the description of `iO(1^λ, C; ρ)` from
   `(1^λ, C, ρ)` in polynomial time;
2. *correctness*: for every `λ`, every circuit `C` and every coin string, `iO(1^λ, C; ρ)` and `C` are
   functionally equivalent;
3. *indistinguishability*, sub-exponential and non-uniform: there is `δ > 0` such that for every
   polynomial `p`, for all sufficiently large `λ`, for every pair of functionally equivalent circuits
   `C₀, C₁` with `n ≤ p(λ)` inputs and equal size `|C₀| = |C₁| ≤ p(λ)`, and every distinguisher circuit
   `D` of size at most `p(λ)`, `|Pr[D(iO(C₀)) = 1] − Pr[D(iO(C₁)) = 1]| ≤ 2^{−λ^δ}`.

**Formalization Note** `D` reads the description `MCircuit.code` of the obfuscated circuit.
Distinguishers are non-uniform polynomial-size circuits ("PPT (resp. polynomial-size)
distinguisher"; the proof of Claim 4.7, p.19, invokes "the (non-uniform) sub-exponential security of
iO"). The pair has equal size, the convention the paper realizes by padding every obfuscated circuit
to a common size (pp.11–12); without it no obfuscator exists, since a distinguisher reads the size.
"At most poly(ε) advantage" with `ε = 2^{−λ^δ}` is written as the bound `2^{−λ^δ}` itself: an
advantage `2^{−c·λ^δ}` is at most `2^{−λ^{δ/2}}` for large `λ`, so `∃ δ` absorbs the polynomial. -/
def MIOScheme.IsSubexpIO (O : MIOScheme) : Prop :=
  (∃ q : Polynomial ℕ, ∀ lam n s, O.coins lam n s ≤ q.eval (lam + n + s)) ∧
  PolyTimeOn (ι := (lam : ℕ) × (n : ℕ) × (C : MCircuit n) × (Fin (O.coins lam n C.size) → Bool))
    (fun i => [unary i.1, i.2.2.1.code, bits i.2.2.2])
    (fun i => (O.obf i.1 i.2.1 i.2.2.1 i.2.2.2).code) ∧
  (∀ (lam n : ℕ) (C : MCircuit n) (ρ : Fin (O.coins lam n C.size) → Bool),
    FunEquiv (O.obf lam n C ρ) C) ∧
  ∃ δ : ℝ, 0 < δ ∧ ∀ p : Polynomial ℕ, ∀ᶠ lam : ℕ in Filter.atTop,
    ∀ (n : ℕ) (C₀ C₁ : MCircuit n), FunEquiv C₀ C₁ → C₀.size = C₁.size →
      n ≤ p.eval lam → C₀.size ≤ p.eval lam →
      ∀ (k : ℕ) (D : MCircuit k), D.size ≤ p.eval lam →
        |coinAvg (O.coins lam n C₀.size) (fun ρ => accepts D (O.obf lam n C₀ ρ).code) -
          coinAvg (O.coins lam n C₁.size) (fun ρ => accepts D (O.obf lam n C₁ ρ).code)| ≤
          (2 : ℝ) ^ (-(lam : ℝ) ^ δ)

end NearOptOWF


