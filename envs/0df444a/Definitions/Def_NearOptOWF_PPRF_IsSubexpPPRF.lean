-- Prove2me | Definitions.Def_NearOptOWF_PPRF_IsSubexpPPRF
-- name    : NearOptOWF_PPRF_IsSubexpPPRF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:15:16.319895+00:00
-- url     : https://prove2.me/theorems/841a1718-dcb8-444b-b629-f7516b6e7c66
-- title:
--   Sub-exponentially secure puncturable PRF
-- statement:
--   A puncturable PRF $F$ is **sub-exponentially secure** if:
--
--   1. **Efficiency:** keys have length polynomial in $\lambda + n + m$, and the circuit $F_k$, the punctured key $k\{x^*\}$ and the punctured evaluation circuit are each computed in polynomial time;
--   2. **Output length:** $F_k$ has $m$ output bits;
--   3. **Punctured correctness:** the punctured circuit agrees with $F_k$ at every $x \in \{0,1\}^n$ with $x \ne x^*$;
--   4. **Selective security:** there is $\delta > 0$ such that for every polynomial $p$, all sufficiently large $\lambda$, all $n, m \le p(\lambda)$, every $x^* \in \{0,1\}^n$ and every distinguisher circuit $D$ of size at most $p(\lambda)$,
--   $$
--   \Bigl|\Pr_k\bigl[D(k\{x^*\}, F_k(x^*)) = 1\bigr] - \Pr_{k,\,u \leftarrow \{0,1\}^m}\bigl[D(k\{x^*\}, u) = 1\bigr]\Bigr| \le 2^{-\lambda^\delta}.
--   $$
--
--   The paper never defines puncturable PRFs; this is the standard definition (Sahai–Waters; [CCR16]) with sub-exponential, non-uniform security as in §3.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemmas 3.5–3.6, p.9 (PDF p.11); §3, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_NearOptOWF_PPRF
import Definitions.Def_NearOptOWF_accepts
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_LaconicBarrier_coinAvg

namespace NearOptOWF

open LaconicBarrier

/-- `F` is a **sub-exponentially secure puncturable PRF** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 3.5, Lemma 3.6, p.9 (PDF
p.11); "sub-exponentially secure", §3, p.8 (PDF p.10); the paper gives no definition, so the
standard one of Sahai–Waters and Canetti–Chen–Reyzin [CCR16] is used):

1. *efficiency*: keys of polynomial length in `λ + n + m`; one machine computes the circuit `F_k`
   from `(1^λ, 1ⁿ, 1ᵐ, k)`, one computes `k{x*}` from `(1^λ, 1ⁿ, 1ᵐ, k, x*)`, and one computes the
   punctured circuit from `(1^λ, 1ⁿ, 1ᵐ, k{x*})`, each in polynomial time;
2. `F_k` has `m` output wires;
3. *punctured correctness*: the punctured circuit agrees with `F_k` on every `x ∈ {0,1}ⁿ`, `x ≠ x*`;
4. *selective security*, sub-exponential and non-uniform: there is `δ > 0` such that for every
   polynomial `p`, for all sufficiently large `λ`, all `n, m ≤ p(λ)`, every `x* ∈ {0,1}ⁿ` and every
   distinguisher circuit `D` of size at most `p(λ)`, `D` tells `(k{x*}, F_k(x*))` from `(k{x*}, u)`,
   `u` uniform in `{0,1}ᵐ`, with advantage at most `2^{−λ^δ}`.

**Formalization Note** `D` reads the tuple `(k{x*}, value)` in the published tuple encoding. The
advantage bound `2^{−λ^δ}` is the "poly(ε)" of §3 with the polynomial absorbed by `∃ δ`. -/
def PPRF.IsSubexpPPRF (F : PPRF) : Prop :=
  (∃ q : Polynomial ℕ, ∀ lam n m, F.keyLen lam n m ≤ q.eval (lam + n + m)) ∧
  PolyTimeOn (ι := (lam : ℕ) × (n : ℕ) × (m : ℕ) × (Fin (F.keyLen lam n m) → Bool))
    (fun i => [unary i.1, unary i.2.1, unary i.2.2.1, bits i.2.2.2])
    (fun i => (F.circ i.1 i.2.1 i.2.2.1 i.2.2.2).code) ∧
  PolyTimeOn (ι := (lam : ℕ) × (n : ℕ) × (m : ℕ) ×
      ((Fin (F.keyLen lam n m) → Bool) × {xs : List Bool // xs.length = n}))
    (fun i => [unary i.1, unary i.2.1, unary i.2.2.1, bits i.2.2.2.1, i.2.2.2.2.1])
    (fun i => F.punc i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1) ∧
  PolyTimeOn (ι := (lam : ℕ) × (n : ℕ) × (m : ℕ) ×
      ((Fin (F.keyLen lam n m) → Bool) × {xs : List Bool // xs.length = n}))
    (fun i => [unary i.1, unary i.2.1, unary i.2.2.1,
      F.punc i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1])
    (fun i => (F.pcirc i.1 i.2.1 i.2.2.1 (F.punc i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1)).code) ∧
  (∀ (lam n m : ℕ) (k : Fin (F.keyLen lam n m) → Bool), (F.circ lam n m k).outs.length = m) ∧
  (∀ (lam n m : ℕ) (k : Fin (F.keyLen lam n m) → Bool) (xs x : List Bool),
    xs.length = n → x.length = n → x ≠ xs →
      (F.pcirc lam n m (F.punc lam n m k xs)).eval x = (F.circ lam n m k).eval x) ∧
  ∃ δ : ℝ, 0 < δ ∧ ∀ p : Polynomial ℕ, ∀ᶠ lam : ℕ in Filter.atTop,
    ∀ n m : ℕ, n ≤ p.eval lam → m ≤ p.eval lam → ∀ xs : List Bool, xs.length = n →
      ∀ (k : ℕ) (D : MCircuit k), D.size ≤ p.eval lam →
        |coinAvg (F.keyLen lam n m) (fun key => accepts D
            (QAdvFew.PoQOracle.tup [F.punc lam n m key xs, (F.circ lam n m key).eval xs])) -
          coinAvg (F.keyLen lam n m) (fun key => coinAvg m (fun u => accepts D
            (QAdvFew.PoQOracle.tup [F.punc lam n m key xs, bits u])))| ≤
          (2 : ℝ) ^ (-(lam : ℝ) ^ δ)

end NearOptOWF


