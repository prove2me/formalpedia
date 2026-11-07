-- Prove2me | Definitions.Def_AvgPHETH_S2kTIME
-- name    : AvgPHETH_S2kTIME
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:34.366531+00:00
-- url     : https://prove2.me/theorems/ab890e03-9406-4352-b819-1b13f5f45366
-- title:
--   The class $\mathrm{S}_2^k\mathrm{TIME}^O[t(n)]$
-- statement:
--   $L\in\mathrm{S}_2^k\mathrm{TIME}^O[t(n)]$ if there are predicates $B_0,\dots,B_k$, with $B_0$ the characteristic function of $L$, such that
--
--   $$B_{i-1}(x,h)=1\implies\exists u_i\,\forall v_i\;B_i(x,h,u_i,v_i)=1,$$
--   $$B_{i-1}(x,h)=0\implies\exists v_i\,\forall u_i\;B_i(x,h,u_i,v_i)=0,$$
--
--   with $u_i,v_i\in\{0,1\}^{\ell_i(n)}$, for every $i=1,\dots,k$ and every history $h=(u_1,v_1,\dots,u_{i-1},v_{i-1})$. Here $n=|x|$, the total length $\sum_i\ell_i(n)$ is $O(t(n))$, each $\ell_i(n)$ is computable in time $O(t(n))$, and $B_k$ is computable in time $O(t(n))$ with oracle access to $O$. In particular $\mathrm{S}_2^0\mathrm{TIME}^O[t(n)]=\mathrm{DTIME}^O[t(n)]$.
--
--   **Formalization Note** $O(t)$ is written $Ct+C$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.2, pp.15–16 (PDF 17–18)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_acceptsAt
import Definitions.Def_AvgPHETH_outAt
import Definitions.Def_AvgPHETH_unary
open KarpLiptonOM

namespace AvgPHETH

/-- The class `S₂^kTIME^O[t(n)]` of `k` nested symmetric alternations
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.2, pp.15–16 (PDF 17–18)): there are predicates `B₀, …, B_k`, with `B₀` the characteristic
function of `L`, such that for every `i = 1, …, k`, every input `x` with `n = |x|`, and every history
`h = (u₁, v₁, …, u_{i−1}, v_{i−1})`,
`B_{i−1}(x, h) = 1 ⟹ ∃u_i ∀v_i B_i(x, h, u_i, v_i) = 1` and
`B_{i−1}(x, h) = 0 ⟹ ∃v_i ∀u_i B_i(x, h, u_i, v_i) = 0`, with `u_i, v_i ∈ {0,1}^{ℓ_i(n)}`.
The total length `∑ ℓ_i(n)` is `O(t(n))`, each `ℓ_i(n)` is computable in time `O(t(n))`, and `B_k` is
computable in time `O(t(n))` with oracle `O`.

**Formalization Note** `O(t)` is `C t + C`. Only `B_k` has to be computable; `B₁, …, B_{k−1}` are arbitrary
predicates. In a history `h`, the string at position `j` (from `0`) belongs to round `j/2 + 1`. For `k = 0`
this is `DTIME^O[O(t)]`. -/
def S2kTIME (O : Set (List Bool)) (k : ℕ) (t : ℕ → ℕ) (L : Set (List Bool)) : Prop :=
  ∃ (B : ℕ → List Bool → List (List Bool) → Prop) (ℓ : ℕ → ℕ → ℕ) (C : ℕ) (Mk : OracleTM),
    (∀ x, B 0 x [] ↔ x ∈ L) ∧
    (∀ i, 1 ≤ i → i ≤ k → ∀ (x : List Bool) (h : List (List Bool)), h.length = 2 * (i - 1) →
      (∀ (j : ℕ) (hj : j < h.length), h[j].length = ℓ (j / 2 + 1) x.length) →
      (B (i - 1) x h → ∃ u : List Bool, u.length = ℓ i x.length ∧
        ∀ v : List Bool, v.length = ℓ i x.length → B i x (h ++ [u, v])) ∧
      (¬ B (i - 1) x h → ∃ v : List Bool, v.length = ℓ i x.length ∧
        ∀ u : List Bool, u.length = ℓ i x.length → ¬ B i x (h ++ [u, v]))) ∧
    (∀ n, ∑ i ∈ Finset.Icc 1 k, ℓ i n ≤ C * t n + C) ∧
    (∀ i, 1 ≤ i → i ≤ k → ∃ Mℓ : OracleTM, ∀ n,
      Mℓ.HaltsWithin ∅ (C * t n + C) (tupleEnc [unary n]) ∧
        outAt Mℓ ∅ (C * t n + C) (tupleEnc [unary n]) = Nat.bits (ℓ i n)) ∧
    (∀ (x : List Bool) (h : List (List Bool)), h.length = 2 * k →
      (∀ (j : ℕ) (hj : j < h.length), h[j].length = ℓ (j / 2 + 1) x.length) →
      Mk.HaltsWithin O (C * t x.length + C) (tupleEnc (x :: h)) ∧
        (B k x h ↔ acceptsAt Mk O (C * t x.length + C) (tupleEnc (x :: h))))

end AvgPHETH


