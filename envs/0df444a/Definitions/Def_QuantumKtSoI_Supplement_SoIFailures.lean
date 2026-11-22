-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_SoIFailures
-- name    : QuantumKtSoI_Supplement_SoIFailures
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:33:18.010084+00:00
-- url     : https://prove2.me/theorems/e80d9cec-5911-4ecb-915d-627a9abf76a2
-- title:
--   The symmetry-failure statements of §5 for a conditional measure $\mu$
-- statement:
--   For a real-valued conditional measure $\mu(y|x)$ with $\mu(y)=\mu(y|\epsilon)$, this module states, with $\mu$ in place of $\mathrm{qKt}$:
--
--   1. **Theorem 5.10**: for every real $a\ge1$, infinitely many pairs satisfy $\mu(y|x)-\mu(\langle x,y\rangle)+\mu(x)>2^{(\log\log(|x|+|y|+4))^a}$, and symmetry fails with every fixed polylogarithmic error;
--   2. **Corollary 5.13**: for every real $a\ge1$, infinitely many $n$ admit $x,y\in\{0,1\}^n$ with $\mu(y|x)-\mu(\langle x,y\rangle)+\mu(x)>2^{(\log\log(2n+4))^a}$;
--   3. **Corollary 5.15(ii),(iii)**: the same two statements with the error $F^{[j]}_a(|x|+|y|)$, respectively $F^{[j]}_a(2n)$, for all integers $j,a\ge1$;
--   4. **Theorem 5.16**: for every $C\ge1$ there are a positive integer $\beta$ and a quantum polynomial-time sampler $S$ such that for infinitely many $n$, with probability greater than $1/(8000n^2)$, $S(1^n)$ outputs a pair of $n$-bit strings with $\mu(y|x)>\mu(\langle x,y\rangle)-\mu(x)+C\log(|x|+|y|+2)$, and every output of $S(1^n)$ is $\langle0^n,0^n\rangle$ or $\langle\mathrm{pad}_n(P),\mathrm{pad}_n(b)\rangle$ with $|P|,|b|<n$ and $|b|\le\beta\lceil\log(n+2)\rceil$;
--   5. **Theorem 5.22**: for every $\kappa\ge0$ there is $\eta>0$ such that infinitely many triples satisfy $\mu(y|wx)>\mu(xy|w)-\mu(x|w)+\eta(|x|+|y|)+\kappa\log(|w|+|x|+|y|+2)$;
--   6. **Corollary 5.24**: for every $\kappa\ge0$ there is $\eta>0$ such that for infinitely many $n$ there are $x,y\in\{0,1\}^n$ and $w$ with $\mu(x|\langle y,w\rangle)>\mu(\langle x,y\rangle|w)-\mu(y|w)+\eta n+\kappa\log(|w|+2n+2)$.
--
--   The transfer theorems D.38, F.3 and F.9 assert these with $\mathrm{qKt}_U$ or $\mathrm{qKt}^{(c)}$ in place of $\mathrm{qKt}$; at $\mu=\mathrm{qKt}$ each is the paper's statement.
--
--   **Formalization Note** In Theorem 5.22, $wx$ and $xy$ are concatenations; in Corollary 5.24, $\langle y,w\rangle$ and $\langle x,y\rangle$ are pairs. "Every output" is every $w$ of positive probability.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 5.10, p.59; Corollary 5.13, p.61; Corollary 5.15, p.63; Theorem 5.16, p.65; Theorem 5.22, p.71; Corollary 5.24, p.74

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_Supplement_iterH
import Definitions.Def_QuantumKtSoI_Supplement_QSampler

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-! Statements of §5 for a conditional measure `µ`, where `µ y x` is `µ(y | x)` and `µ(y) = µ(y | ε)`
(Myrisiotis, STOC 2027 submission, held version sha256 6616571c…). With `µ = qKt` each is the
paper's statement; Theorems D.38 and F.9 assert them "with `qKt_U` in place of `qKt`". -/

/-- **Theorem 5.10** for `µ` (p.59): for every real `a ≥ 1`, infinitely many pairs `(x, y)` satisfy
`µ(y|x) − µ(⟨x,y⟩) + µ(x) > 2^{(log log(|x|+|y|+4))^a}`; in particular symmetry fails with every
fixed polylogarithmic error: for all reals `C, k`, some pair has
`µ(y|x) − µ(⟨x,y⟩) + µ(x) > C (log(|x|+|y|+2))^k`. -/
def Thm510For (μ : List Bool → List Bool → ℝ) : Prop :=
  (∀ a : ℝ, 1 ≤ a →
    {p : List Bool × List Bool |
      (2 : ℝ) ^ (Real.logb 2 (Real.logb 2 ((p.1.length : ℝ) + p.2.length + 4))) ^ a <
        μ p.2 p.1 - μ (pair p.1 p.2) [] + μ p.1 []}.Infinite) ∧
  ∀ C k : ℝ, ∃ x y : List Bool,
    C * Real.logb 2 ((x.length : ℝ) + y.length + 2) ^ k < μ y x - μ (pair x y) [] + μ x []

/-- **Corollary 5.13** for `µ` (p.61): for every real `a ≥ 1`, infinitely many integers `n` admit
`x, y ∈ {0,1}ⁿ` with `µ(y|x) − µ(⟨x,y⟩) + µ(x) > 2^{(log log(2n+4))^a}`. -/
def Cor513For (μ : List Bool → List Bool → ℝ) : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∀ N : ℕ, ∃ n ≥ N, ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
    (2 : ℝ) ^ (Real.logb 2 (Real.logb 2 (2 * (n : ℝ) + 4))) ^ a < μ y x - μ (pair x y) [] + μ x []

/-- **Corollary 5.15(ii)** for `µ` (p.63): for integers `j, a ≥ 1`, infinitely many pairs `(x, y)`
satisfy `µ(y|x) − µ(⟨x,y⟩) + µ(x) > F^{[j]}_a(|x| + |y|)`. -/
def Cor515iiFor (μ : List Bool → List Bool → ℝ) : Prop :=
  ∀ j a : ℕ, 1 ≤ j → 1 ≤ a →
    {p : List Bool × List Bool |
      (iterF j a (p.1.length + p.2.length) : ℝ) < μ p.2 p.1 - μ (pair p.1 p.2) [] + μ p.1 []}.Infinite

/-- **Corollary 5.15(iii)** for `µ` (p.63): for integers `j, a ≥ 1`, infinitely many integers `n`
admit `x, y ∈ {0,1}ⁿ` with `µ(y|x) − µ(⟨x,y⟩) + µ(x) > F^{[j]}_a(2n)`. -/
def Cor515iiiFor (μ : List Bool → List Bool → ℝ) : Prop :=
  ∀ j a : ℕ, 1 ≤ j → 1 ≤ a → ∀ N : ℕ, ∃ n ≥ N, ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
    (iterF j a (2 * n) : ℝ) < μ y x - μ (pair x y) [] + μ x []

/-- **Theorem 5.16** for `µ` (p.65): for every constant `C ≥ 1` there are a positive integer `β` and
a quantum polynomial-time sampler `S` such that, for infinitely many `n`, with probability greater
than `1/(8000n²)` the output of `S(1ⁿ)` is a pair `⟨x, y⟩` of strings of length `n` with
`µ(y|x) > µ(⟨x,y⟩) − µ(x) + C log(|x|+|y|+2)`, and every output of `S(1ⁿ)` is `⟨0ⁿ, 0ⁿ⟩` or
`⟨pad_n(P), pad_n(b)⟩` for strings `P, b` with `|P|, |b| < n` and `|b| ≤ β⌈log(n+2)⌉`. -/
def Thm516For (μ : List Bool → List Bool → ℝ) : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ β : ℕ, 0 < β ∧ ∃ S : QSampler,
    (∀ N : ℕ, ∃ n ≥ N, 1 / (8000 * (n : ℝ) ^ 2) <
      S.pairProb n fun x y =>
        μ (pair x y) [] - μ x [] + C * Real.logb 2 ((x.length : ℝ) + y.length + 2) < μ y x) ∧
    ∀ n : ℕ, ∀ w : List Bool, 0 < S.outProb n w →
      w = pair (List.replicate n false) (List.replicate n false) ∨
        ∃ P b : List Bool, P.length < n ∧ b.length < n ∧ b.length ≤ β * Nat.clog 2 (n + 2) ∧
          w = pair (pad n P) (pad n b)

/-- **Theorem 5.22** for `µ` (p.71): for every `κ ≥ 0` there is `η > 0` such that infinitely many
triples `(w, x, y)` satisfy
`µ(y|wx) > µ(xy|w) − µ(x|w) + η(|x|+|y|) + κ log(|w|+|x|+|y|+2)`, where `wx`, `xy` are
concatenations. -/
def Thm522For (μ : List Bool → List Bool → ℝ) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ η : ℝ, 0 < η ∧
    {t : List Bool × List Bool × List Bool |
      μ (t.2.1 ++ t.2.2) t.1 - μ t.2.1 t.1 + η * ((t.2.1.length : ℝ) + t.2.2.length) +
          κ * Real.logb 2 ((t.1.length : ℝ) + t.2.1.length + t.2.2.length + 2) <
        μ t.2.2 (t.1 ++ t.2.1)}.Infinite

/-- **Corollary 5.24** for `µ` (p.74): for every `κ ≥ 0` there is `η > 0` such that, for infinitely
many integers `n`, there are `x, y ∈ {0,1}ⁿ` and `w ∈ {0,1}*` with
`µ(x|⟨y,w⟩) > µ(⟨x,y⟩|w) − µ(y|w) + ηn + κ log(|w|+2n+2)`. -/
def Cor524For (μ : List Bool → List Bool → ℝ) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ η : ℝ, 0 < η ∧ ∀ N : ℕ, ∃ n ≥ N, ∃ x y w : List Bool,
    x.length = n ∧ y.length = n ∧
      μ (pair x y) w - μ y w + η * n + κ * Real.logb 2 ((w.length : ℝ) + 2 * n + 2) < μ x (pair y w)

/-- The conclusion of **Theorem D.38** (p.184) for a measure `µ`: Theorems 5.10, 5.16 and 5.22,
Corollaries 5.13 and 5.24, and parts (ii) and (iii) of Corollary 5.15 hold with `µ` in place of
`qKt`, with the same scales and the same polynomial `p(n) = 8000n²`. -/
def SoIFailures (μ : List Bool → List Bool → ℝ) : Prop :=
  Thm510For μ ∧ Cor513For μ ∧ Cor515iiFor μ ∧ Cor515iiiFor μ ∧ Thm516For μ ∧ Thm522For μ ∧ Cor524For μ

end QuantumKtSoI.Supplement


