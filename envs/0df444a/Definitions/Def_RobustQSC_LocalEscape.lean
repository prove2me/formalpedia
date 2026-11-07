-- Prove2me | Definitions.Def_RobustQSC_LocalEscape
-- name    : RobustQSC_LocalEscape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:50:12.886082+00:00
-- url     : https://prove2.me/theorems/9b7e1578-cf87-4a44-a06a-7720b9633295
-- title:
--   The good set $A(T)$ and the local escape property
-- statement:
--   For $T>0$ and a measure $\mu$ with $N=2^n$, the good set is
--
--   $$
--   A(T)=\Bigl\{x:\mu(x)\in\Bigl[\frac1{TN},\frac TN\Bigr]\Bigr\},
--   $$
--
--   and $B(T)$ is its complement. A set $A\subseteq\{0,1\}^n$ has the **local escape property** with parameter $\alpha$ if
--
--   1. each $x\in\{0,1\}^n$ has at least $\alpha n$ neighbours in $A$;
--   2. for all $x,y$ with $d(x,y)\le3$, at least $\alpha n$ of the canonical paths $P_i(x,y)$ have all their internal vertices in $A$.
--
--   This geometric property makes interior influence on $A$ control the influence of an extension to the whole cube.
--
--   **Formalization Note** Counts are compared with $\alpha n$ as real numbers; $d$ is the Hamming distance. The paper uses "local escape" without a separate name for $\alpha$; the two bullets are those of Proposition 13.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §6, p.47; Proposition 13, p.49; Theorem 9, p.55

import Definitions.Def_RobustQSC_canonPath

namespace RobustQSC

open QAlgorithms

/-- The good set `A = A(T) = {x : μ(x) ∈ [1/(TN), T/N]}`, `N = 2ⁿ`; its complement is the bad set
`B = B(T)`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), §6, p.47 ("A = {x : µ(x) ∈ [1/(TN),
T/N]} and B = A^c"), Theorem 9, p.55 ("B = B(T) = {x : µ_f(x) ∉ [1/TN, T/N]}"). -/
def goodSet {n : ℕ} (T : ℝ) (μ : Qubits n → ℝ) : Set (Qubits n) :=
  {x | 1 / (T * 2 ^ n) ≤ μ x ∧ μ x ≤ T / 2 ^ n}

/-- The local escape property of `A ⊆ {0,1}ⁿ` with parameter `α`:

1. each `x ∈ {0,1}ⁿ` has at least `αn` neighbours in `A`;
2. for all `x, y` with `d(x, y) ≤ 3`, at least `αn` of the canonical paths `P_i(x, y)`,
   `i ∈ [n]`, have all their internal vertices in `A`.

Source: Coladangelo, Li, Slote, arXiv:2607.27184 (sha256 09d2692e…), Proposition 13, p.49 (the
two bullets), Proposition 14, p.50 ("so that local escape holds").

**Formalization Note.** Counts are `Set.ncard` of sets of coordinates `i`, compared with `αn` as
real numbers; `d` is the Hamming distance. -/
def LocalEscape {n : ℕ} (A : Set (Qubits n)) (α : ℝ) : Prop :=
  (∀ x : Qubits n, α * n ≤ ({i : Fin n | flip x i ∈ A}.ncard : ℝ)) ∧
    ∀ x y : Qubits n, hammingDist x y ≤ 3 →
      α * n ≤ ({i : Fin n | ∀ v ∈ canonPathInternal i x y, v ∈ A}.ncard : ℝ)

end RobustQSC


