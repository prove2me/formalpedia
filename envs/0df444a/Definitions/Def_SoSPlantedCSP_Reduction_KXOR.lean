-- Prove2me | Definitions.Def_SoSPlantedCSP_Reduction_KXOR
-- name    : SoSPlantedCSP_Reduction_KXOR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:37:17.162198+00:00
-- url     : https://prove2.me/theorems/1adb04fe-2d9c-4eab-8ffb-54cea497add4
-- title:
--   k-XOR instances, $\mathrm{Bias}(\varepsilon)$ and $\mathrm{XOR}(\mathcal H,x^*,\varepsilon)$
-- statement:
--   Signs are the elements of $\{-1,1\}$ and an assignment is $x\in\{-1,1\}^n$. For a set $C\subseteq[n]$ write $x_C=\prod_{i\in C}x_i$.
--
--   1. **Biased bit (Definition 2.1).** $\mathrm{Bias}(\varepsilon)$ is the law on $\{-1,1\}$ that equals $1$ with probability $(1+\varepsilon)/2$ and $-1$ otherwise; its mass function is $s\mapsto(1+s\varepsilon)/2$, a probability mass function for $-1\le\varepsilon\le1$. The mass function of $t$ independent samples of a law $q$ is $y\mapsto\prod_{i=1}^t q(y_i)$.
--   2. **k-XOR instance (Definition 1.1).** An instance with $n$ variables and $m$ constraints is a multiset $\mathcal H$ of $m$ subsets of $[n]$ of size $k$ together with right-hand sides $b_C\in\{-1,1\}$, representing the equations $x_C=b_C$. Its **instance polynomial** is
--   $$\Psi(x)=\frac12+\frac1{2m}\sum_{C\in\mathcal H}b_C\,x_C,$$
--   a real polynomial in $x_1,\dots,x_n$ whose value at $x\in\{-1,1\}^n$ is the fraction of satisfied equations.
--   3. **Semirandom planted noisy k-XOR (Definition 1.2).** For fixed $\mathcal H$, $x^*\in\{-1,1\}^n$ and $\varepsilon$, the law $\mathrm{XOR}(\mathcal H,x^*,\varepsilon)$ samples $r_C\sim\mathrm{Bias}(\varepsilon)$ independently for every $C\in\mathcal H$ and sets $b_C=r_C\,x^*_C$. Its mass function is $b\mapsto\prod_{C}\mathrm{Bias}(\varepsilon)(b_C\,x^*_C)$.
--
--   The probability of an event $E$ under a mass function $\mu$ on a finite set is $\sum_{a\in E}\mu(a)$.
--
--   **Formalization Note** The multiset $\mathcal H$ is an indexed family $H:\mathrm{Fin}\,m\to\mathrm{Finset}(\mathrm{Fin}\,n)$; repeated values are repeated hyperedges, sub-multisets are subsets of positions, and $|H_j|=k$ is a hypothesis of the theorems. Variables are indexed $0,\dots,n-1$. Signs are the units $\mathbb Z^\times$. Laws on finite sets are real-valued mass functions. $\mathrm{Bias}(\varepsilon)$ is defined by the same formula for every real $\varepsilon$ (the paper states $\varepsilon\ge0$); it is used only for $|\varepsilon|\le1$.
-- source:
--   Arpon Basu, Andrew D. Lin, Peter Manohar, STOC 2027 submission #544 (October 2026), Definitions 1.1 and 1.2, p. 3 (PDF p. 5); Definition 2.1, p. 9 (PDF p. 11)

import Mathlib

namespace SoSPlantedCSP.Reduction

/-!
# k-XOR instances, biased bits and semirandom planted noisy k-XOR

Basu–Lin–Manohar, STOC 2027 submission #544 (October 2026): Definition 1.1 (k-XOR instance) and
Definition 1.2 (semirandom planted noisy k-XOR), printed p. 3 (PDF p. 5); Definition 2.1
(biased random bit), printed p. 9 (PDF p. 11).

* Signs `{−1, 1}` are the units `ℤˣ`; an assignment is `x : Fin n → ℤˣ` (the paper's `[n]` is
  `Fin n`, 0-based).
* The multiset `ℋ` of `k`-subsets of `[n]` with `m` elements is an indexed family
  `H : Fin m → Finset (Fin n)` (with `(H j).card = k` stated where it is used); repeated values
  are repeated hyperedges, and sub-multisets of `ℋ` are subsets of `Fin m`.
* Laws on finite sets are mass functions with values in `ℝ`.
-/

/-- The monomial `x_C = ∏_{i ∈ C} x_i` of a sign vector, as a sign. -/
def monoSign {n : ℕ} (x : Fin n → ℤˣ) (C : Finset (Fin n)) : ℤˣ :=
  ∏ i ∈ C, x i

/-- Definition 2.1: the mass function of `Bias(ε)`, the law on `{−1, 1}` equal to `1` with
probability `(1 + ε)/2` and to `−1` otherwise: `s ↦ (1 + s ε)/2`. It is a probability mass
function exactly when `−1 ≤ ε ≤ 1`. -/
noncomputable def biasMass (ε : ℝ) (s : ℤˣ) : ℝ :=
  (1 + ((s : ℤ) : ℝ) * ε) / 2

/-- The mass function of `t` independent samples, each with mass function `q`. -/
noncomputable def iidMass {t : ℕ} (q : ℤˣ → ℝ) (y : Fin t → ℤˣ) : ℝ :=
  ∏ i, q (y i)

/-- Definition 1.2: the mass function of the right-hand sides `b` of `XOR(ℋ, x*, ε)`.
Independently for every position `j`, `r_j ∼ Bias(ε)` and `b_j = r_j · x*_{H j}`; since
`x*_{H j} = ±1`, `b` has mass `∏_j Bias(ε)(b_j · x*_{H j})`. -/
noncomputable def xorMass {n m : ℕ} (H : Fin m → Finset (Fin n)) (xstar : Fin n → ℤˣ) (ε : ℝ)
    (b : Fin m → ℤˣ) : ℝ :=
  ∏ j, biasMass ε (b j * monoSign xstar (H j))

open Classical in
/-- The probability of the event `E` under the mass function `μ` on a finite type. -/
noncomputable def prob {α : Type*} [Fintype α] (μ : α → ℝ) (E : α → Prop) : ℝ :=
  ∑ a, if E a then μ a else 0

/-- Definition 1.1: the instance polynomial
`Ψ(x) = 1/2 + (1/(2m)) ∑_{j} b_j x_{H j}` of the instance `(H, b)`, as a real polynomial in
`x_1, …, x_n`. -/
noncomputable def instancePoly {n m : ℕ} (H : Fin m → Finset (Fin n)) (b : Fin m → ℤˣ) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (1 / 2) +
    MvPolynomial.C (1 / (2 * (m : ℝ))) *
      ∑ j, MvPolynomial.C (((b j : ℤ) : ℝ)) * ∏ i ∈ H j, MvPolynomial.X i

end SoSPlantedCSP.Reduction


