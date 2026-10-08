-- Prove2me | Definitions.Def_AMPUniversality_Universal_Regular
-- name    : AMPUniversality_Universal_Regular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:07.177462+00:00
-- url     : https://prove2.me/theorems/ebc3aea7-38ed-4e94-877b-3f6ff381f38e
-- title:
--   Definition 4, p. 7 — (C, d)-regular polynomial sequences of random AMP instances
-- statement:
--   Let $(\Omega, \mathbb P)$ be a probability space. For every $N$, let $A(N)$ be a random $N\times N$ matrix, let $c(N)$ be the (possibly random) coefficients of the polynomial maps $f^i(\cdot\,;t) : \mathbb R^q \to \mathbb R^q$, $i \in [N]$, $t \ge 0$, of degree at most $d$, and let $x^{0,N} = (x^{0,N}_1,\dots,x^{0,N}_N)$ be a random initial condition with $x^{0,N}_i \in \mathbb R^q$. The sequence $\{(A(N), \mathcal F_N, x^{0,N})\}_{N}$ is **$(C,d)$-regular polynomial** if $C > 0$ and, for every $N$:
--
--   1. $A(N)$ is symmetric with $A_{ii}(N) = 0$ (so it is an AMP instance, Definition 2);
--   2. the entries $(A_{ij}(N))_{1 \le i < j \le N}$ are independent and centered, and each is sub-Gaussian with scale factor $C/N$:
--   $$
--   \mathbb E\, e^{\lambda A_{ij}(N)} \;\le\; e^{C\lambda^2/(2N)} \qquad \text{for all } \lambda \in \mathbb R;
--   $$
--   3. every coefficient of every $f^i(\cdot\,;t)$ is bounded by $C$ in absolute value;
--   4. $A(N)$, the coefficients $c(N)$ and $x^{0,N}$ are mutually independent;
--   5. almost surely, $\displaystyle\sum_{i=1}^N \exp\big(\|x^{0,N}_i\|_2^2 / C\big) \le N C$;
--   6. all these random objects are measurable.
--
--   This is the class of random instances for which Theorem 3 asserts universality: the asymptotic moments of the AMP iterates do not depend on the law of the matrix entries beyond their variances.
--
--   **Formalization Note** Three readings of the printed Definition 4 are disclosed. (i) The page defines sub-Gaussianity by $\mathbb E e^{\lambda X} \le e^{\sigma^2\lambda^2/2}$ "for all $\lambda > 0$"; this is taken for all real $\lambda$ (Mathlib's `HasSubgaussianMGF`), since the proof's absolute-moment bound (4.15) needs both tails. (ii) The bracket of Definition 4(1) writes $\log \mathbb E e^{\lambda A_{ij}} \le (C\lambda)^2/(2N^2)$, which contradicts "scale factor $C/N$" and would exclude every ensemble with variance $1/N$ once $N > C^2$; the scale factor $C/N$ used in the proof (p. 20) is formalized. (iii) The initial-condition bound of Definition 4(3) is printed "with probability converging to one"; it is required almost surely for every $N$, as the proof (p. 21) uses it deterministically and the expectations compared in Theorem 3 need not be finite otherwise. The squared Euclidean norm is written as $\sum_s x(s)^2$. Since Mathlib puts no measurable structure on `Matrix`, measurability and independence of $A(N)$ are stated for its entry array `fun i j => A N ω i j`.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 7, (1.7) and Definition 4; p. 6, Definition 2(1); p. 20 (scale factor C/N in the proof of Proposition 1)

import Mathlib

namespace AMPUniversality.Universal

open MeasureTheory ProbabilityTheory Finset

/-- A sequence `{(A(N), F_N, x^{0,N})}_{N≥1}` of random AMP instances on one probability space
`(Ω, P)` is **`(C, d)`-regular polynomial** (Definition 4, p. 7). The data are
`A N ω : Matrix (Fin N) (Fin N) ℝ`, the coefficient process `c N ω i t r m` of the polynomials
`f^i_r(·; t)` in coefficient form (4.10), and the initial condition `x0 N ω i ∈ ℝ^q`.

* `A(N)` is symmetric with zero diagonal (Definition 2(1));
* its entries `(A_ij)_{i<j}` are independent, centered, sub-Gaussian with scale factor `C/N`,
  i.e. `E e^{λ A_ij} ≤ e^{(C/N) λ² / 2}` for every real `λ` (Definition 4(1), read as in the proof, p. 20);
* every coefficient is bounded by `C` in absolute value (Definition 4(2); degree `≤ d` is built
  into the coefficient form);
* `A(N)`, the (possibly random) coefficients and `x^{0,N}` are mutually independent
  (Definition 4(2)–(3));
* `∑_i exp(‖x^{0,N}_i‖₂² / C) ≤ N C` almost surely, for every `N` (Definition 4(3));
* all random objects are measurable, and `C > 0`. -/
structure IsRegular {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : ℝ) (d q : ℕ)
    (A : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
    (c : (N : ℕ) → Ω → Fin N → ℕ → Fin q → (Fin q → Fin (d + 1)) → ℝ)
    (x0 : (N : ℕ) → Ω → Fin N → Fin q → ℝ) : Prop where
  C_pos : 0 < C
  symm : ∀ N ω, (A N ω).IsSymm
  diag_zero : ∀ N ω (i : Fin N), A N ω i i = 0
  measurable_A : ∀ N, Measurable (fun ω (i j : Fin N) => A N ω i j)
  measurable_c : ∀ N, Measurable (c N)
  measurable_x0 : ∀ N, Measurable (x0 N)
  indep_entries : ∀ N, iIndepFun
    (fun (p : {p : Fin N × Fin N // p.1 < p.2}) ω => A N ω p.1.1 p.1.2) P
  centered : ∀ N (i j : Fin N), i < j → ∫ ω, A N ω i j ∂P = 0
  subgaussian : ∀ N (i j : Fin N), i < j →
    HasSubgaussianMGF (fun ω => A N ω i j) (Real.toNNReal (C / N)) P
  coeff_bound : ∀ N ω (i : Fin N) (t : ℕ) (r : Fin q) (m : Fin q → Fin (d + 1)),
    |c N ω i t r m| ≤ C
  indep_A : ∀ N, IndepFun (fun ω (i j : Fin N) => A N ω i j) (fun ω => (c N ω, x0 N ω)) P
  indep_c_x0 : ∀ N, IndepFun (c N) (x0 N) P
  init_bound : ∀ N, ∀ᵐ ω ∂P, ∑ i, Real.exp ((∑ s, x0 N ω i s ^ 2) / C) ≤ N * C

end AMPUniversality.Universal


