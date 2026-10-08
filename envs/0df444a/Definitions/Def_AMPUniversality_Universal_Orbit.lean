-- Prove2me | Definitions.Def_AMPUniversality_Universal_Orbit
-- name    : AMPUniversality_Universal_Orbit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:04.996979+00:00
-- url     : https://prove2.me/theorems/d8e3994b-3b3b-4fc2-916a-28749b0d1e53
-- title:
--   Definitions 2–3, (1.4)–(1.6), (4.5)–(4.6) — the AMP orbit xᵗ⁺¹ = Af(xᵗ;t) − B_t f(xᵗ⁻¹;t−1) and the message-passing iteration z
-- statement:
--   Let $A \in \mathbb R^{N \times N}$ be a matrix and, for each $j \in [N]$ and $t \ge 0$, let $f^j(\cdot\,; t) : \mathbb R^q \to \mathbb R^q$ be a polynomial map (given by its coefficients, see the definition `Poly`). Let $x^0 = (x^0_1, \dots, x^0_N)$ with $x^0_i \in \mathbb R^q$ be an initial condition.
--
--   **The AMP orbit** (Definition 3, display (1.6)) is the sequence $x^t = (x^t_1, \dots, x^t_N)$, $x^t_i \in \mathbb R^q$, defined for $t \ge 0$ by
--
--   $$
--   x^{t+1}_i \;=\; \sum_{j\in[N]} A_{ij}\, f^j(x^t_j; t) \;-\; \sum_{j \in [N]} A_{ij}^2\, \frac{\partial f^j}{\partial x}(x^t_j; t)\, f^i(x^{t-1}_i; t-1),
--   $$
--
--   where $\frac{\partial f^j}{\partial x}$ is the $q\times q$ Jacobian matrix, applied to the vector $f^i(x^{t-1}_i; t-1)$. The second sum (the memory, or Onsager, term) is absent at $t = 0$. The matrix entries enter the memory term as $A_{ij}^2$ itself, not through its expectation.
--
--   **The message-passing iteration** (displays (4.5)–(4.6)) consists of messages $z^t_{i\to j} \in \mathbb R^q$ for $i, j \in [N]$ and vectors $z^t_i \in \mathbb R^q$: $z^0_{i \to j} = x^0_i$, and for $t \ge 0$ and $r \in [q]$
--
--   $$
--   z^{t+1}_{i\to j}(r) \;=\; \sum_{\ell \in [N]\setminus \{j\}} A_{\ell i}\, f^\ell_r(z^t_{\ell\to i}; t), \qquad
--   z^{t+1}_{i}(r) \;=\; \sum_{\ell \in [N]} A_{\ell i}\, f^\ell_r(z^t_{\ell\to i}; t).
--   $$
--
--   The AMP orbit is the algorithm whose universality Theorem 3 asserts; the message-passing iteration is the auxiliary non-backtracking recursion through which the proof compares two matrix ensembles (Propositions 1 and 3).
--
--   **Formalization Note** Indices are 0-based (`Fin N`, `Fin q`); $f^j(\cdot\,;t)$ is `polyEval (c j t)` and its Jacobian is `polyJac (c j t)`. The orbit is computed by recursion on the pair $(x^t, x^{t-1})$; at $t = 0$ the second component is a placeholder equal to $x^0$, which the step never reads because the memory term is switched off there. The messages are computed for all pairs, including the diagonal $i = j$, which the paper never uses (it enters the sums only through $A_{ii}$, which is $0$ for an AMP instance). The paper defines $z^t_i$ for $t \ge 1$ only; the formalization sets $z^0_i := x^0_i$, which no statement uses.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, pp. 6–7, Definitions 2–3, (1.4)–(1.6); p. 2 (convention b₀ = 0); pp. 15–16, (4.5)–(4.6)

import Mathlib
import Definitions.Def_AMPUniversality_Universal_Poly

namespace AMPUniversality.Universal

open Finset

/-- One step of the AMP recursion (1.6). Given the matrix `A`, the coefficient family
`c j t` of the polynomials `f^j(·; t)`, the current iterate `xt = x^t` and the previous
iterate `xprev = x^{t-1}`, it returns `x^{t+1}` with coordinates
`x^{t+1}_i(r) = ∑_j A_ij f^j_r(x^t_j; t) − ∑_j A_ij² ∑_s (∂f^j_r/∂x(s))(x^t_j; t) f^i_s(x^{t-1}_i; t-1)`.
The memory (Onsager) term is absent at `t = 0` (the convention `b_0 = 0`). -/
def ampStep {N q d : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (c : Fin N → ℕ → Fin q → (Fin q → Fin (d + 1)) → ℝ) (t : ℕ)
    (xt xprev : Fin N → Fin q → ℝ) : Fin N → Fin q → ℝ :=
  fun i r =>
    (∑ j, A i j * polyEval (c j t) (xt j) r) -
      (if t = 0 then 0 else
        ∑ j, A i j ^ 2 * ∑ s, polyJac (c j t) (xt j) r s * polyEval (c i (t - 1)) (xprev i) s)

/-- The pair `(x^t, x^{t-1})` of the AMP orbit; at `t = 0` the second component is a
placeholder (equal to `x^0`) that `ampStep` never reads. -/
def ampPair {N q d : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (c : Fin N → ℕ → Fin q → (Fin q → Fin (d + 1)) → ℝ) (x0 : Fin N → Fin q → ℝ) :
    ℕ → (Fin N → Fin q → ℝ) × (Fin N → Fin q → ℝ)
  | 0 => (x0, x0)
  | t + 1 => (ampStep A c t (ampPair A c x0 t).1 (ampPair A c x0 t).2, (ampPair A c x0 t).1)

/-- The approximate message passing orbit `{x^t}_{t≥0}` of the instance `(A, F, x^0)`
(Definition 3, (1.4)–(1.6)), with `f^j(·; t) = polyEval (c j t)`. -/
def ampOrbit {N q d : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (c : Fin N → ℕ → Fin q → (Fin q → Fin (d + 1)) → ℝ) (x0 : Fin N → Fin q → ℝ) (t : ℕ) :
    Fin N → Fin q → ℝ :=
  (ampPair A c x0 t).1

/-- The message-passing iteration (4.5): `mpMessages A c x0 t i j = z^t_{i→j} ∈ ℝ^q`, with
`z^0_{i→j} = x^0_i` and `z^{t+1}_{i→j}(r) = ∑_{ℓ ∈ [N] \ j} A_ℓi f^ℓ_r(z^t_{ℓ→i}; t)`.
The recursion is evaluated for all pairs, including the diagonal `i = j`, which the paper
never uses. -/
def mpMessages {N q d : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (c : Fin N → ℕ → Fin q → (Fin q → Fin (d + 1)) → ℝ) (x0 : Fin N → Fin q → ℝ) :
    ℕ → Fin N → Fin N → Fin q → ℝ
  | 0 => fun i _ => x0 i
  | t + 1 => fun i j r =>
      ∑ ℓ ∈ univ.erase j, A ℓ i * polyEval (c ℓ t) (mpMessages A c x0 t ℓ i) r

/-- The vectors `z^t_i ∈ ℝ^q` of (4.6): `z^{t+1}_i(r) = ∑_{ℓ ∈ [N]} A_ℓi f^ℓ_r(z^t_{ℓ→i}; t)`.
The paper defines `z^t_i` only for `t ≥ 1`; here `z^0_i := x^0_i`. -/
def mpOrbit {N q d : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (c : Fin N → ℕ → Fin q → (Fin q → Fin (d + 1)) → ℝ) (x0 : Fin N → Fin q → ℝ) :
    ℕ → Fin N → Fin q → ℝ
  | 0 => x0
  | t + 1 => fun i r => ∑ ℓ, A ℓ i * polyEval (c ℓ t) (mpMessages A c x0 t ℓ i) r

end AMPUniversality.Universal


