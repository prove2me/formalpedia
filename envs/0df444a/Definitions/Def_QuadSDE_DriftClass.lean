-- Prove2me | Definitions.Def_QuadSDE_DriftClass
-- name    : QuadSDE_DriftClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:16.856387+00:00
-- url     : https://prove2.me/theorems/ec7316b9-f1e4-4489-84df-b200269014a1
-- title:
--   Norm- and volume-preserving quadratic drifts: strength $J$, $r$ channels, sparsity $s$
-- statement:
--   A **quadratic drift** on $\mathbb R^N$ is given by real coefficients $c_{ijk}$, $i,j,k\in[N]$, through
--   $$f_i(x)=\sum_{j,k=1}^N c_{ijk}\,x_jx_k \qquad (5).$$
--   It is **admissible** when
--   1. the coefficients are symmetric, $c_{ijk}=c_{ikj}$;
--   2. it preserves the Euclidean norm, $\sum_{i} x_if_i(x)=0$ for all $x\in\mathbb R^N$ (6);
--   3. it preserves volume, $\sum_i \partial f_i(x)/\partial x_i=0$ for all $x\in\mathbb R^N$ (7).
--
--   Viewing $c$ as an $N\times N^2$ matrix (rows $i$, columns $(j,k)$), the drift has **strength** $J$ if every row has Euclidean norm at most $J$, $\max_i(\sum_{j,k}c_{ijk}^2)^{1/2}\le J$; it has (at most) $r$ **channels** if every column has at most $r$ nonzero entries; and it is $s$-**sparse** if every row has at most $s$ nonzero entries.
--
--   These are the drift functions of APX-SDE: norm preservation makes the ODE globally well posed, and norm plus volume preservation turns the evolution of densities into a linear evolution on Hermite coefficients.
--
--   **Formalization Note** Indices are `Fin N` (0-based). The divergence condition is written with the Fréchet derivative of $x\mapsto f_i(x)$ in the direction $e_i$, i.e. in the derivative form of (7); its coefficient form is Lemma 1. Strength, channels and sparsity are upper bounds (`≤`), as on p. 4.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §1, Eqs. (5)–(7), pp. 3–4

import Mathlib

noncomputable section

namespace QuadSDE

/-- Bravyi, Byrne, Zayats, Zhuk, Zlokapa, *Quantum algorithms for stochastic nonlinear differential
equations*, arXiv:2606.08349 (sha256 29bd9b01…), §1, Eq. (5), p. 3: the coefficient tensor
`c_{ijk}` of a homogeneous quadratic drift on `ℝ^N`.

**Formalization Note.** The paper's index set `[N] = {1, …, N}` is `Fin N` (0-based). -/
abbrev Coeff (N : ℕ) := Fin N → Fin N → Fin N → ℝ

/-- Eq. (5), p. 3: the quadratic drift `f_i(x) = Σ_{j,k} c_{ijk} x_j x_k`. -/
def drift {N : ℕ} (c : Coeff N) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => ∑ j, ∑ k, c i j k * x j * x k

/-- Eqs. (5)–(7), pp. 3–4: the drift is *admissible*: its coefficients are symmetric,
`c_{ijk} = c_{ikj}`; it preserves the norm, `Σ_i x_i f_i(x) = 0` for all `x ∈ ℝ^N` (Eq. (6)); and it
preserves volume, `Σ_i ∂f_i/∂x_i (x) = 0` for all `x ∈ ℝ^N` (Eq. (7)).

**Formalization Note.** The divergence is written with the Fréchet derivative of the polynomial map
`x ↦ f_i(x)` applied to the `i`-th unit vector, i.e. in the derivative form of Eq. (7); its
coefficient form is Lemma 1. -/
def IsAdmissibleDrift {N : ℕ} (c : Coeff N) : Prop :=
  (∀ i j k, c i j k = c i k j) ∧
  (∀ x : Fin N → ℝ, ∑ i, x i * drift c x i = 0) ∧
  (∀ x : Fin N → ℝ, ∑ i, fderiv ℝ (fun y : Fin N → ℝ => drift c y i) x (Pi.single i 1) = 0)

/-- p. 4: the drift has *strength* `J`: every row of the `N × N²` matrix `c` has Euclidean norm at
most `J`, `max_i (Σ_{j,k} c_{ijk}²)^{1/2} ≤ J`. -/
def strengthLE {N : ℕ} (c : Coeff N) (J : ℝ) : Prop :=
  ∀ i, Real.sqrt (∑ j, ∑ k, c i j k ^ 2) ≤ J

/-- p. 4: the drift has (at most) `r` *channels*: for any fixed `j, k` at most `r` coefficients
`c_{ijk}` are nonzero (every column of the `N × N²` matrix `c` has at most `r` nonzeros). -/
def channelsLE {N : ℕ} (c : Coeff N) (r : ℕ) : Prop :=
  ∀ j k, (Finset.univ.filter fun i => c i j k ≠ 0).card ≤ r

/-- p. 4: the drift is `s`-*sparse*: for any fixed `i` at most `s` coefficients `c_{ijk}` are
nonzero (every row of the `N × N²` matrix `c` has at most `s` nonzeros). -/
def sparsityLE {N : ℕ} (c : Coeff N) (s : ℕ) : Prop :=
  ∀ i, (Finset.univ.filter fun jk : Fin N × Fin N => c i jk.1 jk.2 ≠ 0).card ≤ s

end QuadSDE


