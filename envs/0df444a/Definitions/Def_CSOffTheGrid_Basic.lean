-- Prove2me | Definitions.Def_CSOffTheGrid_Basic
-- name    : CSOffTheGrid_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T03:21:48.820716+00:00
-- url     : https://prove2.me/theorems/aa5a9568-7589-43bb-96bd-5d351949c1bb
-- title:
--   Atomic norm, Toeplitz SDPs, Fejér-kernel system matrices and sampling models for compressed sensing off the grid
-- statement:
--   Objects of Sections 1, 2 and 4 of Tang, Bhaskar, Shah and Recht, *Compressed Sensing Off the Grid* (2013).
--
--   1. **Index sets and atoms.** $J$ is either $\{0,\dots,n-1\}$ or $\{-2M,\dots,2M\}$. For a frequency $f\in[0,1]$ (with $0$ and $1$ identified) and a phase $\phi\in[0,2\pi)$, the atom $a(f,\phi)\in\mathbb C^{|J|}$ has entries $[a(f,\phi)]_j=e^{i(2\pi fj+\phi)}$. The signal with frequencies $f_1,\dots,f_s$ and coefficients $c_1,\dots,c_s$ is $x^\star=\sum_k c_k\,a(f_k,0)$, and $\operatorname{sign}(c)=c/|c|$.
--   2. **Separation.** $|f-f'|$ is the wrap-around distance on the circle (the distance from $f-f'$ to the nearest integer), and $\Delta_f=\min_{k\ne j}|f_k-f_j|$.
--   3. **Atomic norm (Section 2).** $\|x\|_{\mathcal A}=\inf\{\sum_k c_k: x=\sum_k c_k a(f_k,\phi_k),\ c_k\ge0\}$ over finite decompositions, and $\|x\|_{\mathcal A,0}$ is the least number of atoms in such a decomposition.
--   4. **Toeplitz semidefinite programs.** $\operatorname{Toep}(u)$ is the Hermitian Toeplitz matrix with first column $u$. The SDP value is $\inf\{\frac1{2|J|}\operatorname{trace}\operatorname{Toep}(u)+\frac t2: \left[\begin{smallmatrix}\operatorname{Toep}(u)&x\\x^*&t\end{smallmatrix}\right]\succeq0\}$, and the rank value is the minimum of $\operatorname{rank}\operatorname{Toep}(u)$ under the same constraint.
--   5. **Recovery and duality.** $x^\star$ is the unique optimizer of $\min\|x\|_{\mathcal A}$ subject to $x_j=x^\star_j$, $j\in T$, if every other feasible $x$ has strictly larger atomic norm. The dual polynomial of $q\in\mathbb C^{|J|}$ is $Q(f)=\sum_{j\in J}q_je^{-i2\pi jf}$. A dual certificate satisfies $Q(f_k)=\operatorname{sign}(c_k)$, $|Q(f)|<1$ for $f\notin\{f_k\}$, and $q_j=0$ for $j\notin T$. The dual SDP (2.13)–(2.15) has feasible pairs $(q,H)$ with $\left[\begin{smallmatrix}H&-q\\-q^*&1\end{smallmatrix}\right]\succeq0$, the diagonal sums of $H$ equal to $1$ (main diagonal) and $0$ (other diagonals), $H$ Hermitian and $q_{T^c}=0$. Its objective is $\operatorname{Re}\langle q_T,x_T\rangle$, and $\mathcal D$ is its set of optimal solutions.
--   6. **Kernels (Section 4).** $g_M(j)=\frac1M\sum_{k=\max(j-M,-M)}^{\min(j+M,M)}(1-|k/M|)(1-|j/M-k/M|)$. The squared Fejér kernel is $\bar K_M(f)=\frac1M\sum_{j=-2M}^{2M}g_M(j)e^{-i2\pi fj}$, and its derivatives are $\bar K_M^{(\ell)}(f)=\frac1M\sum_j(-i2\pi j)^\ell g_M(j)e^{-i2\pi fj}$. The random kernel $K_M$ keeps only the terms with $j\in T$.
--   7. **System matrices.** With $[D_\ell]_{jk}=K^{(\ell)}(f_j-f_k)$ and $\kappa=|\bar K_M''(0)|$, the system matrix is $\left[\begin{smallmatrix}D_0&D_1/\sqrt\kappa\\-D_1/\sqrt\kappa&-D_2/\kappa\end{smallmatrix}\right]$. It is $\bar D$ for $\bar K_M$ and $D$ for $K_M$. $\bar L$ and $L$ are the first $s$ columns of $\bar D^{-1}$ and $D^{-1}$, and $\|\cdot\|$ is the operator norm.
--   8. **Probability models.** In the Bernoulli model the indicators $\delta_j$, $j\in J$, are i.i.d. with $P(\delta_j=1)=p$, and $T=\{j:\delta_j=1\}$. In the uniform model $T$ is a uniformly random $m$-subset of $J$. The signs $u_k=\operatorname{sign}(c_k)$ are i.i.d., independent of $T$, with either the uniform law on the unit circle or a symmetric law (invariant under $u\mapsto-u$) carried by the unit circle.
--
--   **Formalization Note** Vectors in $\mathbb C^{|J|}$ are functions on $J$. $\operatorname{Toep}(u)$ takes $u$ as the list of its sub-diagonal entries, $u_d=\operatorname{Toep}(u)_{j+d,j}$. The derivatives $\bar K_M^{(\ell)}$ are defined by the termwise-differentiated expansion (4.2), and $|\bar K_M''(0)|$ is the modulus of $\bar K_M''(0)$. Probabilities are explicit finite averages over $T$ combined with the product law of the signs. A failure probability is the measure of the failure event, which for a non-measurable set is its outer measure, so a bound on it is never weaker than the paper's.
-- source:
--   Tang, Bhaskar, Shah and Recht, Compressed Sensing Off the Grid, arXiv:1207.6053v3 (2013), Section 1 (eq. 1.1), Section 2 (eqs. 2.1-2.19), Sections 4.1-4.4 (eqs. 4.2, 4.6, 4.24-4.26)

import Mathlib

/-!
Tang, Bhaskar, Shah and Recht, *Compressed Sensing Off the Grid*, arXiv:1207.6053v3 (2013):
the signal model of Section 1 (eq. (1.1)), the atomic norm and its semidefinite characterization
of Section 2 (eqs. (2.1)-(2.19)), the squared Fejér kernel, its random analogue and the
interpolation system matrices of Section 4 (eqs. (4.2), (4.6), (4.24)-(4.26)), and the uniform,
Bernoulli and random-sign observation models of Theorems 1.1 and 2.3 and Section 4.2.
-/

open MeasureTheory

open scoped ENNReal ComplexOrder

noncomputable section

namespace CSOffTheGrid

/-- Theorem 1.1, p. 2: the wrap-around distance `|a - b|` on the unit circle `[0,1]` with `0` and
`1` identified, i.e. the distance from `a - b` to the nearest integer. -/
def wrapDist (a b : ℝ) : ℝ := |(a - b) - round (a - b)|

/-- Theorem 1.1, p. 2: the frequencies `f₁, …, f_s` satisfy `Δ_f = min_{k ≠ j} |f_k - f_j| ≥ sep`
(wrap-around distance); for `s ≤ 1` the minimum is over the empty set and the condition holds. -/
def IsSeparated {s : ℕ} (f : Fin s → ℝ) (sep : ℝ) : Prop :=
  ∀ k j, k ≠ j → sep ≤ wrapDist (f k) (f j)

/-- Section 2, p. 4: the symmetric index set `J = {-2M, …, 2M}`. -/
def symJ (M : ℕ) : Finset ℤ := Finset.Icc (-(2 * (M : ℤ))) (2 * (M : ℤ))

/-- Section 2, p. 4: the index set `J = {0, …, n-1}`. -/
def stdJ (n : ℕ) : Finset ℤ := Finset.Ico 0 (n : ℤ)

/-- Section 2, p. 4: the atom `a(f, φ) ∈ ℂ^{|J|}`, `[a(f, φ)]_j = e^{i(2π f j + φ)}`, `j ∈ J`. -/
def atom (J : Finset ℤ) (f φ : ℝ) : J → ℂ :=
  fun j => Complex.exp (Complex.I * ((2 * Real.pi * f * ((j : ℤ) : ℝ) + φ : ℝ) : ℂ))

/-- Eqs. (1.1) and (2.1): the signal `x⋆_j = ∑_k c_k e^{i 2π f_k j}`, `j ∈ J`. -/
def signal (J : Finset ℤ) {s : ℕ} (f : Fin s → ℝ) (c : Fin s → ℂ) : J → ℂ :=
  ∑ k, c k • atom J (f k) 0

/-- Theorem 1.1, p. 2: the complex sign `sign(c) = c / |c|`. -/
def csign (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

/-- Section 2, p. 4: the atomic norm
`‖x‖_A = inf { ∑_k c_k : x = ∑_k c_k a(f_k, φ_k), c_k ≥ 0, f_k ∈ [0,1], φ_k ∈ [0, 2π) }`,
the infimum being over finite decompositions. -/
def atomicNorm (J : Finset ℤ) (x : J → ℂ) : ℝ :=
  sInf {t : ℝ | ∃ (r : ℕ) (c f φ : Fin r → ℝ), (∀ k, 0 ≤ c k) ∧ (∀ k, f k ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ k, φ k ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) ∧ x = ∑ k, (c k : ℂ) • atom J (f k) (φ k) ∧
    t = ∑ k, c k}

/-- Section 2.2, p. 11: `‖x‖_{A,0}`, the least number of atoms `a(f_k, φ_k)` with nonnegative
coefficients `c_k` whose combination `∑_k c_k a(f_k, φ_k)` equals `x`. -/
def atomicL0 (J : Finset ℤ) (x : J → ℂ) : ℕ :=
  sInf {s : ℕ | ∃ (c f φ : Fin s → ℝ), (∀ k, 0 ≤ c k) ∧ (∀ k, f k ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ k, φ k ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) ∧ x = ∑ k, (c k : ℂ) • atom J (f k) (φ k)}

/-- Proposition 2.1, p. 5: `Toep(u)`, the Hermitian Toeplitz matrix on `J` whose first column is
`u`. Here `u k` is the entry `k` places below the diagonal (`k = 0, …, |J| - 1`), so the entry in
row `j` and column `l` is `u (j - l)` for `j ≥ l` and the conjugate of `u (l - j)` for `j < l`. -/
def toep (J : Finset ℤ) (u : ℤ → ℂ) : Matrix J J ℂ :=
  fun j l => if (l : ℤ) ≤ (j : ℤ) then u ((j : ℤ) - (l : ℤ)) else star (u ((l : ℤ) - (j : ℤ)))

/-- Eq. (2.2): the block matrix `[[Toep(u), x], [x^*, t]]`. -/
def sdpBlock (J : Finset ℤ) (u : ℤ → ℂ) (x : J → ℂ) (t : ℝ) : Matrix (J ⊕ Unit) (J ⊕ Unit) ℂ :=
  Matrix.fromBlocks (toep J u) (Matrix.of fun j (_ : Unit) => x j)
    (Matrix.of fun (_ : Unit) j => star (x j)) (Matrix.of fun _ _ => (t : ℂ))

/-- Eq. (2.2): the value of the semidefinite program
`inf { (1/(2|J|)) trace(Toep(u)) + t/2 : [[Toep(u), x], [x^*, t]] ⪰ 0 }`. -/
def sdpValue (J : Finset ℤ) (x : J → ℂ) : ℝ :=
  sInf {v : ℝ | ∃ (u : ℤ → ℂ) (t : ℝ), (sdpBlock J u x t).PosSemidef ∧
    v = 1 / (2 * (J.card : ℝ)) * (Matrix.trace (toep J u)).re + t / 2}

/-- Eq. (2.19): the optimal value of `minimize rank(Toep(u))` subject to
`[[Toep(u), x], [x^*, t]] ⪰ 0`. -/
def rankValue (J : Finset ℤ) (x : J → ℂ) : ℕ :=
  sInf {r : ℕ | ∃ (u : ℤ → ℂ) (t : ℝ), (sdpBlock J u x t).PosSemidef ∧ r = (toep J u).rank}

/-- Eq. (2.9): the dual polynomial `Q(f) = ⟨q, a(f,0)⟩ = ∑_{j ∈ J} q_j e^{-i 2π j f}`. -/
def dualPoly (J : Finset ℤ) (q : J → ℂ) (f : ℝ) : ℂ :=
  ∑ j : J, q j * Complex.exp (-(((2 * Real.pi * f * ((j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I))

/-- Eq. (2.5) and Theorem 2.3, p. 7: `x⋆` is the unique optimizer of
`minimize ‖x‖_A subject to x_j = x⋆_j, j ∈ T`. -/
def IsUniqueOptimizer (J T : Finset ℤ) (xs : J → ℂ) : Prop :=
  ∀ x : J → ℂ, (∀ j : J, (j : ℤ) ∈ T → x j = xs j) → x ≠ xs → atomicNorm J xs < atomicNorm J x

/-- Proposition 2.4, eqs. (2.10)-(2.12): `q` is a dual certificate for the frequencies `f_k` and
coefficients `c_k`: `Q(f_k) = sign(c_k)`, `|Q(f)| < 1` for every `f` not equal (on the circle) to
any `f_k`, and `q_j = 0` for `j ∉ T`. -/
def IsDualCertificate (J T : Finset ℤ) {s : ℕ} (f : Fin s → ℝ) (c : Fin s → ℂ) (q : J → ℂ) :
    Prop :=
  (∀ j : J, (j : ℤ) ∉ T → q j = 0) ∧ (∀ k, dualPoly J q (f k) = csign (c k)) ∧
    ∀ g : ℝ, (∀ k, wrapDist g (f k) ≠ 0) → ‖dualPoly J q g‖ < 1

/-- Eq. (2.13): the block matrix `[[H, -q], [-q^*, 1]]` of the dual semidefinite program. -/
def dualBlock (J : Finset ℤ) (q : J → ℂ) (H : Matrix J J ℂ) : Matrix (J ⊕ Unit) (J ⊕ Unit) ℂ :=
  Matrix.fromBlocks H (Matrix.of fun j (_ : Unit) => -q j)
    (Matrix.of fun (_ : Unit) j => -star (q j)) (Matrix.of fun _ _ => 1)

/-- Eqs. (2.13)-(2.15) with `q_{T^c} = 0`: feasibility for the dual semidefinite program,
`[[H, -q], [-q^*, 1]] ⪰ 0`, `∑_k H_{k,k+d} = 1` for `d = 0` and `= 0` for `d = 1, …, |J|-1`
(sums along the diagonals of `H`), `H` Hermitian, and `q_j = 0` for `j ∉ T`. -/
def IsDualFeasible (J T : Finset ℤ) (q : J → ℂ) (H : Matrix J J ℂ) : Prop :=
  (dualBlock J q H).PosSemidef ∧
    (∀ d : ℕ, d < J.card →
      (∑ a : J, ∑ b : J, if (b : ℤ) - (a : ℤ) = (d : ℤ) then H a b else 0) =
        if d = 0 then 1 else 0) ∧
    H.IsHermitian ∧ ∀ j : J, (j : ℤ) ∉ T → q j = 0

/-- Eq. (2.13): the dual objective `⟨q_T, x_T⟩_ℝ = Re ∑_{j ∈ T} conj(x_j) q_j`. -/
def dualObjective (J T : Finset ℤ) (x q : J → ℂ) : ℝ :=
  (∑ j : J, if (j : ℤ) ∈ T then star (x j) * q j else 0).re

/-- Proposition 2.5, p. 10: the set `𝒟` of optimal solutions `(q, H)` of the dual semidefinite
program (2.13)-(2.15) for the data `x_T`. -/
def dualOptimalSet (J T : Finset ℤ) (x : J → ℂ) : Set ((J → ℂ) × Matrix J J ℂ) :=
  {p | IsDualFeasible J T p.1 p.2 ∧
    ∀ p' : (J → ℂ) × Matrix J J ℂ, IsDualFeasible J T p'.1 p'.2 →
      dualObjective J T x p'.1 ≤ dualObjective J T x p.1}

/-- Eq. (4.2): `g_M(j) = (1/M) ∑_{k = max(j-M, -M)}^{min(j+M, M)} (1 - |k/M|)(1 - |j/M - k/M|)`,
the discrete convolution of two triangular functions. -/
def gM (M : ℕ) (j : ℤ) : ℝ :=
  1 / (M : ℝ) * ∑ k ∈ Finset.Icc (max (j - M) (-(M : ℤ))) (min (j + M) (M : ℤ)),
    (1 - |(k : ℝ) / M|) * (1 - |(j : ℝ) / M - (k : ℝ) / M|)

/-- Eq. (4.2) and p. 16: the `ℓ`-th derivative of the squared Fejér kernel
`K̄_M(f) = [sin(π M f) / (M sin(π f))]^4 = (1/M) ∑_{j=-2M}^{2M} g_M(j) e^{-i 2π f j}`, i.e.
`K̄_M^{(ℓ)}(f) = (1/M) ∑_{j=-2M}^{2M} (-i 2π j)^ℓ g_M(j) e^{-i 2π f j}`. -/
def kerBarDeriv (M ℓ : ℕ) (f : ℝ) : ℂ :=
  1 / (M : ℂ) * ∑ j ∈ symJ M, (-2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) ^ ℓ * (gM M j : ℂ) *
    Complex.exp (-(((2 * Real.pi * f * (j : ℝ) : ℝ) : ℂ) * Complex.I))

/-- Section 4.3, p. 19: the `ℓ`-th derivative of the random kernel
`K_M(f) = (1/M) ∑_{j ∈ T} g_M(j) e^{-i 2π f j}` for the observed index set `T ⊆ J`, i.e.
`K_M^{(ℓ)}(f) = (1/M) ∑_{j=-2M}^{2M} (-i 2π j)^ℓ g_M(j) δ_j e^{-i 2π f j}` with `δ_j = 1_{j ∈ T}`. -/
def kerRandDeriv (M : ℕ) (T : Finset ℤ) (ℓ : ℕ) (f : ℝ) : ℂ :=
  1 / (M : ℂ) * ∑ j ∈ (symJ M).filter (· ∈ T),
    (-2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) ^ ℓ * (gM M j : ℂ) *
      Complex.exp (-(((2 * Real.pi * f * (j : ℝ) : ℝ) : ℂ) * Complex.I))

/-- Section 4.1, p. 16: `|K̄_M''(0)|` (which equals `4π²(M² - 1)/3`). -/
def kerCurv (M : ℕ) : ℝ := ‖kerBarDeriv M 2 0‖

/-- Eqs. (4.6) and (4.24): the `2s × 2s` system matrix built from a kernel with derivatives
`K^{(ℓ)}` and the normalization `κ = |K̄_M''(0)|`:
`[[D₀, D₁/√κ], [-D₁/√κ, -D₂/κ]]` with `[D_ℓ]_{jk} = K^{(ℓ)}(f_j - f_k)`. -/
def sysMatOf {s : ℕ} (K : ℕ → ℝ → ℂ) (κ : ℝ) (f : Fin s → ℝ) :
    Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ :=
  Matrix.fromBlocks (Matrix.of fun j k => K 0 (f j - f k))
    (Matrix.of fun j k => K 1 (f j - f k) / (Real.sqrt κ : ℂ))
    (Matrix.of fun j k => -(K 1 (f j - f k) / (Real.sqrt κ : ℂ)))
    (Matrix.of fun j k => -(K 2 (f j - f k) / (κ : ℂ)))

/-- Eq. (4.6): the deterministic system matrix `D̄` of the squared Fejér kernel `K̄_M`. -/
def sysMatBar (M : ℕ) {s : ℕ} (f : Fin s → ℝ) : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ :=
  sysMatOf (kerBarDeriv M) (kerCurv M) f

/-- Eq. (4.24): the random system matrix `D` of the random kernel `K_M` for the observed set `T`,
normalized by the deterministic `|K̄_M''(0)|`. -/
def sysMat (M : ℕ) (T : Finset ℤ) {s : ℕ} (f : Fin s → ℝ) :
    Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ :=
  sysMatOf (kerRandDeriv M T) (kerCurv M) f

/-- Pp. 17 and 22: the left `2s × s` block `L` of a `2s × 2s` matrix `[L R]` (its first `s`
columns); applied to `D̄⁻¹` it gives `L̄`, applied to `D⁻¹` it gives `L`. -/
def leftBlock {s : ℕ} (A : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ) :
    Matrix (Fin s ⊕ Fin s) (Fin s) ℂ :=
  A.submatrix id Sum.inl

/-- Proposition 4.1, p. 17: the matrix operator norm `‖A‖` (largest singular value), the norm of
`A` as a linear map between Euclidean spaces. -/
def opNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

open Classical in
/-- Section 4.2, p. 18: the probability of an event `E` about the observed set
`T = {j ∈ J : δ_j = 1}` when the `δ_j`, `j ∈ J`, are i.i.d. Bernoulli with `P(δ_j = 1) = p`:
`∑_{T ⊆ J, E(T)} p^{|T|} (1-p)^{|J| - |T|}`. -/
def bernoulliProb (J : Finset ℤ) (p : ℝ) (E : Finset ℤ → Prop) : ℝ :=
  ∑ T ∈ J.powerset, if E T then p ^ T.card * (1 - p) ^ (J.card - T.card) else 0

/-- Theorem 1.1, p. 2: the uniform distribution on the complex unit circle, the law of `e^{iθ}`
for `θ` uniform on `[0, 2π)`. -/
def uniformCircle : Measure ℂ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) •
    (volume.restrict (Set.Ico (0 : ℝ) (2 * Real.pi))).map
      (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I))

/-- Theorem 2.3, p. 7: `μ` is a symmetric distribution on the complex unit circle: a probability
measure on `ℂ` carried by the unit circle and invariant under `u ↦ -u`. -/
def IsSymmetricCircleLaw (μ : Measure ℂ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Metric.sphere (0 : ℂ) 1)ᶜ = 0 ∧ μ.map Neg.neg = μ

/-- Theorems 1.1 and 2.3: the probability that `good T u` fails when the index set `T ⊆ J` of size
`m` is selected uniformly at random and, independently, the signs `u_1, …, u_s` are i.i.d. with
law `μ`: `(1 / #{T ⊆ J : |T| = m}) ∑_{T ⊆ J, |T| = m} μ^{⊗s}{u : ¬ good T u}`. -/
def uniformFailureProb (J : Finset ℤ) (m s : ℕ) (μ : Measure ℂ)
    (good : Finset ℤ → (Fin s → ℂ) → Prop) : ℝ≥0∞ :=
  ((J.powersetCard m).card : ℝ≥0∞)⁻¹ *
    ∑ T ∈ J.powersetCard m, (Measure.pi fun _ : Fin s => μ) {u | ¬ good T u}

end CSOffTheGrid


