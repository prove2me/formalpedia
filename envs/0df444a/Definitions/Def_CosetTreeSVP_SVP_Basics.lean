-- Prove2me | Definitions.Def_CosetTreeSVP_SVP_Basics
-- name    : CosetTreeSVP_SVP_Basics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:31:34.063881+00:00
-- url     : https://prove2.me/theorems/dc12a2fd-860e-4b26-a022-4147546fe788
-- title:
--   Constants β, t₀, g, s; shortest vectors; discrete Gaussian weights; the periodic Gaussian F_σ, its gradient, and the q-ary f, G; the parameters p, q, m, Q, N of Eq. (17)
-- statement:
--   Throughout, $L = B\mathbb Z^n$ is the lattice of a nonsingular $B \in \mathbb R^{n\times n}$ (the published `SuperlatSVP.lat`), $\lambda_1(L)$ its first minimum (`SuperlatSVP.lam1`), $L^* = B^{-T}\mathbb Z^n$ its dual (the published `RegevLWE.GaussConv.dual`), and $\rho_\sigma(x) = e^{-\pi\|x\|^2/\sigma^2}$ (`RegevLWE.GaussConv.rho`).
--
--   **Constants.** The lattice-point constant is $\beta = 2^{R}$ with
--   $$R = a\log_2 a - b\log_2 b,\qquad a = \frac{1+\sin\theta}{2\sin\theta},\ b = \frac{1-\sin\theta}{2\sin\theta},\ \theta = \pi/3,$$
--   the Kabatiansky–Levenshtein exponent at angle $\pi/3$ ($R = 0.401413\ldots$). Further $t_0 = \beta^2/(4e\ln 2) = 0.23147\ldots$, $g = \tfrac12\log_2(t/t_0)$ and $s = \sqrt{4nt\ln 2/(\pi d^2)}$ for the fixed $t \in (t_0, 1/4)$ and the guess $d > 0$.
--
--   **Vectors.** $\mathbb C^n$ carries the Hermitian norm; a real vector is viewed in $\mathbb C^n$ by `toC`; $\operatorname{Re}A, \operatorname{Im}A \in \mathbb R^n$ are `reVec`, `imVec`. A shortest vector $v$ of $L$ is a nonzero $v \in L$ with $\|v\| = \lambda_1(L)$.
--
--   **Discrete Gaussian.** $D_{L,\sigma}(x) = \rho_\sigma(x)/\rho_\sigma(L)$ on $L$ (the published `RegevLWE.Hyperplane.discreteGaussian`), here as a weight in $[0,\infty]$; $\Pr_{X\sim D_{L,\sigma}}[X \in S]$ and $\mathbb E_{X\sim D_{L,\sigma}}[h(X)]$ for $h \ge 0$ are the corresponding sums in $[0,\infty]$.
--
--   **Periodic Gaussian (Eqs. (9), (10)).** $F_\sigma(z) = \rho_\sigma(L+z)/\rho_\sigma(L)$ and
--   $$\nabla F_\sigma(z) = -\frac{2\pi}{\sigma^2\rho_\sigma(L)}\sum_{x\in L}(x+z)\,\rho_\sigma(x+z).$$
--
--   **q-ary objects (Eq. (11)).** $\omega_q = e^{2\pi i/q}$, $\langle a, b\rangle = \sum_k a_kb_k \in \mathbb F_q$. For $X \in L^*$, $[X]_q = B^TX \bmod q \in \mathbb F_q^n$; for $v \in L$, $w = B^{-1}v \bmod q$. For $w \in \mathbb F_q^n$ (lifted to $\{0,\dots,q-1\}^n$), $f(w) = F_{1/s}(Bw/q)$ and $G(w) = \nabla F_{1/s}(Bw/q)$.
--
--   **Parameters (Eq. (17), §4.3, footnote 7).** $p$ is the largest power of two with $p \le n/\ln^3 n$, $q$ the smallest prime larger than $2\sqrt p$, $m = \log_2 p + 1$, $Q = q^{\lfloor n/m\rfloor}$ and $N = Qp^4$.
--
--   **Formalization Note.** `beta`, `t0`, `gPar t`, `sPar n t d`, `IsShortestVec`, `dgW`, `dgProb`, `dgExpect`, `perGauss`, `perGaussGrad`, `omegaPow`, `dotq`, `resid`, `coeffMod`, `fq B q s`, `Gq B q s`, `pN`, `qN`, `mN`, `QN`, `NN`. $f$ and $G$ use the primal representations (first forms of (9), (10)); the dual forms are Poisson summation, facts rather than definitions. `resid` and `coeffMod` round $B^TX$ and $B^{-1}v$ to integers, which is exact on $L^*$ and $L$. When $n/\ln^3 n < 2$ the formula gives $p = 1$; the paper's parameters are only used for large $n$, and every statement using them holds for $n \ge n_0$.
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), pp. 11–14 (PDF 13–16), §2.1, §3, Eqs. (9)–(11), (17), footnote 7

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian

open MeasureTheory
open scoped ENNReal

namespace CosetTreeSVP.SVP

/-! ### Constants of §2.1 and §3 -/

/-- The Kabatiansky–Levenshtein exponent at angle `π/3`:
`R = a log₂ a − b log₂ b` with `a = (1 + sin θ)/(2 sin θ)`, `b = (1 − sin θ)/(2 sin θ)`, `θ = π/3`.
Numerically `R = 0.40141354…`. -/
noncomputable def klExponent : ℝ :=
  let S := Real.sin (Real.pi / 3)
  let a := (1 + S) / (2 * S)
  let b := (1 - S) / (2 * S)
  a * Real.logb 2 a - b * Real.logb 2 b

/-- The lattice-point constant `β = 2^{0.4014…}` of §2.1 (p. 11), read as `2^R` with `R` the
Kabatiansky–Levenshtein exponent `klExponent`. -/
noncomputable def beta : ℝ := (2 : ℝ) ^ klExponent

/-- `t₀ := β² / (4 e ln 2) = 0.23147…` (§3, p. 12). -/
noncomputable def t0 : ℝ := beta ^ 2 / (4 * Real.exp 1 * Real.log 2)

/-- `g = ½ log₂ (t / t₀)` (§3, p. 12). -/
noncomputable def gPar (t : ℝ) : ℝ := (1 / 2) * Real.logb 2 (t / t0)

/-- The width `s = √(4 n t ln 2 / (π d²))` (§3, p. 12). -/
noncomputable def sPar (n : ℕ) (t d : ℝ) : ℝ :=
  Real.sqrt (4 * n * t * Real.log 2 / (Real.pi * d ^ 2))

/-! ### Vectors -/

/-- `ℝⁿ` (the published `SuperlatSVP.E`). -/
abbrev E (n : ℕ) := SuperlatSVP.E n

/-- `ℂⁿ` with the Hermitian norm `‖z‖ = (Σ |z_k|²)^{1/2}`. -/
abbrev CE (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- A real vector viewed in `ℂⁿ`. -/
noncomputable def toC {n : ℕ} (x : E n) : CE n := WithLp.toLp 2 (fun k => ((x.ofLp k : ℝ) : ℂ))

/-- The real part `Re A ∈ ℝⁿ` of `A ∈ ℂⁿ`. -/
noncomputable def reVec {n : ℕ} (A : CE n) : E n := WithLp.toLp 2 (fun k => (A.ofLp k).re)

/-- The imaginary part `Im A ∈ ℝⁿ` of `A ∈ ℂⁿ`. -/
noncomputable def imVec {n : ℕ} (A : CE n) : E n := WithLp.toLp 2 (fun k => (A.ofLp k).im)

/-! ### Lattices (§2.1) -/

/-- `v` is a shortest vector of `L`: `v ∈ L`, `v ≠ 0` and `‖v‖ = λ₁(L)`. -/
def IsShortestVec {n : ℕ} (L : Submodule ℤ (E n)) (v : E n) : Prop :=
  v ∈ L ∧ v ≠ 0 ∧ ‖v‖ = SuperlatSVP.lam1 L

/-- The dual lattice `L* = {y : ⟨x, y⟩ ∈ ℤ ∀ x ∈ L}` (the published `RegevLWE.GaussConv.dual`); for
`L = BZⁿ` with `B` nonsingular it is `B^{−T}Zⁿ`. -/
noncomputable abbrev dualL {n : ℕ} (L : Submodule ℤ (E n)) : Submodule ℤ (E n) :=
  RegevLWE.GaussConv.dual L

/-- The discrete Gaussian `D_{L,σ}` as a weight in `[0, ∞]`: `ρ_σ(x) / ρ_σ(L)` for `x ∈ L`. -/
noncomputable def dgW {n : ℕ} (L : Submodule ℤ (E n)) (σ : ℝ) (x : L) : ℝ≥0∞ :=
  ENNReal.ofReal (RegevLWE.Hyperplane.discreteGaussian L σ x)

/-- `P_{X∼D_{L,σ}}[X ∈ S]`. -/
noncomputable def dgProb {n : ℕ} (L : Submodule ℤ (E n)) (σ : ℝ) (S : Set (E n)) : ℝ≥0∞ :=
  ∑' x : L, dgW L σ x * S.indicator (fun _ => 1) (x : E n)

/-- `E_{X∼D_{L,σ}}[h(X)]` for a nonnegative `h` (values in `[0, ∞]`). -/
noncomputable def dgExpect {n : ℕ} (L : Submodule ℤ (E n)) (σ : ℝ) (h : E n → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x : L, dgW L σ x * h (x : E n)

/-! ### Periodic Gaussian (Eqs. (9)–(12)) -/

/-- The periodic Gaussian `F_σ(z) = ρ_σ(L + z) / ρ_σ(L)` (Eq. (9), first representation). -/
noncomputable def perGauss {n : ℕ} (L : Submodule ℤ (E n)) (σ : ℝ) (z : E n) : ℝ :=
  RegevLWE.GaussConv.rhoCoset σ L z / RegevLWE.Hyperplane.rhoLattice σ L

/-- Its gradient `∇F_σ(z) = −(2π / (σ² ρ_σ(L))) Σ_{x∈L} (x + z) ρ_σ(x + z)` (Eq. (10), first
representation). -/
noncomputable def perGaussGrad {n : ℕ} (L : Submodule ℤ (E n)) (σ : ℝ) (z : E n) : E n :=
  (-(2 * Real.pi) / (σ ^ 2 * RegevLWE.Hyperplane.rhoLattice σ L)) •
    ∑' x : L, RegevLWE.GaussConv.rho σ ((x : E n) + z) • ((x : E n) + z)

/-! ### q-ary objects (§2, §3) -/

/-- `ω_q^z = exp(2πi z / q)` for `z ∈ F_q` (any integral lift gives the same value). -/
noncomputable def omegaPow (q : ℕ) (z : ZMod q) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (z.val : ℂ) / (q : ℂ))

/-- The standard bilinear form `⟨a, b⟩ = Σ_k a_k b_k` on `F_qⁿ`. -/
def dotq {n q : ℕ} (a b : Fin n → ZMod q) : ZMod q := ∑ k, a k * b k

/-- The residue `[X]_q := BᵀX mod q ∈ F_qⁿ` of a dual vector `X ∈ L* = B^{−T}Zⁿ` (§3, p. 13);
`BᵀX ∈ Zⁿ` for `X ∈ L*`, so rounding is exact there. -/
noncomputable def resid {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (q : ℕ) (X : E n) :
    Fin n → ZMod q :=
  fun k => ((round ((B.transpose.mulVec X.ofLp) k) : ℤ) : ZMod q)

/-- `B^{−1} v mod q ∈ F_qⁿ` for a lattice vector `v ∈ L = BZⁿ` (`B^{−1}v ∈ Zⁿ`). -/
noncomputable def coeffMod {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (q : ℕ) (v : E n) :
    Fin n → ZMod q :=
  fun k => ((round ((B⁻¹.mulVec v.ofLp) k) : ℤ) : ZMod q)

/-- The point `Bw/q ∈ ℝⁿ` for `w ∈ F_qⁿ`, with the lift `w_k ∈ {0, …, q − 1}`. -/
noncomputable def ptq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (q : ℕ) (w : Fin n → ZMod q) : E n :=
  WithLp.toLp 2 ((1 / (q : ℝ)) • B.mulVec (fun k => ((w k).val : ℝ)))

/-- The q-ary periodic Gaussian `f(w) := F_{1/s}(Bw/q)` (Eq. (11)) for the lattice `L = BZⁿ`. -/
noncomputable def fq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (q : ℕ) (s : ℝ)
    (w : Fin n → ZMod q) : ℝ :=
  perGauss (SuperlatSVP.lat B) (1 / s) (ptq B q w)

/-- Its gradient `G(w) := ∇F_{1/s}(Bw/q)` (Eq. (11)). -/
noncomputable def Gq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (q : ℕ) (s : ℝ)
    (w : Fin n → ZMod q) : E n :=
  perGaussGrad (SuperlatSVP.lat B) (1 / s) (ptq B q w)

/-! ### Parameters of Eq. (17) and §4.4 -/

/-- `p` = the largest power of two with `p ≤ n / log³ n` (natural logarithm), i.e.
`2^{⌊log₂ ⌊n / ln³ n⌋⌋}`; it equals `1` when `n / ln³ n < 2` (the paper's parameters are only
used for large `n`). -/
noncomputable def pN (n : ℕ) : ℕ := 2 ^ Nat.log 2 ⌊(n : ℝ) / Real.log n ^ 3⌋₊

lemma exists_prime_gt (x : ℝ) : ∃ q : ℕ, q.Prime ∧ x < q := by
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes (⌈x⌉₊ + 1)
  exact ⟨q, hp, lt_of_lt_of_le (Nat.lt_of_ceil_lt (by omega)) le_rfl⟩

open Classical in
/-- `q` = the smallest prime larger than `2√p`. -/
noncomputable def qN (n : ℕ) : ℕ := Nat.find (exists_prime_gt (2 * Real.sqrt (pN n)))

/-- `m = log₂ p + 1`. -/
noncomputable def mN (n : ℕ) : ℕ := Nat.log 2 (pN n) + 1

/-- Footnote 7: `Q := |H₁| = ⋯ = |H_{m−1}| = q^ℓ`, `ℓ := ⌊n/m⌋`. -/
noncomputable def QN (n : ℕ) : ℕ := qN n ^ (n / mN n)

/-- `N := Q p⁴` (§4.3). -/
noncomputable def NN (n : ℕ) : ℕ := QN n * pN n ^ 4

lemma qN_prime (n : ℕ) : (qN n).Prime := by
  classical
  exact (Nat.find_spec (exists_prime_gt (2 * Real.sqrt (pN n)))).1

instance (n : ℕ) : NeZero (qN n) := ⟨(qN_prime n).ne_zero⟩

instance (n : ℕ) : Fact (qN n).Prime := ⟨qN_prime n⟩

end CosetTreeSVP.SVP


