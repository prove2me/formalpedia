-- Prove2me | Definitions.Def_CompressedSensingRadar_Basic
-- name    : CompressedSensingRadar_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T09:42:17.638696+00:00
-- url     : https://prove2.me/theorems/eec96fea-a800-44f1-9972-a7a47767ed38
-- title:
--   Time-frequency dictionaries, Alltop sequence, basis pursuit and OMP for compressed sensing radar
-- statement:
--   Objects of Sections II-III and Appendix A of Herman and Strohmer (2008).
--
--   1. **Vectors.** On $\mathbb{C}^n$, $\langle x,y\rangle=\sum_p\overline{x_p}\,y_p$, $\|x\|_2=(\sum_p|x_p|^2)^{1/2}$ and $\|x\|_1=\sum_p|x_p|$. $\|s\|_0$ is the number of nonzero coefficients of $s$, and $s$ is $K$-sparse if $\|s\|_0\le K$.
--   2. **Dictionaries.** A dictionary is a matrix $\Phi=(\varphi_0|\cdots|\varphi_{M-1})\in\mathbb{C}^{n\times M}$ with atoms $\varphi_i$. Its coherence is $\mu(\Phi)=\max_{i\ne i'}|\langle\varphi_i,\varphi_{i'}\rangle|$. Its atoms are unit-norm if $\|\varphi_i\|_2=1$ for all $i$. $\|A\|=\max_{\|v\|_2\le1}\|Av\|_2$ is the spectral norm. For $T\subseteq\{0,\dots,M-1\}$, $\Phi_T$ is the subdictionary of the columns in $T$. The statement $\sigma_{\min}(A)\ge c$ means $c\|v\|_2\le\|Av\|_2$ for every $v$.
--   3. **Basis pursuit (eq. 5).** $s^\star$ solves BP for the data $y$ if $\Phi s^\star=y$ and $\|s^\star\|_1\le\|s'\|_1$ whenever $\Phi s'=y$. BP recovers $s$ from $y$ if $s$ is its unique solution. In the noise-aware program of footnote 1, $s^\star$ minimises $\|s'\|_1$ subject to $|(\Phi s'-y)_n|\le\varepsilon$ for every $n$.
--   4. **Orthogonal matching pursuit.** A run of $t$ steps on $y$ starts from $x_0=0$. At step $k$ it selects an index $\lambda_k$ maximising $|\langle\varphi_j,y-\Phi x_k\rangle|$, with ties broken arbitrarily. Then $x_{k+1}$ is any minimiser of $\|y-\Phi x\|_2$ among the $x$ supported on $\{\lambda_0,\dots,\lambda_k\}$. OMP recovers $s$ if every run of $\|s\|_0$ steps on $y$ ends at $x_{\|s\|_0}=s$.
--   5. **Time-frequency shifts (eq. 10).** $\omega_N=e^{2\pi i/N}$. $T$ is the cyclic unit shift ($T_{p,q}=1$ iff $p\equiv q+1\pmod N$) and $M=\operatorname{diag}(\omega_N^0,\dots,\omega_N^{N-1})$. For $0\le i<N^2$, $H_i=M^{i\bmod N}T^{\lfloor i/N\rfloor}$, and $H=\sum_is_iH_i$ for a coefficient vector $s\in\mathbb{C}^{N^2}$. $\langle A,B\rangle_F=\operatorname{trace}(A^*B)$.
--   6. **Gabor dictionary (eqs. 7, 8, 11).** For a probe $f\in\mathbb{C}^N$, $\Phi\in\mathbb{C}^{N\times N^2}$ has atoms $\varphi_i=H_if$. The block atoms are the columns of $D_kW_N$, $(\varphi^{(k)}_j)_p=f_{(p+k)\bmod N}\,\omega_N^{pj}$.
--   7. **Alltop sequence (eq. 12).** $f_n=N^{-1/2}e^{2\pi i n^3/N}$, $n=0,\dots,N-1$. $\Phi_A$ is the Gabor dictionary of $f_A$.
--   8. **Random signals (Section III-E).** The nonzero coefficients of a random signal are independent circularly symmetric complex Gaussians of mean $0$ and variance $1$: real and imaginary parts are independent $N(0,1/2)$. For a fixed support $T$, the probability that BP recovers $s$ from $y=\Phi s$ is computed with $s$ supported on $T$. For a random $K$-sparse signal the support is moreover a uniformly random $K$-subset. For a random $K$-column subdictionary, the probability $P\{\|X^*X-I\|\ge\delta\}$ is the fraction of $K$-subsets $T$ with $\|\Phi_T^*\Phi_T-I\|\ge\delta$.
--
--   **Formalization Note** Indices run over $\{0,\dots,N-1\}$ and $\{0,\dots,N^2-1\}$ as in the paper. The coherence of a dictionary with fewer than two atoms is $0$. A probability of an event $E$ is the Gaussian measure of the set of coefficient values for which $E$ holds.
-- source:
--   Herman and Strohmer, High-Resolution Radar via Compressed Sensing, arXiv:0803.2257v2 (2008), Section II (eq. (5), footnote 1), Section III-A to III-E (eqs. (6)-(12)), Appendix A (Propositions 1-3); OMP as in Tropp, Greed is good (2004), Algorithm 3

import Mathlib

/-!
Herman and Strohmer, *High-Resolution Radar via Compressed Sensing*, arXiv:0803.2257v2 (2008),
IEEE Trans. Signal Process. 57(6) (2009): sparse vectors, basis pursuit and orthogonal matching
pursuit (Section II and the cited Tropp 2004), the coherence of a dictionary (Section III-B), the
time-frequency shift basis and its Gabor dictionary (Section III-C), the Alltop sequence
(Section III-D), and the random signal and random subdictionary models of Section III-E and
Appendix A.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace CompressedSensingRadar

section Vectors

variable {ι : Type*} [Fintype ι]

/-- The Hermitian inner product `⟨x, y⟩ = ∑ₙ conj(xₙ) yₙ` on `ℂ^ι` (Section III-B). -/
def ip (x y : ι → ℂ) : ℂ := ∑ n, star (x n) * y n

/-- The Euclidean norm `‖x‖₂ = (∑ₙ |xₙ|²)^{1/2}`. -/
def norm2 (x : ι → ℂ) : ℝ := Real.sqrt (∑ n, ‖x n‖ ^ 2)

/-- The `ℓ¹` norm `‖x‖₁ = ∑ₙ |xₙ|`, the objective of basis pursuit, eq. (5). -/
def norm1 (x : ι → ℂ) : ℝ := ∑ n, ‖x n‖

/-- The number of nonzero coefficients of `s`. -/
def suppCard (s : ι → ℂ) : ℕ := {i | s i ≠ 0}.ncard

/-- Section II: `s` is `K`-sparse if at most `K` of its coefficients are nonzero. -/
def IsSparse (K : ℕ) (s : ι → ℂ) : Prop := suppCard s ≤ K

end Vectors

section Dictionaries

variable {m ι : Type*} [Fintype m] [Fintype ι]

/-- The `i`-th atom (column) `φᵢ` of a dictionary `Φ = (φ₀ | ⋯ | φ_{M-1})`. -/
def atom (Φ : Matrix m ι ℂ) (i : ι) : m → ℂ := fun p => Φ p i

/-- Section III-B: the atoms of `Φ` have unit norm, `‖φᵢ‖₂ = 1`, the standing assumption under
which the coherence is used. -/
def HasUnitAtoms (Φ : Matrix m ι ℂ) : Prop := ∀ i, norm2 (atom Φ i) = 1

/-- Section III-B: the coherence `μ(Φ) = max_{i ≠ i'} |⟨φᵢ, φᵢ'⟩|` (this is `0` if `Φ` has fewer
than two atoms). -/
def coherence (Φ : Matrix m ι ℂ) : ℝ :=
  ⨆ (i : ι) (i' : ι) (_ : i ≠ i'), ‖ip (atom Φ i) (atom Φ i')‖

/-- The spectral norm `‖A‖ = max_{‖v‖₂ ≤ 1} ‖Av‖₂` (Appendix A, Proposition 1). -/
def specNorm {k : Type*} [Fintype k] (A : Matrix m k ℂ) : ℝ :=
  sSup ((fun v => norm2 (A.mulVec v)) '' {v | norm2 v ≤ 1})

/-- Appendix A, Proposition 2: the least singular value of `A` is at least `c`, i.e.
`c ‖v‖₂ ≤ ‖Av‖₂` for every `v`. -/
def LeastSingValGe {k : Type*} [Fintype k] (A : Matrix m k ℂ) (c : ℝ) : Prop :=
  ∀ v : k → ℂ, c * norm2 v ≤ norm2 (A.mulVec v)

/-- Appendix A: the subdictionary `Φ_T` of the columns `φⱼ`, `j ∈ T`. -/
def subdict (Φ : Matrix m ι ℂ) (T : Finset ι) : Matrix m T ℂ := fun p j => Φ p j

/-- Appendix A, Proposition 1: the Gram matrix `X* X` of the subdictionary `X = Φ_T`. -/
def subGram (Φ : Matrix m ι ℂ) (T : Finset ι) : Matrix T T ℂ :=
  (subdict Φ T).conjTranspose * subdict Φ T

/-- Eq. (5): `s` solves basis pursuit `min ‖s'‖₁ s.t. Φ s' = y`. -/
def IsBPSolution (Φ : Matrix m ι ℂ) (y : m → ℂ) (s : ι → ℂ) : Prop :=
  Φ.mulVec s = y ∧ ∀ s' : ι → ℂ, Φ.mulVec s' = y → norm1 s ≤ norm1 s'

/-- Basis pursuit recovers `s` from the observation `y`: `s` is the unique solution of eq. (5). -/
def BPRecovers (Φ : Matrix m ι ℂ) (y : m → ℂ) (s : ι → ℂ) : Prop :=
  ∀ s' : ι → ℂ, IsBPSolution Φ y s' ↔ s' = s

/-- Footnote 1 of Section II: `s` solves the noise-aware basis pursuit
`min ‖s'‖₁ s.t. |(Φ s' - y)ₙ| ≤ ε` for every `n`. -/
def IsNoisyBPSolution (Φ : Matrix m ι ℂ) (y : m → ℂ) (ε : ℝ) (s : ι → ℂ) : Prop :=
  (∀ n, ‖(Φ.mulVec s - y) n‖ ≤ ε) ∧
    ∀ s' : ι → ℂ, (∀ n, ‖(Φ.mulVec s' - y) n‖ ≤ ε) → norm1 s ≤ norm1 s'

/-- Orthogonal matching pursuit (Section II; Tropp 2004, Algorithm 3), run for `t` steps on `y`:
`x 0 = 0`; at step `k < t` the index `lam k` maximises `|⟨φⱼ, y - Φ x_k⟩|` over all `j` (any
choice among ties), and `x (k+1)` minimises `‖y - Φ x‖₂` over the `x` supported on
`{lam 0, …, lam k}` (any minimiser). -/
def IsOMPRun (Φ : Matrix m ι ℂ) (y : m → ℂ) (t : ℕ) (lam : ℕ → ι) (x : ℕ → ι → ℂ) : Prop :=
  x 0 = 0 ∧ ∀ k < t,
    (∀ j, ‖ip (atom Φ j) (y - Φ.mulVec (x k))‖ ≤ ‖ip (atom Φ (lam k)) (y - Φ.mulVec (x k))‖) ∧
    (∀ i, (∀ l ≤ k, lam l ≠ i) → x (k + 1) i = 0) ∧
    (∀ x' : ι → ℂ, (∀ i, (∀ l ≤ k, lam l ≠ i) → x' i = 0) →
      norm2 (y - Φ.mulVec (x (k + 1))) ≤ norm2 (y - Φ.mulVec x'))

/-- Orthogonal matching pursuit recovers `s` from `y`: every run of `‖s‖₀` steps (the number of
nonzero coefficients of `s`) ends at `s`. -/
def OMPRecovers (Φ : Matrix m ι ℂ) (y : m → ℂ) (s : ι → ℂ) : Prop :=
  ∀ (lam : ℕ → ι) (x : ℕ → ι → ℂ), IsOMPRun Φ y (suppCard s) lam x → x (suppCard s) = s

end Dictionaries

section TimeFrequency

variable (N : ℕ)

/-- Section III-C: the `N`-th root of unity `ω_N = e^{2πi/N}`. -/
def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- Section III-C: the unit-shift operator `T`, `T_{p,q} = 1` if `p ≡ q + 1 (mod N)` and `0`
otherwise. -/
def shiftMat : Matrix (Fin N) (Fin N) ℂ :=
  fun p q => if (p : ℕ) = ((q : ℕ) + 1) % N then 1 else 0

/-- Section III-C: the modulation operator `M = diag(ω_N^0, …, ω_N^{N-1})`. -/
def modMat : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal fun p => omega N ^ (p : ℕ)

/-- Eq. (10): the `i`-th time-frequency shift `Hᵢ = M^{i mod N} T^{⌊i/N⌋}`, `0 ≤ i < N²`. -/
def tfShift (i : Fin (N ^ 2)) : Matrix (Fin N) (Fin N) ℂ :=
  modMat N ^ ((i : ℕ) % N) * shiftMat N ^ ((i : ℕ) / N)

/-- Eq. (6): the matrix `H = ∑ᵢ sᵢ Hᵢ` with coefficient vector `s ∈ ℂ^{N²}`. -/
def tfSynth (s : Fin (N ^ 2) → ℂ) : Matrix (Fin N) (Fin N) ℂ := ∑ i, s i • tfShift N i

/-- Section III-A: the Frobenius inner product `⟨A, B⟩_F = trace(A* B)`. -/
def frobIp (A B : Matrix (Fin N) (Fin N) ℂ) : ℂ := (A.conjTranspose * B).trace

/-- Eqs. (7)-(8): the Gabor dictionary `Φ = (φ₀ | ⋯ | φ_{N²-1}) ∈ ℂ^{N×N²}` generated by the
probe `f`, with atoms `φᵢ = Hᵢ f`. -/
def gaborDict (f : Fin N → ℂ) : Matrix (Fin N) (Fin (N ^ 2)) ℂ :=
  fun p i => (tfShift N i).mulVec f p

/-- Eq. (11): the `j`-th column `φⱼ^{(k)}` of the block `Φ^{(k)} = D_k W_N`, where
`D_k = diag(f_k, …, f_{N-1}, f_0, …, f_{k-1})` and `W_N = (ω_N^{pq})`; its `p`-th entry is
`f_{(p+k) mod N} ω_N^{pj}`. -/
def blockAtom (f : Fin N → ℂ) (k j : Fin N) : Fin N → ℂ :=
  fun p => f (p + k) * omega N ^ ((p : ℕ) * (j : ℕ))

/-- Eq. (12): the Alltop sequence `fₙ = N^{-1/2} e^{2πi n³/N}`, `n = 0, …, N-1`. -/
def alltop : Fin N → ℂ :=
  fun n => ((Real.sqrt N)⁻¹ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((n : ℕ) ^ 3 : ℂ) / N)

end TimeFrequency

section Random

variable {n M : ℕ}

/-- Section III-E: the law of the coefficients of a random signal. Coordinate `(i, 0)` is the real
part and `(i, 1)` the imaginary part of coefficient `i`; all are independent `N(0, 1/2)`, so each
coefficient is a circularly symmetric complex Gaussian of zero mean and unit variance. -/
def gaussCoeffs (M : ℕ) : Measure (Fin M × Fin 2 → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 2⁻¹

/-- Section III-E: the signal with support `T` whose coefficients on `T` are given by `w`. -/
def maskedSignal (T : Finset (Fin M)) (w : Fin M × Fin 2 → ℝ) : Fin M → ℂ :=
  fun i => if i ∈ T then (w (i, 0) : ℂ) + (w (i, 1) : ℂ) * Complex.I else 0

/-- Appendix A, Proposition 2: the probability that basis pursuit recovers a random signal `s`
with fixed support `T` (independent standard complex Gaussian coefficients on `T`) from
`y = Φ s`. -/
def bpProbOnSupport (Φ : Matrix (Fin n) (Fin M) ℂ) (T : Finset (Fin M)) : ℝ :=
  (gaussCoeffs M).real {w | BPRecovers Φ (Φ.mulVec (maskedSignal T w)) (maskedSignal T w)}

/-- Section III-E: the probability that basis pursuit recovers a random `K`-sparse signal `s`
from `y = Φ s`. The support is a uniformly random `K`-subset of the `M` indices and the nonzero
coefficients are independent standard complex Gaussians. -/
def bpProbRandom (Φ : Matrix (Fin n) (Fin M) ℂ) (K : ℕ) : ℝ :=
  (∑ T ∈ (Finset.univ : Finset (Fin M)).powersetCard K, bpProbOnSupport Φ T) /
    ((Finset.univ : Finset (Fin M)).powersetCard K).card

open Classical in
/-- Appendix A, Proposition 1: for a random `K`-column subdictionary `X = Φ_T` (every `K`-subset
`T` equally likely), the probability `P{‖X* X - I‖ ≥ δ}`. -/
def illCondProb (Φ : Matrix (Fin n) (Fin M) ℂ) (K : ℕ) (δ : ℝ) : ℝ :=
  (((Finset.univ : Finset (Fin M)).powersetCard K).filter
      fun T => δ ≤ specNorm (subGram Φ T - 1)).card /
    ((Finset.univ : Finset (Fin M)).powersetCard K).card

end Random

end CompressedSensingRadar


