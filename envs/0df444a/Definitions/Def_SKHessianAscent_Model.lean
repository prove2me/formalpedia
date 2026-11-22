-- Prove2me | Definitions.Def_SKHessianAscent_Model
-- name    : SKHessianAscent_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-22T19:53:53.604066+00:00
-- url     : https://prove2.me/theorems/5267f332-522a-4661-aa37-fdd936ad64fd
-- title:
--   The SK Gibbs measure $\mu_{\beta A}$, the TAP Hessian $\nabla^2_m\mathcal F_{\mathrm{TAP}}$, the safe set $\mathcal S_{\beta,A}(c)$ and the event $\Omega_{\beta,c}$
-- statement:
--   Throughout, $n\ge 0$, $A$ is a real $n\times n$ matrix, $\beta\in\mathbb R$, spins are $\sigma\in\{\pm1\}^n$ and vectors $m\in\mathbb R^n$ carry the Euclidean norm $\|m\|_2$ (`l2`).
--
--   **Norms and matrix operations.** `opNorm` is the Euclidean operator norm $\|M\|_{\mathrm{op}}$, `frob` the Frobenius norm $\|M\|_F$, `schatten2` the normalized Schatten 2-norm $\|M\|_{L^2}=\|M\|_F/\sqrt n$, `ntr` the normalized trace $\mathrm{tr}_n(M)=\mathrm{Tr}(M)/n$, and `diagPart` the diagonal projection $\mathbf E_{\mathcal D_n}[M]=\mathrm{diag}(M_{11},\dots,M_{nn})$.
--
--   **Gibbs measure (p. 1).** `ham A σ` is $H_A(\sigma)=\tfrac12\langle\sigma,A\sigma\rangle$ and `gibbsSK β A` is
--   $$\mu_{\beta A}(\sigma)=\frac{1}{Z(\beta A)}\exp\Big(\tfrac12\langle\sigma,\beta A\sigma\rangle\Big),\qquad Z(\beta A)=\sum_{\sigma\in\{\pm1\}^n}\exp\Big(\tfrac12\langle\sigma,\beta A\sigma\rangle\Big).$$
--   `tiltSK β A y` is the tilted measure $\mu_{\beta A,y}(\sigma)\propto\mu_{\beta A}(\sigma)e^{\langle y,\sigma\rangle}$, and `meanVec p` is the mean vector $\langle\sigma\rangle_p$ of a law $p$ on $\{\pm1\}^n$.
--
--   **TAP Hessian (Definition 2.1, (2.2)).** `cube n` is $(-1,1)^n$, `Dmat m` is $D(m)=\mathrm{diag}\big(1/(1-m_i^2)\big)$ and `Dinv m` is $D(m)^{-1}=\mathrm{diag}(1-m_i^2)$. `tapHess β A m` is the Hessian in $m$ of the TAP free energy (2.1),
--   $$\nabla^2_m\mathcal F_{\mathrm{TAP}}(m)=-\beta A+D(m)+\beta^2\Big(1-\frac{\|m\|_2^2}{n}\Big)I_n-\frac{2\beta^2}{n}mm^{\mathsf T},$$
--   and `Qhat β A m` is $\widehat Q(m)=\big(\nabla^2_m\mathcal F_{\mathrm{TAP}}(m)\big)^{-1}$.
--
--   **Safe set (Definition 2.2).** `safeSet β A c` is
--   $$\mathcal S_{\beta,A}(c)=\big\{m\in(-1,1)^n:\ c\,D(m)\prec\nabla^2\mathcal F_{\mathrm{TAP}}(m)\big\},$$
--   and `cubeBall x r` is $B_\square(x,r)=\{u\in(-1,1)^n:\|u-x\|_2<r\}$.
--
--   **Coefficients of the algorithmic process ((2.4), (d5)).** `fDrift β A m` is
--   $$f(m)=\Big(\mathbf E_{\mathcal D_n}\big[\widehat Q(m)^2\big]D(m)^2-\frac{\beta^2}{n}\big(\mathrm{Tr}[\widehat Q(m)^2]\,I_n+2\widehat Q(m)^2\big)\Big)m,$$
--   and `omega β A m` is $\omega(m)=\tfrac12\big(\mathrm{Tr}[\widehat Q(m)]+\|m\|_2^2\big)$.
--
--   **The diagonal event ((5.36), (6.3)–(6.5)).** For a diagonal matrix $D=\mathrm{diag}(d)$, `resolventArg β A d` is $\beta^2\mathrm{tr}_n(D^{-1})I_n-\beta A+D$ and `diagError β A d` is
--   $$\Big\|\mathbf E_{\mathcal D_n}\big[D(\beta^2\mathrm{tr}_n(D^{-1})I_n-\beta A+D)^{-2}D\big]-\frac{I_n}{1-\beta^2\mathrm{tr}_n(D^{-2})}\Big\|_{L^2}.$$
--   `gammaY β c` is $\gamma_Y=\min\big\{\tfrac{(1-\beta)^4}{4(1+2\beta^2)^2},\big(1+\tfrac{1+3\beta}{c}\big)^{-2}\big\}$; `SD β A c` is $S_D=\{D\in\mathcal D_n([1,\infty)):\beta^2\mathrm{tr}_n(D^{-1})I_n-\beta A+D\succeq cI_n\}$; and `OmegaEvent β c C n` is the set of matrices $A$ with `diagError` at most $C\beta/(\gamma_Y^2\sqrt n)$ for every $D\in S_D$, i.e. the event $\Omega_{\beta,c}$ of (6.5) with its universal constant named $C$.
--
--   These are the objects in which the desiderata (d1)–(d5) of the paper are stated.
--
--   **Formalization Note** Spins are the published `OAI.CriticalSK.Spin n = Fin n → Bool` and laws on the cube are mass functions `Spin n → ℝ`. $X\preceq Y$ is `(Y - X).PosSemidef` and $X\prec Y$ is `(Y - X).PosDef`; both require symmetric matrices, so for a non-symmetric $A$ the safe set is empty. $\widehat Q(m)$ is Mathlib's matrix inverse, which is $0$ for a singular matrix; the paper defines $\widehat Q$ only where the Hessian is positive definite, which holds on the safe set of a symmetric $A$. The free energy (2.1) itself is not encoded: only its Hessian (2.2) is used.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §1 p. 1 (Gibbs measure), Definition 2.1 and (2.2) pp. 4–5, Definition 2.2 p. 5, (2.4) p. 5, (d5) p. 6, (5.36) p. 35, (6.1)–(6.5) pp. 36–37

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_gibbsOf
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_tilt

open OAI.CriticalSK SKAnnealing.Sampling
open scoped BigOperators

namespace SKHessianAscent

/-!
# The SK Gibbs measure, the TAP Hessian and the safe set

H. Lee, J. S. Sandhu, J. Shi, *Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick
model at β < 1*, §1 (p. 1), §2.1–2.2 (pp. 4–6), §6 (p. 36).

**Formalization Note.**
* Spins are the published `OAI.CriticalSK.Spin n = Fin n → Bool` with values `±1`
  (`spinValue`); laws on `{±1}^n` are mass functions `Spin n → ℝ` (published `gibbsOf`, `tilt`,
  `lawMean`, `lawCov`, `lawTV`).
* Vectors of `ℝ^n` are functions `Fin n → ℝ` and every vector norm is written out as the Euclidean
  norm `l2` (the default norm of `Fin n → ℝ` in Mathlib is the sup norm and is never used).
* `X ⪯ Y` for symmetric matrices is written `(Y - X).PosSemidef`, and `X ≺ Y` is
  `(Y - X).PosDef`.
* The paper's `E_{D_n}` is the projection onto diagonal matrices (`diagPart`), `tr_n = Tr / n`
  (`ntr`), and `‖·‖_{L²}` is the normalized Schatten 2-norm `‖X‖_{L²} = ‖X‖_F / √n`
  (`schatten2`), as stated in §6 (p. 37).
-/

noncomputable section

/-- The Euclidean norm `‖v‖₂` of a vector `v ∈ ℝ^n`. -/
def l2 {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- The Euclidean operator norm `‖M‖_op` of a real `n × n` matrix. -/
def opNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖

/-- The Frobenius norm `‖M‖_F`. -/
def frob {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ := Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- The normalized Schatten 2-norm `‖M‖_{L²} = (tr_n(MᵀM))^{1/2} = ‖M‖_F / √n`. -/
def schatten2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt ((∑ i, ∑ j, M i j ^ 2) / n)

/-- The normalized trace `tr_n(M) = Tr(M) / n`. -/
def ntr {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ := M.trace / n

/-- `E_{D_n}[M]`: the diagonal part of `M` (the projection onto diagonal matrices). -/
def diagPart {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => M i i

/-- The SK Hamiltonian `H_A(σ) = ½⟨σ, Aσ⟩` of an interaction matrix `A`. -/
def ham {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (σ : Spin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, A i j * spinValue (σ i) * spinValue (σ j)

/-- The **SK Gibbs measure** `μ_{βA}(σ) = exp(½⟨σ, βAσ⟩) / Z(βA)` on `{±1}^n` (p. 1). -/
def gibbsSK {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Spin n → ℝ :=
  gibbsOf (ham A) β

/-- The tilted measure `μ_{βA,y}(σ) ∝ μ_{βA}(σ) e^{⟨y,σ⟩}` (p. 7). -/
def tiltSK {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) : Spin n → ℝ :=
  tilt (gibbsSK β A) y

/-- The mean (magnetization) vector `⟨σ⟩_p` of a law `p` on `{±1}^n`. -/
def meanVec {n : ℕ} (p : Spin n → ℝ) : Fin n → ℝ :=
  fun i => lawMean p fun x => spinValue (x i)

/-- The open solid cube `(−1, 1)^n`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := {m | ∀ i, |m i| < 1}

/-- `D(m) = diag(1 / (1 − m_i²))` (Definition 2.2). -/
def Dmat {n : ℕ} (m : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => (1 - m i ^ 2)⁻¹

/-- `D(m)⁻¹ = diag(1 − m_i²)`. -/
def Dinv {n : ℕ} (m : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => 1 - m i ^ 2

/-- The **TAP Hessian** (2.2):
`∇²_m F_TAP(m) = −βA + diag(1/(1−m²)) + β²(1 − ‖m‖₂²/n) I_n − (2β²/n) m mᵀ`.
It is the Hessian in `m` of the TAP free energy (2.1) and does not depend on `y`. -/
def tapHess {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  -(β • A) + Dmat m + (β ^ 2 * (1 - (∑ i, m i ^ 2) / n)) • (1 : Matrix (Fin n) (Fin n) ℝ)
    - (2 * β ^ 2 / n) • Matrix.vecMulVec m m

/-- `Q̂(m) = (∇²_m F_TAP(m))⁻¹` (2.2). The paper defines it where the Hessian is positive
definite; elsewhere this is Mathlib's matrix inverse (zero for a singular matrix). -/
def Qhat {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (tapHess β A m)⁻¹

/-- The **safe set** `S_{β,A}(c) = {m ∈ (−1,1)^n : c D(m) ≺ ∇² F_TAP(m)}` (Definition 2.2). -/
def safeSet {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) : Set (Fin n → ℝ) :=
  {m | m ∈ cube n ∧ (tapHess β A m - c • Dmat m).PosDef}

/-- `B_□(x, r) = {u ∈ (−1,1)^n : ‖u − x‖₂ < r}`: the `ℓ₂` ball inside the cube (p. 5). -/
def cubeBall {n : ℕ} (x : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℝ) :=
  {u | u ∈ cube n ∧ l2 (u - x) < r}

/-- The drift correction (2.4), (6.2):
`f(m) = (E_{D_n}[Q̂(m)²] D(m)² − (β²/n)(Tr[Q̂(m)²] I_n + 2 Q̂(m)²)) m`. -/
def fDrift {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ) : Fin n → ℝ :=
  (diagPart (Qhat β A m ^ 2) * Dmat m ^ 2
      - (β ^ 2 / n) • ((Qhat β A m ^ 2).trace • (1 : Matrix (Fin n) (Fin n) ℝ)
          + (2 : ℝ) • Qhat β A m ^ 2)).mulVec m

/-- The Jarzynski weight integrand `ω(m) = ½(Tr[Q̂(m)] + ‖m‖₂²)` ((d5), (JE)). -/
def omega {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ((Qhat β A m).trace + ∑ i, m i ^ 2)

/-- `a I_n − βA + D` at the TAP value `a = β² tr_n(D⁻¹)`, for `D = diag(d)` ((5.36), (6.4)). -/
def resolventArg {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (β ^ 2 * ((∑ i, (d i)⁻¹) / n)) • (1 : Matrix (Fin n) (Fin n) ℝ) - β • A + Matrix.diagonal d

/-- The diagonal error of (5.36), for `D = diag(d)`:
`‖E_{D_n}[D (β² tr_n(D⁻¹) I_n − βA + D)⁻² D] − I_n / (1 − β² tr_n(D⁻²))‖_{L²}`. -/
def diagError {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) : ℝ :=
  schatten2
    (diagPart (Matrix.diagonal d * (resolventArg β A d)⁻¹ ^ 2 * Matrix.diagonal d)
      - (1 - β ^ 2 * ((∑ i, ((d i)⁻¹) ^ 2) / n))⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ))

/-- The spectral cutoff (6.3): `γ_Y = min{(1−β)⁴ / (4(1+2β²)²), (1 + (1+3β)/c)⁻²}`. -/
def gammaY (β c : ℝ) : ℝ :=
  min ((1 - β) ^ 4 / (4 * (1 + 2 * β ^ 2) ^ 2)) (((1 + (1 + 3 * β) / c) ^ 2)⁻¹)

/-- `S_D = {D ∈ D_n([1,∞)) : β² tr_n(D⁻¹) I_n − βA + D ⪰ c I_n}` (6.4), as a set of diagonals. -/
def SD {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) : Set (Fin n → ℝ) :=
  {d | (∀ i, 1 ≤ d i) ∧
    (resolventArg β A d - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef}

/-- The event `Ω_{β,c}` of (6.5), with the universal constant of Corollary 5.9 named `C`:
for every `D ∈ S_D`, the diagonal error (5.36) is at most `C β / (γ_Y² √n)`. -/
def OmegaEvent (β c C : ℝ) (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | ∀ d ∈ SD β A c, diagError β A d ≤ C * β / (gammaY β c ^ 2 * Real.sqrt n)}

end

end SKHessianAscent


