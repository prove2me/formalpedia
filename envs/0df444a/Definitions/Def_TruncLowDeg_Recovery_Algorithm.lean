-- Prove2me | Definitions.Def_TruncLowDeg_Recovery_Algorithm
-- name    : TruncLowDeg_Recovery_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:24:29.43862+00:00
-- url     : https://prove2.me/theorems/a051ced7-4622-4885-a022-280105bca645
-- title:
--   Algorithm 1 (parameter recovery for truncated Gaussians) as a relation, system (14), condition (15) and the good event
-- statement:
--   **Algorithm 1** (p. 26) receives $n$ samples $X_1,\dots,X_n\in\mathbb R^d$ and the parameters $\alpha_0,k,\varepsilon,\delta$. Its implicit constants are explicit natural parameters $c=(c_{pre},c_\rho,c_\eta,c_q,c_r)$:
--
--   1. The **preliminary batch** $\hat{\mathcal D}_{pre}$ is the first $n_{pre}=\lceil c_{pre}d^4/(\alpha_0^{11}\delta)\rceil$ samples and $\hat{\mathcal D}_{rec}$ the rest.
--   2. $\hat\mu_{pre}$ and $\hat\Sigma_{pre}=\frac1m\sum(x-\hat\mu_{pre})(x-\hat\mu_{pre})^\top$ are the sample mean and covariance of the batch. A matrix $W$ **whitens** $\hat\Sigma_{pre}$ if $W\hat\Sigma_{pre}W^\top=I$; the paper's choice is $W=\hat\Sigma_{pre}^{-1/2}$. Then $T(x)=W(x-\hat\mu_{pre})$.
--   3. $\rho=c_\rho\sqrt d/\alpha_0^2$, $U=\mathrm{Unif}([-\rho,\rho]^d)$, and $\hat{\mathcal D}$ is the list of $T(x)$, $x\in\hat{\mathcal D}_{rec}$, with $\|T(x)\|_2\le\rho$. If $|\hat{\mathcal D}|<|\hat{\mathcal D}_{rec}|/4$ the algorithm returns Fail.
--   4. $\eta=\varepsilon(\alpha_0/d)^{c_\eta k}$. For each coordinate $j$ it chooses any $(p_j,q_j)\in\mathbb R[x]_{\le3k}\times\mathbb R[x]_{\le4k}$ solving **system (14)**:
--   $$\|p_j\|_{L^2(U)}=1,\quad \|q_j\|_{L^2(U)}\le(d/\alpha_0)^{c_qk},\quad \big|\mathbb E_{\hat{\mathcal D}}[fq_j-\partial_j(fp_j)]\big|\le\eta\,(d/\alpha_0)^{c_rk}\,\|f\|_{L^2(U)}\ \ \forall f\in\mathbb R[x]_{\le10k},$$
--   returning Fail if some coordinate has none, and any $\hat s_j\in\arg\min_{r\in\mathbb R[x]_{\le1}}\|p_jr-q_j\|_{L^2(U)}$, $\hat s_j(x)=\hat s_j^0+\sum_i\hat s_j^ix_i$.
--   5. $\tilde A_{ji}=\hat s_j^i$, $b_j=-\hat s_j^0$, $A=(\tilde A+\tilde A^\top)/2$. If $A\not\succ0$ it returns Fail; otherwise $\hat\Sigma=A^{-1}$, $\hat\mu=\hat\Sigma b$, and it returns $\hat\mu_0=\hat\mu_{pre}+W^{-1}\hat\mu$, $\hat\Sigma_0=W^{-1}\hat\Sigma W^{-\top}$ (for $W=\hat\Sigma_{pre}^{-1/2}$: $\hat\mu_{pre}+\hat\Sigma_{pre}^{1/2}\hat\mu$ and $\hat\Sigma_{pre}^{1/2}\hat\Sigma\hat\Sigma_{pre}^{1/2}$).
--
--   `Alg1Output c d k α₀ ε δ X W out` holds when `out` is an output Algorithm 1 can return over all admissible choices in steps 4 (`none` is Fail). The analysis uses: the conclusions of Lemma 5.4 with a constant $C$ (`PrecondOK`: $\Sigma\succ0$, $\|\Sigma^{-1/2}\mu\|_2\le C\sqrt{\log(1/\alpha_0)}$, $(\alpha_0^2/C)I\preceq\Sigma\preceq(C/\alpha_0^2)I$); **the preconditioning succeeds** (`Success`: those conclusions, $\mathcal N(\mu,\Sigma)(S)\ge\alpha_0/2$ and $\mathrm{BVD}(S)\le3k$); **condition (15)**: $|\mathbb E_{\hat{\mathcal D}}[f]-\mathbb E_{\mathcal N(\mu,\Sigma)|_S}[f]|\le\eta\|f\|_{L^2(U)}$ for all $f\in\mathbb R[x]_{\le14k}$; the transformed parameters $\mu=W(\mu_0-\hat\mu_{pre})$, $\Sigma=W\Sigma_0W^\top$, $S=T(S_0)\cap\{\|x\|_2\le\rho\}$; and the **good event** `Good`: the preconditioning works, $|\hat{\mathcal D}|\ge|\hat{\mathcal D}_{rec}|/4$, and (15) holds.
--
--   **Formalization Note.** The supremum in (14) is multiplied out (equivalent, since $\|f\|_{L^2(U)}>0$ for $f\ne0$). The batch size dominates the $\tilde O(d^3\alpha_0^{-10}\log^2(2/\delta))$ that Lemma 5.4 requires for large $c_{pre}$ and is computable without logarithms. The whitening $W$ is a parameter; the paper's algorithm is $W=\hat\Sigma_{pre}^{-1/2}$. When $\hat\Sigma_{pre}$ is singular no $W$ whitens it and the relation is empty (the paper's $T$ is undefined there). The sample covariance is normalized by $1/m$.
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 26, Algorithm 1 and system (14); p. 27, Lemma 6.2, Lemma 6.3 and condition (15); p. 21, Lemma 5.4

import Definitions.Def_TruncLowDeg_Recovery_Basic

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-!
# Algorithm 1 (parameter recovery for truncated Gaussians) as a relation, system (14), and the
events of its analysis

Vári-Kakas, Wiedmer, *A General Approach to Polynomial-Time Truncated Learning via Low-Degree
Moments*, STOC 2027 submission (manuscript sha256 613f0e39…): p. 26 Algorithm 1 and system (14);
p. 27 Lemma 6.2, Lemma 6.3 and condition (15); p. 21 Lemma 5.4 (the conclusions on `µ`, `Σ`).

* The implicit constants of Algorithm 1 (batch size, `ρ = O(√d/α₀²)`, `η = ε·(α₀/d)^{O(k)}` and
  the two `(d/α₀)^{O(k)}` bounds of (14)) are explicit natural-number parameters `Consts`.
* The input is the list `X` of the `n` samples. The preliminary batch is its first
  `nPre` entries, the recovery samples the rest.
* Line 4's map `T(x) = Σ̂_pre^{−1/2}(x − µ̂_pre)` is taken with a **whitening matrix** `W` of
  `Σ̂_pre` (`W Σ̂_pre Wᵀ = I`), and line 14's `Σ̂_pre^{1/2}` with `W⁻¹`. The paper's choice is
  `W = Σ̂_pre^{−1/2}` (then `W⁻¹ = Σ̂_pre^{1/2}`); every other whitening is `QΣ̂_pre^{−1/2}`
  for an orthogonal `Q`.
* The relation `Alg1Output` lists every output Algorithm 1 can produce over all admissible
  choices in lines 9 and 11.
* The sample covariance is normalized by `1/m` (`m` the batch size).
-/

/-- The implicit constants of Algorithm 1 and of system (14), as explicit naturals:
`pre` (preliminary batch size), `rho` (`ρ`), `eta` (exponent in `η`), `q` and `r` (the two
`(d/α₀)^{O(k)}` bounds in (14)). -/
structure Consts where
  /-- batch-size constant (line 3) -/
  pre : ℕ
  /-- `ρ = rho · √d / α₀²` (line 5) -/
  rho : ℕ
  /-- `η = ε · (α₀/d)^{eta · k}` (line 7) -/
  eta : ℕ
  /-- `‖q_j‖_{L²(U)} ≤ (d/α₀)^{q · k}` in (14) -/
  q : ℕ
  /-- residual bound `η · (d/α₀)^{r · k}` in (14) -/
  r : ℕ

/-- Size of the preliminary batch (line 3): `⌈pre · d⁴ / (α₀¹¹ δ)⌉`. It dominates the size
`Õ(d³/α₀¹⁰ · log²(2/δ))` that Lemma 5.4 requires for failure probability `δ/2` once `pre` is
large, and is computable with field operations and comparisons only. -/
noncomputable def nPre (c : Consts) (d : ℕ) (α₀ δ : ℝ) : ℕ :=
  ⌈(c.pre : ℝ) * (d : ℝ) ^ 4 / (α₀ ^ 11 * δ)⌉₊

/-- The preliminary batch `𝒟̂_pre` (the first `nPre` samples). -/
noncomputable def batch (c : Consts) {d : ℕ} (α₀ δ : ℝ) (X : List (Vec d)) : List (Vec d) :=
  X.take (nPre c d α₀ δ)

/-- The recovery samples `𝒟̂_rec` (the remaining samples). -/
noncomputable def recov (c : Consts) {d : ℕ} (α₀ δ : ℝ) (X : List (Vec d)) : List (Vec d) :=
  X.drop (nPre c d α₀ δ)

/-- Sample mean `µ̂ = (1/m) ∑ x`. -/
noncomputable def empMean {d : ℕ} (D : List (Vec d)) : Vec d :=
  (D.length : ℝ)⁻¹ • D.sum

/-- Sample covariance `Σ̂ = (1/m) ∑ (x − µ̂)(x − µ̂)ᵀ` (normalization `1/m`). -/
noncomputable def empCov {d : ℕ} (D : List (Vec d)) : Mat d :=
  Matrix.of fun i j =>
    (D.map fun x => (x i - empMean D i) * (x j - empMean D j)).sum / D.length

/-- `W` whitens `M`: `W M Wᵀ = I`. -/
def IsWhitening {d : ℕ} (M W : Mat d) : Prop := W * M * W.transpose = 1

/-- The affine map `T(x) = W(x − m)`. -/
noncomputable def Tmap {d : ℕ} (m : Vec d) (W : Mat d) (x : Vec d) : Vec d := mulV W (x - m)

/-- `ρ = rho · √d / α₀²` (line 5). -/
noncomputable def rhoV (c : Consts) (d : ℕ) (α₀ : ℝ) : ℝ := c.rho * Real.sqrt d / α₀ ^ 2

/-- `η = ε · (α₀/d)^{eta · k}` (line 7). -/
noncomputable def etaV (c : Consts) (d k : ℕ) (α₀ ε : ℝ) : ℝ := ε * (α₀ / d) ^ (c.eta * k)

/-- The transformed, clipped recovery set `𝒟̂ = {T(x) : x ∈ 𝒟̂_rec, ‖T(x)‖₂ ≤ ρ}` (lines 4, 6),
in the order of the samples. -/
noncomputable def Dhat (c : Consts) {d : ℕ} (α₀ δ : ℝ) (X : List (Vec d)) (W : Mat d) :
    List (Vec d) :=
  ((recov c α₀ δ X).map (Tmap (empMean (batch c α₀ δ X)) W)).filter
    fun x => decide (‖x‖ ≤ rhoV c d α₀)

/-- System (14) for coordinate `j` (line 9): `(p, q) ∈ ℝ[x]_{≤3k} × ℝ[x]_{≤4k}` with
`‖p‖_{L²(U)} = 1`, `‖q‖_{L²(U)} ≤ (d/α₀)^{cq·k}`, and
`|E_𝒟̂[f q − ∂_j(f p)]| ≤ η · (d/α₀)^{cr·k} · ‖f‖_{L²(U)}` for every `f ∈ ℝ[x]_{≤10k}`
(the supremum over `f ≠ 0` of the ratio, multiplied out). -/
def Solves14 {d : ℕ} (k : ℕ) (α₀ ρ η : ℝ) (cq cr : ℕ) (D : List (Vec d)) (j : Fin d)
    (p q : MvPolynomial (Fin d) ℝ) : Prop :=
  p.totalDegree ≤ 3 * k ∧ q.totalDegree ≤ 4 * k ∧ L2U ρ p = 1 ∧
    L2U ρ q ≤ ((d : ℝ) / α₀) ^ (cq * k) ∧
    ∀ f : MvPolynomial (Fin d) ℝ, f.totalDegree ≤ 10 * k →
      |empAvg D (peval (f * q - MvPolynomial.pderiv j (f * p)))| ≤
        η * ((d : ℝ) / α₀) ^ (cr * k) * L2U ρ f

/-- `s ∈ argmin_{r ∈ ℝ[x]_{≤1}} ‖p r − q‖_{L²(U)}` (line 11). -/
def IsLSFit {d : ℕ} (ρ : ℝ) (p q s : MvPolynomial (Fin d) ℝ) : Prop :=
  s.totalDegree ≤ 1 ∧
    ∀ r : MvPolynomial (Fin d) ℝ, r.totalDegree ≤ 1 → L2U ρ (p * s - q) ≤ L2U ρ (p * r - q)

/-- Constant coefficient `ŝ⁰` of an affine polynomial. -/
noncomputable def coef0 {d : ℕ} (s : MvPolynomial (Fin d) ℝ) : ℝ := MvPolynomial.coeff 0 s

/-- Coefficient `ŝⁱ` of `x_i` in an affine polynomial. -/
noncomputable def coefX {d : ℕ} (s : MvPolynomial (Fin d) ℝ) (i : Fin d) : ℝ :=
  MvPolynomial.coeff (Finsupp.single i 1) s

/-- Line 13: `Ã_{ji} = ŝ_jⁱ`, `A = (Ã + Ãᵀ)/2`. -/
noncomputable def symA {d : ℕ} (s : Fin d → MvPolynomial (Fin d) ℝ) : Mat d :=
  (1 / 2 : ℝ) • (Matrix.of (fun j i => coefX (s j) i) +
    (Matrix.of (fun j i => coefX (s j) i)).transpose)

/-- Line 13: `b_j = −ŝ_j⁰`. -/
noncomputable def vecB {d : ℕ} (s : Fin d → MvPolynomial (Fin d) ℝ) : Vec d :=
  WithLp.toLp 2 (fun j => -coef0 (s j))

/-- **Algorithm 1** (p. 26) as a relation: `out` is an output Algorithm 1 can return on the
sample list `X` with parameters `(d, k, α₀, ε, δ)`, constants `c`, and whitening `W` of
`Σ̂_pre` in line 4, over all admissible choices in lines 9 and 11. `none` is `Fail`;
`some (µ̂₀, Σ̂₀)` is the returned pair (line 14: `µ̂₀ = µ̂_pre + W⁻¹µ̂`,
`Σ̂₀ = W⁻¹ Σ̂ W⁻ᵀ`, which for `W = Σ̂_pre^{−1/2}` is `µ̂_pre + Σ̂_pre^{1/2}µ̂`,
`Σ̂_pre^{1/2} Σ̂ Σ̂_pre^{1/2}`). -/
def Alg1Output (c : Consts) (d k : ℕ) (α₀ ε δ : ℝ) (X : List (Vec d)) (W : Mat d)
    (out : Option (Vec d × Mat d)) : Prop :=
  IsWhitening (empCov (batch c α₀ δ X)) W ∧
    ((4 * (Dhat c α₀ δ X W).length < (recov c α₀ δ X).length ∧ out = none) ∨
     ((recov c α₀ δ X).length ≤ 4 * (Dhat c α₀ δ X W).length ∧
        (∃ j : Fin d, ∀ p q : MvPolynomial (Fin d) ℝ,
          ¬ Solves14 k α₀ (rhoV c d α₀) (etaV c d k α₀ ε) c.q c.r (Dhat c α₀ δ X W) j p q) ∧
        out = none) ∨
     ((recov c α₀ δ X).length ≤ 4 * (Dhat c α₀ δ X W).length ∧
        ∃ p q s : Fin d → MvPolynomial (Fin d) ℝ,
          (∀ j, Solves14 k α₀ (rhoV c d α₀) (etaV c d k α₀ ε) c.q c.r (Dhat c α₀ δ X W) j
            (p j) (q j)) ∧
          (∀ j, IsLSFit (rhoV c d α₀) (p j) (q j) (s j)) ∧
          ((¬ (symA s).PosDef ∧ out = none) ∨
           ((symA s).PosDef ∧
             out = some (empMean (batch c α₀ δ X) + mulV W⁻¹ (mulV (symA s)⁻¹ (vecB s)),
               W⁻¹ * (symA s)⁻¹ * (W⁻¹).transpose)))))

/-- The conclusions of Lemma 5.4 on `(µ, Σ)` with the single constant `C` standing for its
`O(·)` and `Ω(·)`: `Σ ≻ 0`, `‖Σ^{−1/2}µ‖₂ ≤ C √log(1/α₀)` and
`(α₀²/C) I ⪯ Σ ⪯ (C/α₀²) I`. -/
def PrecondOK {d : ℕ} (C α₀ : ℝ) (μ : Vec d) (Sig : Mat d) : Prop :=
  Sig.PosDef ∧ ‖mulV (invSqrt Sig) μ‖ ≤ C * Real.sqrt (Real.log (1 / α₀)) ∧
    LoewnerLE ((α₀ ^ 2 / C) • (1 : Mat d)) Sig ∧ LoewnerLE Sig ((C / α₀ ^ 2) • (1 : Mat d))

/-- "The preconditioning succeeds" (the event of Lemma 6.2): `(µ, Σ)` satisfy the conclusions of
Lemma 5.4 with constant `C`, `N(µ, Σ)(S) ≥ α₀/2` and `BVD(S) ≤ 3k`. -/
def Success {d : ℕ} (C : ℝ) (k : ℕ) (α₀ : ℝ) (μ : Vec d) (Sig : Mat d) (S : Set (Vec d)) :
    Prop :=
  PrecondOK C α₀ μ Sig ∧ ENNReal.ofReal (α₀ / 2) ≤ gaussian μ Sig S ∧ BVD S ≤ ((3 * k : ℕ) : ℕ∞)

/-- Condition (15) (p. 27): `|E_𝒟̂[f] − E_{N(µ,Σ)|S}[f]| ≤ η ‖f‖_{L²(U)}` for all
`f ∈ ℝ[x]_{≤14k}`. -/
def Eq15 {d : ℕ} (k : ℕ) (ρ η : ℝ) (D : List (Vec d)) (μ : Vec d) (Sig : Mat d)
    (S : Set (Vec d)) : Prop :=
  ∀ f : MvPolynomial (Fin d) ℝ, f.totalDegree ≤ 14 * k →
    |empAvg D (peval f) - ∫ x, peval f x ∂(truncGaussian μ Sig S)| ≤ η * L2U ρ f

/-- Transformed mean `µ = W(µ₀ − µ̂_pre)` (Lemma 6.2). -/
noncomputable def muT {d : ℕ} (μ₀ m : Vec d) (W : Mat d) : Vec d := mulV W (μ₀ - m)

/-- Transformed covariance `Σ = W Σ₀ Wᵀ` (Lemma 6.2; `Σ̂_pre^{−1/2} Σ₀ Σ̂_pre^{−1/2}` for the
paper's `W`). -/
def SigT {d : ℕ} (Sig₀ W : Mat d) : Mat d := W * Sig₀ * W.transpose

/-- Transformed clipped set `S = T(S₀) ∩ {x : ‖x‖₂ ≤ ρ}` (Lemma 6.2). -/
def ST {d : ℕ} (S₀ : Set (Vec d)) (m : Vec d) (W : Mat d) (ρ : ℝ) : Set (Vec d) :=
  Tmap m W '' S₀ ∩ Metric.closedBall 0 ρ

/-- The preconditioning works (Lemma 6.2's event) for the batch of `X` and the whitening `W`:
`Σ̂_pre ≻ 0`, `W` whitens `Σ̂_pre`, and `Success` holds for the transformed parameters and the
clipped set. -/
def PrecondWorks (c : Consts) (C : ℝ) (d k : ℕ) (α₀ δ : ℝ) (μ₀ : Vec d) (Sig₀ : Mat d)
    (S₀ : Set (Vec d)) (X : List (Vec d)) (W : Mat d) : Prop :=
  (empCov (batch c α₀ δ X)).PosDef ∧ IsWhitening (empCov (batch c α₀ δ X)) W ∧
    Success C k α₀ (muT μ₀ (empMean (batch c α₀ δ X)) W) (SigT Sig₀ W)
      (ST S₀ (empMean (batch c α₀ δ X)) W (rhoV c d α₀))

/-- The good event of Proposition 6.7 and Lemma 6.8: the preconditioning works, the retention
check passes (`|𝒟̂| ≥ |𝒟̂_rec|/4`), and (15) holds for `𝒟̂`. -/
def Good (c : Consts) (C : ℝ) (d k : ℕ) (α₀ ε δ : ℝ) (μ₀ : Vec d) (Sig₀ : Mat d)
    (S₀ : Set (Vec d)) (X : List (Vec d)) (W : Mat d) : Prop :=
  PrecondWorks c C d k α₀ δ μ₀ Sig₀ S₀ X W ∧
    (recov c α₀ δ X).length ≤ 4 * (Dhat c α₀ δ X W).length ∧
    Eq15 k (rhoV c d α₀) (etaV c d k α₀ ε) (Dhat c α₀ δ X W)
      (muT μ₀ (empMean (batch c α₀ δ X)) W) (SigT Sig₀ W)
      (ST S₀ (empMean (batch c α₀ δ X)) W (rhoV c d α₀))

end TruncLowDeg.Recovery


