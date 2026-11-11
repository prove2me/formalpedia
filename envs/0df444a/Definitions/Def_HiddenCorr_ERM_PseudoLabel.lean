-- Prove2me | Definitions.Def_HiddenCorr_ERM_PseudoLabel
-- name    : HiddenCorr_ERM_PseudoLabel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:35:20.330559+00:00
-- url     : https://prove2.me/theorems/f80cb76f-0c05-4a19-a5cf-8a645e8924df
-- title:
--   Optimal weights $w^\star$, pseudo-labels $\tilde Y=T_GY$, pseudo-label risks $\hat L_G$, the covariance estimator $Z_f(w)$, the sample model and the risks
-- statement:
--   Fix a candidate graph $G$ with Laplacian $L$, incidence matrix $B$ and demand vector $u$.
--
--   **Optimal weights** (Eq. (11)): $w^\star=B^\top L^\dagger u/(u^\top L^\dagger u)\in\mathbb R^m$, computed from $G$ alone. For $w\in\mathbb R^m$, $A(w)\in\mathbb R^{n\times n}$ has entry $w_e$ at $e=(i,j)\in E$ and $0$ elsewhere.
--
--   **Pseudo-labels** (Eq. (34)). With $A=A(w^\star)$, $J=\mathbf 1_n\mathbf 1_n^\top/n$ and $\Pi=I_n-J$,
--   $$T_G=J+n\,\Pi A\Pi,\qquad \tilde Y=T_GY,$$
--   for the observed label vector $Y=(Y_1,\dots,Y_n)^\top$. Pseudo-labels are not clipped. For one-hot labels, $Q\in\mathbb R^{n\times k}$ has rows $Y_j^\top$, and $\tilde Q=T_GQ$ has rows $\tilde q_i^\top$ (Eq. (45)).
--
--   **Pseudo-label risks.** For the scalar affine loss $\ell(z,y)=f_1(z)+y f_2(z)$, $\hat L_G(h)=\frac1n\sum_i\big[f_1(h(X_i))+\tilde Y_i f_2(h(X_i))\big]$ (Eq. (35)); for binary classification, $f_1(z)=z$, $f_2(z)=1-2z$ gives $\hat L_G(h)=\frac1n\sum_i[h(X_i)+(1-2h(X_i))\tilde Y_i]$ (Eq. (42)). For the vector affine loss $\ell(z,y)=f_1(z)+\langle f_2(z),y\rangle$, $\hat L_G(h)=\frac1n\sum_i[f_1(h(X_i))+\langle f_2(h(X_i)),\tilde q_i\rangle]$ (Eq. (46)); the multiclass 0-1 loss is $f_1=1$, $f_2(z)=-z$ with $z=e_{h(x)}$.
--
--   **Covariance estimator** (Eqs. (22), (30)): $Z_f(w)=\sum_{(i,j)\in E}w_{(i,j)}(f(X_i)-\hat\mu_f)(Y_j-\hat\mu_Y)$, with the sample means $\hat\mu_f=\frac1n\sum_i f(X_i)$, $\hat\mu_Y=\frac1n\sum_j Y_j$.
--
--   **Sample model** (§4.1, data-independent graphs). The true pairs $s_1,\dots,s_n\in\mathcal X\times\mathcal Y$ are i.i.d. from $D$. Under the hidden matching $\sigma$ the learner observes $X_i=(s_i)_1$ and $Y_j=(s_{\sigma^{-1}(j)})_2$, so $(X_i,Y_{\sigma(i)})=s_i$; it does not observe $\sigma$.
--
--   **Risks.** The 0-1 risk $L(h)=\Pr_{(X,Y)\sim D}(h(X)\ne Y)$; the affine risks $L(h)=\mathbb E[f_1(h(X))+Yf_2(h(X))]$ and $L(h)=\mathbb E[f_1(h(X))+\langle f_2(h(X)),e_Y\rangle]$.
--
--   **Formalization Note.** `wStar E` is the vector `(incidence E)ᵀ *ᵥ (pinvMat (laplacian E) *ᵥ demand n)` divided by `neff E`. `pseudoRisk01` and `pseudoRiskMulti01` are the 0-1 instances of `pseudoRisk` and `pseudoRiskVec`, with binary values through `b2r` and one-hot vectors through `onehot`. One-hot labels are stored as `Fin k`, and $\langle f_2(z),e_y\rangle$ is the coordinate `f₂ z y`. `obsX`, `obsY σ` are the observation maps of the sample model. `risk01 D h = (D {p | h p.1 ≠ p.2}).toReal`.
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 9, Eq. (11); p. 16, Eq. (22); p. 23, Eq. (30); pp. 24–25, Eqs. (33)–(36); p. 28, Eq. (42); p. 30, Eqs. (45)–(47); pp. 13–14, §4.1

import Mathlib
import Definitions.Def_IncrementalER_energy
import Definitions.Def_HiddenCorr_ERM_CandidateGraph
import Definitions.Def_HiddenCorr_ERM_Complexity

open Matrix MeasureTheory

namespace HiddenCorr.ERM

/-!
# Optimal weights, pseudo-labels, pseudo-label risks, the sample model and the risks

Chen, Gentile, Kaplan, Koren, *Supervised Learning with Hidden Correspondences*, STOC 2027
submission (manuscript sha256 d0029978…), Eq. (11) (p. 9), Eq. (22) (p. 16), Eq. (30) (p. 23),
Eqs. (33)–(36) (pp. 24–25), Eq. (42) (p. 28), Eqs. (45)–(47) (p. 30), §4.1 (pp. 13–14).

* `wStar E = Bᵀ L† u / (uᵀ L† u)` (Eq. (11)), computed from the graph alone.
* `weightMatrix E w = A(w)`: entry `w_e` at `e = (i, j) ∈ E`, zero elsewhere.
* `T_G = J + n Π A(w⋆) Π` with `J = 1ₙ1ₙᵀ/n`, `Π = Iₙ − J` (Eq. (34)); scalar pseudo-labels
  `Ỹ = T_G Y`, vector pseudo-labels `Q̃ = T_G Q` with `Q` the one-hot label matrix (Eq. (45)).
  Pseudo-labels are not clipped.
* `pseudoRisk`: `L̂_G(h) = (1/n) ∑ᵢ [f₁(h(Xᵢ)) + Ỹᵢ f₂(h(Xᵢ))]` (Eq. (35)); `pseudoRisk01` its
  0-1 instance `f₁(z) = z`, `f₂(z) = 1 − 2z` on `{0, 1}` (Eq. (42)).
* `pseudoRiskVec`: `L̂_G(h) = (1/n) ∑ᵢ [f₁(h(Xᵢ)) + ⟨f₂(h(Xᵢ)), q̃ᵢ⟩]` (Eq. (46));
  `pseudoRiskMulti01` its multiclass 0-1 instance `f₁ = 1`, `f₂(z) = −z`, `z = e_{h(x)}` (p. 31).
* `covEst`: `Z_f(w) = ∑_{(i,j) ∈ E} w_{(i,j)} (f(Xᵢ) − μ̂_f)(Yⱼ − μ̂_Y)` (Eqs. (22), (30)).
* Sample model (§4.1, data-independent graphs): the true pairs `s₁, …, sₙ ∈ X × Y` are i.i.d.
  from `D` (`Measure.pi`); with hidden matching `σ`, the learner observes the inputs `Xᵢ = (sᵢ).1`
  and the labels `Yⱼ = (s_{σ⁻¹(j)}).2`, so that `(Xᵢ, Y_{σ(i)}) = sᵢ`. It does not observe `σ`.
-/

/-- The optimal weights `w⋆ = Bᵀ L† u / (uᵀ L† u)` (Eq. (11), p. 9), one per edge. -/
noncomputable def wStar {n : ℕ} (E : Finset (Fin n × Fin n)) : E → ℝ :=
  fun e => ((incidence E)ᵀ *ᵥ (IncrementalER.pinvMat (laplacian E) *ᵥ demand n)) e / neff E

/-- The matrix `A(w) ∈ ℝ^{n×n}` with entry `w_e` at `e = (i, j) ∈ E` and zero otherwise. -/
def weightMatrix {n : ℕ} (E : Finset (Fin n × Fin n)) (w : E → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if h : (i, j) ∈ E then w ⟨(i, j), h⟩ else 0

/-- The averaging matrix `J = 1ₙ 1ₙᵀ / n`. -/
noncomputable def avgMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun _ _ => (1 : ℝ) / n

/-- The centering projection `Π = Iₙ − J`. -/
noncomputable def centerMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - avgMat n

/-- The pseudo-label transform `T_G = J + n Π A(w⋆) Π` of Eq. (34), p. 25. -/
noncomputable def pseudoTransform {n : ℕ} (E : Finset (Fin n × Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  avgMat n + (n : ℝ) • (centerMat n * weightMatrix E (wStar E) * centerMat n)

/-- The scalar pseudo-labels `Ỹ = T_G Y` of Eq. (34), from the observed labels `Y = (Y₁, …, Yₙ)`. -/
noncomputable def pseudoLabels {n : ℕ} (E : Finset (Fin n × Fin n)) (Y : Fin n → ℝ) :
    Fin n → ℝ :=
  pseudoTransform E *ᵥ Y

/-- The pseudo-label empirical risk of Eq. (35), p. 25, for the affine loss
`ℓ(z, y) = f₁(z) + y f₂(z)`: `L̂_G(h) = (1/n) ∑ᵢ [f₁(h(Xᵢ)) + Ỹᵢ f₂(h(Xᵢ))]`. -/
noncomputable def pseudoRisk {𝒳 : Type*} {n : ℕ} (E : Finset (Fin n × Fin n)) (f₁ f₂ : ℝ → ℝ)
    (h : 𝒳 → ℝ) (X : Fin n → 𝒳) (Y : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (f₁ (h (X i)) + pseudoLabels E Y i * f₂ (h (X i)))

/-- The binary 0-1 pseudo-label risk of Eq. (42), p. 28: `pseudoRisk` with `f₁(z) = z`,
`f₂(z) = 1 − 2z`, hypotheses and labels in `{0, 1}` (encoded by `Bool`):
`L̂_G(h) = (1/n) ∑ᵢ [h(Xᵢ) + (1 − 2h(Xᵢ)) Ỹᵢ]`. -/
noncomputable def pseudoRisk01 {𝒳 : Type*} {n : ℕ} (E : Finset (Fin n × Fin n))
    (h : 𝒳 → Bool) (X : Fin n → 𝒳) (Y : Fin n → Bool) : ℝ :=
  pseudoRisk E (fun z => z) (fun z => 1 - 2 * z) (fun x => b2r (h x)) X (fun j => b2r (Y j))

/-- The one-hot label matrix `Q ∈ ℝ^{n×k}` with rows `Yⱼᵀ = e_{Yⱼ}ᵀ`. -/
def labelMatrix {n k : ℕ} (Y : Fin n → Fin k) : Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun j r => if Y j = r then 1 else 0

/-- The vector pseudo-labels `Q̃ = T_G Q` of Eq. (45), p. 30; row `i` is `q̃ᵢᵀ`. -/
noncomputable def pseudoLabelMatrix {n k : ℕ} (E : Finset (Fin n × Fin n)) (Y : Fin n → Fin k) :
    Matrix (Fin n) (Fin k) ℝ :=
  pseudoTransform E * labelMatrix Y

/-- The multiclass pseudo-label empirical risk of Eq. (46), p. 30, for the affine loss
`ℓ(z, y) = f₁(z) + ⟨f₂(z), y⟩`: `L̂_G(h) = (1/n) ∑ᵢ [f₁(h(Xᵢ)) + ⟨f₂(h(Xᵢ)), q̃ᵢ⟩]`. -/
noncomputable def pseudoRiskVec {𝒳 : Type*} {n k : ℕ} (E : Finset (Fin n × Fin n))
    (f₁ : EuclideanSpace ℝ (Fin k) → ℝ)
    (f₂ : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (h : 𝒳 → EuclideanSpace ℝ (Fin k)) (X : Fin n → 𝒳) (Y : Fin n → Fin k) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (f₁ (h (X i)) + ∑ r, f₂ (h (X i)) r * pseudoLabelMatrix E Y i r)

/-- The multiclass 0-1 pseudo-label risk (p. 31): `pseudoRiskVec` with `f₁(z) = 1`, `f₂(z) = −z`
and the one-hot predictor `x ↦ e_{h(x)}`; it equals `1 − (1/n) ∑ᵢ q̃_{i, h(Xᵢ)}`. -/
noncomputable def pseudoRiskMulti01 {𝒳 : Type*} {n k : ℕ} (E : Finset (Fin n × Fin n))
    (h : 𝒳 → Fin k) (X : Fin n → 𝒳) (Y : Fin n → Fin k) : ℝ :=
  pseudoRiskVec E (fun _ => 1) (fun z => -z) (fun x => onehot (h x)) X Y

/-- The sample mean `μ̂ = (1/n) ∑ᵢ aᵢ`. -/
noncomputable def sampleMean {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, a i

/-- The covariance estimator of Eqs. (22) and (30):
`Z(w) = ∑_{(i,j) ∈ E} w_{(i,j)} (aᵢ − μ̂_a)(Yⱼ − μ̂_Y)`, with `aᵢ = f(Xᵢ)` for `Z_f(w)`. -/
noncomputable def covEst {n : ℕ} (E : Finset (Fin n × Fin n)) (w : E → ℝ) (a Y : Fin n → ℝ) :
    ℝ :=
  ∑ e : E, w e * (a e.1.1 - sampleMean a) * (Y e.1.2 - sampleMean Y)

/-- The observed inputs `Xᵢ = (sᵢ).1` of the paired sample `s`. -/
def obsX {𝒳 𝒴 : Type*} {n : ℕ} (s : Fin n → 𝒳 × 𝒴) : Fin n → 𝒳 :=
  fun i => (s i).1

/-- The observed labels `Yⱼ = (s_{σ⁻¹(j)}).2` under the hidden matching `σ`, so that
`(Xᵢ, Y_{σ(i)}) = sᵢ` are the true pairs. -/
def obsY {𝒳 𝒴 : Type*} {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Fin n → 𝒳 × 𝒴) : Fin n → 𝒴 :=
  fun j => (s (σ.symm j)).2

/-- The 0-1 risk `L(h) = Pr_{(X, Y) ∼ D}(h(X) ≠ Y)` (p. 4), as a real number. -/
noncomputable def risk01 {𝒳 𝒴 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (D : Measure (𝒳 × 𝒴)) (h : 𝒳 → 𝒴) : ℝ :=
  (D {p | h p.1 ≠ p.2}).toReal

/-- The risk `L(h) = E_{(X,Y) ∼ D}[f₁(h(X)) + Y f₂(h(X))]` of the scalar affine loss of Eq. (33). -/
noncomputable def riskAffine {𝒳 : Type*} [MeasurableSpace 𝒳] (D : Measure (𝒳 × ℝ))
    (f₁ f₂ : ℝ → ℝ) (h : 𝒳 → ℝ) : ℝ :=
  ∫ p, (f₁ (h p.1) + p.2 * f₂ (h p.1)) ∂D

/-- The risk `L(h) = E_{(X,Y) ∼ D}[f₁(h(X)) + ⟨f₂(h(X)), e_Y⟩]` of the vector affine loss of §6.6
(p. 29) with one-hot labels `e_Y`, `Y ∈ [k]`; `⟨f₂(z), e_y⟩ = f₂(z)_y`. -/
noncomputable def riskAffineVec {𝒳 : Type*} [MeasurableSpace 𝒳] {k : ℕ}
    (D : Measure (𝒳 × Fin k)) (f₁ : EuclideanSpace ℝ (Fin k) → ℝ)
    (f₂ : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (h : 𝒳 → EuclideanSpace ℝ (Fin k)) : ℝ :=
  ∫ p, (f₁ (h p.1) + f₂ (h p.1) p.2) ∂D

end HiddenCorr.ERM


