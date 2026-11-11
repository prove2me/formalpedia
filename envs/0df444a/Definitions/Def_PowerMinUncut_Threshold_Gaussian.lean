-- Prove2me | Definitions.Def_PowerMinUncut_Threshold_Gaussian
-- name    : PowerMinUncut_Threshold_Gaussian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:43:12.084443+00:00
-- url     : https://prove2.me/theorems/b475f2f2-3c0b-4e87-ac26-6f46482d1135
-- title:
--   Normalized Gaussian projection, the ellipse comparison, chi moments a(d,q), b(d,q), Haar q-frames, Gaussian pairs E_C and the ball kernel L_q
-- statement:
--   Write $\mathbb R^n$ with its Euclidean norm and $\gamma_n$ for the standard Gaussian measure; $\mathrm{normalize}(v)=v/\|v\|$.
--
--   *Lemma 6 objects.* For a real $2\times 2$ matrix $A$, $f(\varphi)=A(\cos\varphi,\sin\varphi)/\|A(\cos\varphi,\sin\varphi)\|$, the **normalized chord ratio** $D_t(\varphi)=\|f(\varphi+t/2)-f(\varphi-t/2)\|/(2\sin(t/2))$ and the **angular speed** $P(\varphi)=\|f'(\varphi)\|$; for $\varphi$ uniform modulo $2\pi$, $\mathbb E\,g(\varphi)=\frac1{2\pi}\int_0^{2\pi}g$.
--
--   *Normalized Gaussian projection.* $G$ is a standard Gaussian $k\times N$ matrix (i.i.d. $N(0,1)$ entries) and $\mathrm{projMoment}(k,N,p,u,v)=\mathbb E\,\|Gu/\|Gu\|-Gv/\|Gv\|\|^p$.
--
--   *Chi moments.* For real $d$ and integer $q$,
--   $$a(d,q)=\mathbb E\chi_d^q=2^{q/2}\frac{\Gamma((d+q)/2)}{\Gamma(d/2)},\qquad b(d,q)=\prod_{j=0}^{q-1}\mathbb E\chi_{d-j}=2^{q/2}\frac{\Gamma((d+1)/2)}{\Gamma((d-q+1)/2)}.$$
--
--   *Haar frames.* $J_q(M)=\sqrt{\det(M^{\mathsf T}M)}$ for $M:\mathbb R^q\to\mathbb R^k$ (the square root of the Gram determinant of its columns). A **Haar orthonormal $q$-frame** $Q$ of $\mathbb R^m$ is the Gram–Schmidt orthonormalization of $q$ independent standard Gaussian vectors; $\mathrm{frameJacMean}(q,A)=\mathbb E_Q J_q(AQ)$ and $\mathrm{gaussPowMoment}(q,A)=\mathbb E\|AZ_m\|^q$.
--
--   *Gaussian pairs.* $\mathbb E_C$ is the expectation over standard Gaussian $X,Y\in\mathbb R^n$ with diagonal cross-covariance $\mathbb E XY^{\mathsf T}=\mathrm{diag}(c)$, $|c_i|\le 1$. The **ball kernel** is $L_q(a,b)=[2(1+a\cdot b)]^{q/2}$ and $a_\rho=[2(1-\rho)]^{q/2}$. The **uniform endpoint quantities** are
--   $$\inf_{n\ge k}\ \inf_{f}\ \frac{\mathbb E_{-\rho I_n}\|f(X)+f(Y)\|^q}{[2(1-\rho)]^{q/2}},$$
--   over measurable $f:\mathbb R^n\to S^{k-1}$ (`sphereEndpoint`), and the same with $L_q(f(X),f(Y))$ over measurable maps into the closed unit ball $B^k$ (`ballEndpoint`).
--
--   **Formalization Note.** Gaussian QR: the Gram–Schmidt frame of a Gaussian matrix has the $O(m)$-invariant (Haar) law on the Stiefel manifold. The pair is realized as $Y_i=c_iX_i+\sqrt{1-c_i^2}\,Z_i$ with $Z$ independent of $X$. Infima over sets are `sInf` of nonempty sets bounded below by $0$.
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 2, Theorem 3; p. 5, §2 (a(d,q), b(d,q)); pp. 6–7, §2.3; p. 8, Lemma 6; p. 9, Theorem 7; p. 50, §10.1

import Mathlib

/-!
# Gaussian rounding, the ellipse comparison, chi moments, Haar frames and Gaussian pairs

Xie, *Sharp Power Loss Thresholds for Vector Min Uncut*, STOC 2027 submission (manuscript
sha256 391063da…): p. 2 (Theorem 3, the ball kernel `L_q`), p. 5 (§2, `a(d, q)`, `b(d, q)`),
pp. 6–7 (§2.3, `J_q`, Haar `q`-frames), p. 8 (Lemma 6), p. 9 (Theorem 7), p. 50 (§10.1, `E_C`,
`a_ρ`).

Conventions.
* `E n = EuclideanSpace ℝ (Fin n)`; `γ_n = stdGaussian (E n)` is standard Gaussian measure.
* `normalize v = v / ‖v‖` (it is `0` at `v = 0`, a null event for every law used here).
* A standard Gaussian `k × N` matrix is `G : Fin k → Fin N → ℝ` under the product of standard
  real Gaussians; `matApply G u = Gu`.
* Lemma 6: `f(φ) = A(cos φ, sin φ)/‖A(cos φ, sin φ)‖` for a `2 × 2` real matrix `A`;
  `D_t(φ) = ‖f(φ + t/2) - f(φ - t/2)‖ / (2 sin(t/2))`, `P(φ) = ‖f'(φ)‖`; the expectation over
  uniform `φ` modulo `2π` is `(1/2π) ∫_0^{2π}`.
* `aFun d q = 2^{q/2} Γ((d+q)/2)/Γ(d/2)` (`= E χ_d^q`) and
  `bFun d q = 2^{q/2} Γ((d+1)/2)/Γ((d-q+1)/2)` (`= Π_{j<q} E χ_{d-j}`), for real `d`.
* `gramJac v = √det(⟨v_i, v_j⟩)`: the `q`-Jacobian `J_q(M) = √det(MᵀM)` of the linear map
  `M : ℝ^q → ℝ^k` with columns `v_1, …, v_q`.
* A Haar orthonormal `q`-frame in `ℝ^m` is the Gram–Schmidt orthonormalization of `q` independent
  standard Gaussian vectors in `ℝ^m` (Gaussian QR: its law is the uniform, i.e. `O(m)`-invariant,
  law on the Stiefel manifold; the columns are almost surely independent).
* `E_C`: a pair `(X, Y)` of standard Gaussian vectors in `ℝ^n` with diagonal cross-covariance
  `E XYᵀ = diag(c)`, `|c_i| ≤ 1`, realized as `Y_i = c_i X_i + √(1 - c_i²) Z_i` with `Z`
  independent of `X`. Theorem 3 uses `c = -ρ`, §10.1 uses `c = ρ J` with `J` a diagonal sign
  matrix.
* `ballKernel q a b = L_q(a, b) = [2(1 + a·b)]^{q/2}` (`Real.rpow`).
-/

namespace PowerMinUncut.Threshold

open MeasureTheory ProbabilityTheory

/-- `ℝ^n` with its Euclidean structure. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Radial normalization `v ↦ v / ‖v‖`. -/
noncomputable def normalize {n : ℕ} (v : E n) : E n := ‖v‖⁻¹ • v

/-! ### Lemma 6: the ellipse comparison -/

/-- `f(φ) = A(cos φ, sin φ) / ‖A(cos φ, sin φ)‖`. -/
noncomputable def ellipseMap (A : Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ) : E 2 :=
  normalize (Matrix.toEuclideanLin A !₂[Real.cos φ, Real.sin φ])

/-- The normalized chord ratio `D_t(φ) = ‖f(φ + t/2) - f(φ - t/2)‖ / (2 sin(t/2))`. -/
noncomputable def chordRatio (A : Matrix (Fin 2) (Fin 2) ℝ) (t φ : ℝ) : ℝ :=
  ‖ellipseMap A (φ + t / 2) - ellipseMap A (φ - t / 2)‖ / (2 * Real.sin (t / 2))

/-- The angular speed `P(φ) = ‖f'(φ)‖`. -/
noncomputable def angSpeed (A : Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ) : ℝ :=
  ‖deriv (ellipseMap A) φ‖

/-- Expectation over `φ` uniform modulo `2π`: `(1/2π) ∫_0^{2π} g`. -/
noncomputable def unifAngle (g : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..2 * Real.pi, g φ

/-! ### Normalized Gaussian projection (Theorem 7) -/

/-- The law of a standard Gaussian `k × N` matrix (i.i.d. `N(0,1)` entries). -/
noncomputable def gaussMat (k N : ℕ) : Measure (Fin k → Fin N → ℝ) :=
  Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1

/-- The product `Gu ∈ ℝ^k` of a `k × N` matrix and `u ∈ ℝ^N`. -/
noncomputable def matApply {k N : ℕ} (G : Fin k → Fin N → ℝ) (u : E N) : E k :=
  WithLp.toLp 2 fun i => ∑ j, G i j * u j

/-- The normalized-projection distortion moment `E‖Gu/‖Gu‖ - Gv/‖Gv‖‖^p`. -/
noncomputable def projMoment (k N : ℕ) (p : ℝ) (u v : E N) : ℝ :=
  ∫ G, ‖normalize (matApply G u) - normalize (matApply G v)‖ ^ p ∂gaussMat k N

/-! ### Chi moments and the rank-sensitive matrix inequality (§2, §2.3) -/

/-- `a(d, q) = E χ_d^q = 2^{q/2} Γ((d+q)/2) / Γ(d/2)`. -/
noncomputable def aFun (d : ℝ) (q : ℕ) : ℝ :=
  (2 : ℝ) ^ ((q : ℝ) / 2) * Real.Gamma ((d + q) / 2) / Real.Gamma (d / 2)

/-- `b(d, q) = Π_{j=0}^{q-1} E χ_{d-j} = 2^{q/2} Γ((d+1)/2) / Γ((d-q+1)/2)` (used for `d ≥ q`). -/
noncomputable def bFun (d : ℝ) (q : ℕ) : ℝ :=
  (2 : ℝ) ^ ((q : ℝ) / 2) * Real.Gamma ((d + 1) / 2) / Real.Gamma ((d - q + 1) / 2)

/-- `J_q` of the linear map with columns `v_1, …, v_q`: `√det(⟨v_i, v_j⟩)`. -/
noncomputable def gramJac {q k : ℕ} (v : Fin q → E k) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)))

/-- The Haar orthonormal `q`-frame `Q` of `ℝ^m` built from a Gaussian `m × q` matrix `Z`
(columns `Z j`) by Gram–Schmidt (Gaussian QR). -/
noncomputable def haarFrame {m q : ℕ} (Z : Fin q → E m) : Fin q → E m :=
  InnerProductSpace.gramSchmidtNormed ℝ Z

/-- `E_Q J_q(AQ)` for a Haar orthonormal `q`-frame `Q` of `ℝ^m` and a linear `A : ℝ^m → ℝ^k`. -/
noncomputable def frameJacMean (q : ℕ) {m k : ℕ} (A : E m →L[ℝ] E k) : ℝ :=
  ∫ Z, gramJac (fun j => A (haarFrame Z j)) ∂Measure.pi (fun _ : Fin q => stdGaussian (E m))

/-- `E‖A Z_m‖^q` for a standard Gaussian `Z_m` in `ℝ^m`. -/
noncomputable def gaussPowMoment (q : ℕ) {m k : ℕ} (A : E m →L[ℝ] E k) : ℝ :=
  ∫ z, ‖A z‖ ^ q ∂stdGaussian (E m)

/-! ### Gaussian pairs with diagonal cross-covariance, the ball kernel, endpoints -/

/-- `Y = diag(c) X + diag(√(1 - c²)) Z`. -/
noncomputable def pairY {n : ℕ} (c : Fin n → ℝ) (x z : E n) : E n :=
  WithLp.toLp 2 fun i => c i * x i + Real.sqrt (1 - c i ^ 2) * z i

/-- `E_C g(X, Y)`: `X, Y` standard Gaussian in `ℝ^n` with cross-covariance `E XYᵀ = diag(c)`. -/
noncomputable def pairExp {n : ℕ} (c : Fin n → ℝ) (g : E n → E n → ℝ) : ℝ :=
  ∫ p, g p.1 (pairY c p.1 p.2) ∂(stdGaussian (E n)).prod (stdGaussian (E n))

/-- The ball kernel `L_q(a, b) = [2(1 + a·b)]^{q/2}`. -/
noncomputable def ballKernel (q : ℕ) {k : ℕ} (a b : E k) : ℝ :=
  (2 * (1 + inner ℝ a b)) ^ ((q : ℝ) / 2)

/-- `a_ρ = [2(1 - ρ)]^{q/2}`. -/
noncomputable def aRho (q : ℕ) (ρ : ℝ) : ℝ := (2 * (1 - ρ)) ^ ((q : ℝ) / 2)

/-- The uniform sphere endpoint quantity of Theorem 3:
`inf_{n ≥ k} inf_{f : ℝ^n → S^{k-1} measurable} E_{-ρI} ‖f(X) + f(Y)‖^q / [2(1-ρ)]^{q/2}`. -/
noncomputable def sphereEndpoint (k q : ℕ) (ρ : ℝ) : ℝ :=
  sInf {e | ∃ n : ℕ, k ≤ n ∧ ∃ f : E n → E k, Measurable f ∧ (∀ x, ‖f x‖ = 1) ∧
    e = pairExp (fun _ => -ρ) (fun x y => ‖f x + f y‖ ^ q) / aRho q ρ}

/-- The same quantity for the ball kernel `L_q` over measurable maps into the closed unit ball. -/
noncomputable def ballEndpoint (k q : ℕ) (ρ : ℝ) : ℝ :=
  sInf {e | ∃ n : ℕ, k ≤ n ∧ ∃ f : E n → E k, Measurable f ∧ (∀ x, ‖f x‖ ≤ 1) ∧
    e = pairExp (fun _ => -ρ) (fun x y => ballKernel q (f x) (f y)) / aRho q ρ}

end PowerMinUncut.Threshold


