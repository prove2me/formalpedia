-- Prove2me | Definitions.Def_PowerMinUncut_Threshold_Sobolev
-- name    : PowerMinUncut_Threshold_Sobolev
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:43:51.851093+00:00
-- url     : https://prove2.me/theorems/e217d81d-58fa-40a8-b2dd-8ad8c25f518e
-- title:
--   Gaussian and spherical W^{1,q} maps into spheres, odd maps, the tangential q-Jacobian and the shell energy E_θ
-- statement:
--   *Gaussian Sobolev maps.* $f:\mathbb R^n\to\mathbb R^k$ with $Df:\mathbb R^n\to L(\mathbb R^n,\mathbb R^k)$ belongs to $W^{1,q}(\gamma_n;S^{k-1})$ when $f$ and $Df$ are locally integrable, $Df$ is the **weak derivative** of $f$ — $\int \partial_v\varphi\, f\,dx=-\int\varphi\,Df(x)v\,dx$ for every smooth compactly supported $\varphi$ and every direction $v$ — both $f$ and $Df$ lie in $L^q(\gamma_n)$, and $\|f\|=1$ almost everywhere. $f$ is **odd** if $f(-x)=-f(x)$ for almost every $x$. The **directional energy** is $\mathbb E\|Df(X)Z\|^q$ for independent standard Gaussian $X,Z$. The normalized coordinate projection is $f_k(x)=x_{1:k}/\|x_{1:k}\|$.
--
--   *Spherical Sobolev maps.* $S^d\subset\mathbb R^{d+1}$ carries its surface measure (total mass $|S^d|$). $F$ with a tangential derivative $D_SF=G$ ($G(x)x=0$, so $G(x)$ acts on $T_xS^d$) belongs to $W^{1,q}(S^d;\mathbb R^k)$ when $F,G\in L^q(S^d)$ and $G$ is the weak derivative of $F$ along every rotation field $V_{ab}(x)=x_ae_b-x_be_a$:
--   $$\int_{S^d}(V_{ab}\varphi)\,F\,d\sigma=-\int_{S^d}\varphi\,G(x)V_{ab}(x)\,d\sigma\quad\text{for every smooth }\varphi .$$
--   Such an $F$ is in $W^{1,q}(S^d;S^{k-1})$ and odd when $\|F\|=1$ and $F(-x)=-F(x)$ for almost every $x\in S^d$. Its **tangential $q$-Jacobian** (for $d=q$) is $J_q(D_SF(x))=\sqrt{\det(G(x)^{\mathsf T}G(x)+xx^{\mathsf T})}$.
--
--   *Shell energy.* For $d\ge 2$, $\theta>0$ and measurable $F:S^d\to S^{k-1}$, with $x$ uniform on $S^d$ and $z$ uniform on $\{z\in S^d:\langle x,z\rangle=\cos\theta\}$,
--   $$E_\theta(F)=\mathbb E\,\|F(x)+F(-z)\|^q,$$
--   and `shellInf d k q θ` is $\inf_F E_\theta(F)/\theta^q$ over measurable sphere-valued $F$.
--
--   **Formalization Note.** The rotation fields preserve surface measure and span every tangent space, so this is the usual $W^{1,q}(S^d)$ with $D_SF=G$; no continuity or smoothness is assumed. $J_q$ equals the Gram determinant of $G(x)$ on an orthonormal basis of $T_xS^q$ (complete the basis by $x$; $G(x)x=0$). The angle-$\theta$ pair is built from two independent Gaussian vectors $X,Y$: $x=X/\|X\|$, $u$ the normalized component of $Y$ orthogonal to $x$, $z=\cos\theta\,x+\sin\theta\,u$; conditionally on $x$, $u$ is uniform on the unit sphere of $x^\perp$. Maps on $S^d$ are maps on $\mathbb R^{d+1}$ of which only the values on $S^d$ are used.
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 2, Theorem 2; p. 6, Lemma 5; p. 10, §4.1; p. 15, §5.4

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Gaussian

/-!
# Gaussian and spherical `W^{1,q}` maps, the tangential `q`-Jacobian, and shell energies

Xie, *Sharp Power Loss Thresholds for Vector Min Uncut*, STOC 2027 submission (manuscript
sha256 391063da…): p. 2 (Theorem 2, `W^{1,q}(γ_n; S^{k-1})`, directional energy), p. 6
(Lemma 5, `W^{1,q}(S^q; S^{k-1})`, `J_q(D_S F)`), p. 10 (§4.1, `E_θ`), p. 15 (§5.4).

Conventions.
* **Gaussian Sobolev maps.** `f : ℝ^n → ℝ^k` with a candidate derivative
  `Df : ℝ^n → L(ℝ^n, ℝ^k)` is in `W^{1,q}(γ_n; ℝ^k)` when `f` and `Df` are locally integrable,
  `Df` is the weak (distributional) derivative of `f` — for every smooth compactly supported test
  function `φ` and every direction `v`, `∫ ∂_vφ · f = -∫ φ · Df(·)v` (Lebesgue measure) — and
  `f, Df ∈ L^q(γ_n)`. It is **sphere-valued** if `‖f‖ = 1` a.e. and **odd** if `f(-x) = -f(x)` a.e.
* **The sphere.** `S^d ⊆ ℝ^{d+1}` carries the surface measure `σ = volume.toSphere` (total mass
  `|S^d| = (d+1)·vol(B^{d+1})`); `σ_d = σ / |S^d|` is the normalized measure. Maps on `S^d` are
  maps on `ℝ^{d+1}` of which only the values on the sphere matter.
* **Spherical Sobolev maps.** `F` with a candidate tangential derivative
  `G : ℝ^{d+1} → L(ℝ^{d+1}, ℝ^k)` (`G(x)x = 0` on the sphere, so `G(x)` acts on `T_xS^d`) is in
  `W^{1,q}(S^d; ℝ^k)` when `F, G ∈ L^q(σ)` and `G` is the weak derivative of `F` along every
  rotation (Killing) field `V_{ab}(x) = x_a e_b - x_b e_a`: `∫ (V_{ab}φ) F dσ = -∫ φ G(x)V_{ab}(x) dσ`
  for every smooth `φ` on `ℝ^{d+1}`. The fields `V_{ab}` preserve `σ` (no divergence term) and span
  every tangent space, so this is the usual `W^{1,q}` with `D_S F = G`.
* `sphereJac G x = J_q(D_S F(x)) = √det(G(x)ᵀG(x) + xxᵀ)`: in an orthonormal basis of `T_xS^q`
  completed by `x` this is the Gram determinant of `G(x)` on the tangent space (as `G(x)x = 0`).
* **Shell energy (§4.1).** For `x` uniform on `S^d` and `z` uniform on `{z ∈ S^d : ⟨x, z⟩ = cos θ}`,
  `E_θ(F) = E‖F(x) + F(-z)‖^q`. The pair is realized from two independent standard Gaussian
  vectors `X, Y` of `ℝ^{d+1}`: `x = X/‖X‖`, `u` = normalized component of `Y` orthogonal to `x`,
  `z = cos θ · x + sin θ · u` (conditionally on `x`, `u` is uniform on the unit sphere of `x^⊥`).
-/

namespace PowerMinUncut.Threshold

open MeasureTheory ProbabilityTheory

/-! ### Gaussian `W^{1,q}` -/

/-- `Df` is the weak derivative of `f` on `ℝ^n` (both locally integrable). -/
def HasWeakDeriv {n k : ℕ} (f : E n → E k) (Df : E n → (E n →L[ℝ] E k)) : Prop :=
  LocallyIntegrable f ∧ LocallyIntegrable Df ∧
    ∀ φ : E n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∀ v : E n,
      ∫ x, fderiv ℝ φ x v • f x = -∫ x, φ x • Df x v

/-- `f ∈ W^{1,q}(γ_n; S^{k-1})` with weak derivative `Df`: weak derivative, `f, Df ∈ L^q(γ_n)`,
`‖f‖ = 1` almost everywhere. -/
def IsGaussSobolevSphere (q : ℕ) {n k : ℕ} (f : E n → E k) (Df : E n → (E n →L[ℝ] E k)) :
    Prop :=
  HasWeakDeriv f Df ∧ MemLp f q (stdGaussian (E n)) ∧ MemLp Df q (stdGaussian (E n)) ∧
    ∀ᵐ x, ‖f x‖ = 1

/-- `f` is odd almost everywhere: `f(-x) = -f(x)` for a.e. `x`. -/
def IsOddAE {n k : ℕ} (f : E n → E k) : Prop :=
  ∀ᵐ x, f (-x) = -f x

/-- The directional energy `E‖Df(X)Z‖^q`, `X, Z` independent standard Gaussian vectors. -/
noncomputable def dirEnergy (q : ℕ) {n k : ℕ} (Df : E n → (E n →L[ℝ] E k)) : ℝ :=
  ∫ x, ∫ z, ‖Df x z‖ ^ q ∂stdGaussian (E n) ∂stdGaussian (E n)

/-- Normalized projection onto the first `k` coordinates, `f_k(x) = x_{1:k}/‖x_{1:k}‖`. -/
noncomputable def coordProj (n k : ℕ) (x : E n) : E k :=
  normalize (WithLp.toLp 2 fun i : Fin k => if h : (i : ℕ) < n then x ⟨i, h⟩ else 0)

/-! ### The sphere -/

/-- Surface measure on `S^d ⊆ ℝ^{d+1}` (total mass `|S^d|`). -/
noncomputable def sphereArea (d : ℕ) : Measure (Metric.sphere (0 : E (d + 1)) 1) :=
  (volume : Measure (E (d + 1))).toSphere

/-- The rotation (Killing) field `V_{ab}(x) = x_a e_b - x_b e_a`. -/
noncomputable def killing {m : ℕ} (a b : Fin m) (x : E m) : E m :=
  x a • EuclideanSpace.single b (1 : ℝ) - x b • EuclideanSpace.single a (1 : ℝ)

/-- `F ∈ W^{1,q}(S^d; ℝ^k)` with tangential derivative `G` (`D_S F = G`). -/
def IsSphereSobolev (d q : ℕ) {k : ℕ} (F : E (d + 1) → E k)
    (G : E (d + 1) → (E (d + 1) →L[ℝ] E k)) : Prop :=
  MemLp (fun x : Metric.sphere (0 : E (d + 1)) 1 => F x) q (sphereArea d) ∧
    MemLp (fun x : Metric.sphere (0 : E (d + 1)) 1 => G x) q (sphereArea d) ∧
    (∀ x : Metric.sphere (0 : E (d + 1)) 1, G x (x : E (d + 1)) = 0) ∧
    ∀ φ : E (d + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → ∀ a b : Fin (d + 1),
      ∫ x : Metric.sphere (0 : E (d + 1)) 1,
          fderiv ℝ φ (x : E (d + 1)) (killing a b (x : E (d + 1))) • F (x : E (d + 1))
            ∂sphereArea d =
        -∫ x : Metric.sphere (0 : E (d + 1)) 1,
          φ (x : E (d + 1)) • G (x : E (d + 1)) (killing a b (x : E (d + 1))) ∂sphereArea d

/-- `F` is sphere-valued (`‖F‖ = 1` `σ`-a.e.) and odd (`F(-x) = -F(x)` `σ`-a.e.) on `S^d`. -/
def IsOddSphereValued (d : ℕ) {k : ℕ} (F : E (d + 1) → E k) : Prop :=
  (∀ᵐ x : Metric.sphere (0 : E (d + 1)) 1 ∂sphereArea d, ‖F (x : E (d + 1))‖ = 1) ∧
    ∀ᵐ x : Metric.sphere (0 : E (d + 1)) 1 ∂sphereArea d, F (-(x : E (d + 1))) = -F (x : E (d + 1))

/-- An odd map in `W^{1,q}(S^d; S^{k-1})` with tangential derivative `G`. -/
def IsOddSphereSobolev (d q : ℕ) {k : ℕ} (F : E (d + 1) → E k)
    (G : E (d + 1) → (E (d + 1) →L[ℝ] E k)) : Prop :=
  IsSphereSobolev d q F G ∧ IsOddSphereValued d F

/-- `J_q(D_S F(x)) = √det(G(x)ᵀG(x) + xxᵀ)`, the Jacobian of `G(x)` on `T_xS^d`. -/
noncomputable def sphereJac {m k : ℕ} (G : E m →L[ℝ] E k) (x : E m) : ℝ :=
  Real.sqrt (LinearMap.det
    (((ContinuousLinearMap.adjoint G ∘L G + (innerSL ℝ x).smulRight x : E m →L[ℝ] E m)) :
      E m →ₗ[ℝ] E m))

/-! ### Shell energies (§4.1) -/

/-- The angle-`θ` pair `(x, z)` on `S^d` built from two Gaussian vectors `X, Y`. -/
noncomputable def shellPair {m : ℕ} (θ : ℝ) (X Y : E m) : E m × E m :=
  (normalize X,
    Real.cos θ • normalize X + Real.sin θ • normalize (Y - inner ℝ Y (normalize X) • normalize X))

/-- `E_θ(F) = E_{x, z ∼ T_θ(x)} ‖F(x) + F(-z)‖^q` on `S^d`. -/
noncomputable def shellEnergy (d q : ℕ) {k : ℕ} (θ : ℝ) (F : E (d + 1) → E k) : ℝ :=
  ∫ p, ‖F (shellPair θ p.1 p.2).1 + F (-(shellPair θ p.1 p.2).2)‖ ^ q
    ∂(stdGaussian (E (d + 1))).prod (stdGaussian (E (d + 1)))

/-- `inf_{F : S^d → S^{k-1} measurable} E_θ(F) / θ^q`. -/
noncomputable def shellInf (d k q : ℕ) (θ : ℝ) : ℝ :=
  sInf {e | ∃ F : E (d + 1) → E k, Measurable F ∧
    (∀ x ∈ Metric.sphere (0 : E (d + 1)) 1, ‖F x‖ = 1) ∧ e = shellEnergy d q θ F / θ ^ q}

end PowerMinUncut.Threshold


