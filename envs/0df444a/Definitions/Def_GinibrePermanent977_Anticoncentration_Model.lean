-- Prove2me | Definitions.Def_GinibrePermanent977_Anticoncentration_Model
-- name    : GinibrePermanent977_Anticoncentration_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:09:30.867336+00:00
-- url     : https://prove2.me/theorems/8ec0a100-267f-4ffe-91cf-4ad6fb3b312c
-- title:
--   Ginibre ensembles over $\mathbb R,\mathbb C,\mathbb H$, the row-ordered permanent, cofactor columns, gamma benchmarks and Laplace orders
-- statement:
--   This file fixes the model of the paper: the three scalar domains, the standard Ginibre laws, the row-ordered permanent and its cofactor columns, the gamma benchmarks, the Laplace-transform orders and the constants of the density bound.
--
--   1. **Scalars** (p. 1). $\mathbb K\in\{\mathbb R,\mathbb C,\mathbb H\}$ (Hamilton's quaternions with basis $1,i,j,k$) and $\beta=\dim_{\mathbb R}\mathbb K\in\{1,2,4\}$. Each $\mathbb K$ carries its usual multiplication, conjugation $z\mapsto\bar z$, absolute value $|z|$, the Euclidean inner product $(x,y)_{\mathbb R}=\operatorname{Re}(\bar x y)$ of its real coordinates, the Borel $\sigma$-algebra and Lebesgue measure in these coordinates.
--   2. **Standard $\mathbb K$-Gaussian and Ginibre matrices** (p. 1). A standard $\mathbb K$-Gaussian is a scalar whose $\beta$ real coordinates are independent $N(0,1/\beta)$, so $E|Z|^2=1$. An $m\times n$ standard $\mathbb K$-Gaussian matrix has i.i.d. standard $\mathbb K$-Gaussian entries; for $m=n$ it is the standard Ginibre matrix $G_n^{\mathbb K}$, and for $m=n-1$ the matrix $B_n$ of §§1.1, 3.2.
--   3. **Row-ordered permanent** (p. 1). For $A\in\mathbb K^{n\times n}$,
--   $$\operatorname{per}_{\mathbb K}A=\sum_{\sigma\in S_n}a_{1,\sigma(1)}a_{2,\sigma(2)}\cdots a_{n,\sigma(n)},$$
--   the product taken in increasing row order; the $0\times0$ permanent is $1$. The signed version $\sum_\sigma\operatorname{sgn}(\sigma)a_{1,\sigma(1)}\cdots a_{n,\sigma(n)}$ is the ordinary determinant over $\mathbb R,\mathbb C$, where alone it is used.
--   4. **Cofactor columns** (pp. 3, 9). For an $(n-1)\times n$ matrix $B$ let $B_{-j}$ delete column $j$, keeping the order of rows and remaining columns. Then $(C_n)_j=\operatorname{per}_{\mathbb K}(B_{-j})$ and, over $\mathbb R,\mathbb C$, $(C_n^{\det})_j=(-1)^{j-1}\det(B_{-j})$; $C_1=C_1^{\det}=(1)$.
--   5. **Study determinant** (Definition 2.2, p. 5; real-determinant identity p. 6). $\operatorname{Sdet}A=\prod_j\sigma_j(A)$ for $A\in\mathbb H^{n\times n}$, the product of its quaternionic singular values.
--   6. **Gamma benchmarks** (p. 4). Independent $\gamma_{k,\beta}\sim\mathrm{Gamma}(\beta k/2,\,2/\beta)$ (shape, scale), $\Pi_{m,\beta}=\prod_{k=2}^m\gamma_{k,\beta}$, $\Pi_{0,\beta}=\Pi_{1,\beta}=1$; the benchmark column is $\sqrt{\Pi_{n-1,\beta}}\,g_n$ with $g_n$ a standard $\mathbb K$-Gaussian column independent of the gamma variables.
--   7. **Inner products and orders** (pp. 3–4). $(z,w)_{\mathbb R}=\operatorname{Re}\sum_j\bar z_jw_j$ on $\mathbb K^m$; $\|z\|_2^2=\sum_j|z_j|^2$. For random columns $X,Y\in\mathbb K^m$, $XX^*\preceq_{Lt}YY^*$ means $E e^{-\operatorname{Re}\operatorname{tr}(TXX^*)}\ge Ee^{-\operatorname{Re}\operatorname{tr}(TYY^*)}$ for every Hermitian $T\succeq0$ (Definition 1.4); $U\le_{Lt}V$ for nonnegative scalars is the published Laplace-transform order (Definition 1.3).
--   8. **Bilinear Gaussian characteristic function** (pp. 6–7). For $T\in\mathbb R^{d\times d}$, $L\in\mathbb R^{d\times k}$, $a,b\in\mathbb R^k$,
--   $$F_{T,L}(a,b)=E_{X,Y}\exp\bigl(i(X^*TY+X^*Lb+Y^*La)\bigr),$$
--   $X,Y$ independent standard Gaussian columns in $\mathbb R^d$.
--   9. **Normalization and constants** (pp. 2, 12–13). $W_n^{\mathbb K}=\operatorname{per}_{\mathbb K}G_n^{\mathbb K}/\sqrt{n!}$,
--   $$\kappa_{n,\beta}=\frac{(n!)^{\beta/2}}{\pi^{\beta/2}}\Bigl(\frac\beta2\Bigr)^{\beta n/2}\frac{\Gamma(\beta/2)}{\Gamma(\beta n/2)},\qquad \omega_\beta=\frac{\pi^{\beta/2}}{\Gamma(\beta/2+1)}.$$
--
--   These are the objects in which every statement of the mission is written; the permanent, the Gaussian laws and the gamma benchmarks are concrete data, not hypotheses.
--
--   **Formalization Note** The scalar domain is a tag `F : Scalar` whose carrier `F.K` is `ℝ`, `ℂ` or `ℍ[ℝ]` with their Mathlib structures (Lebesgue measure on `ℍ[ℝ]` is the inner-product-space volume, the Borel σ-algebra its σ-algebra). Laws are measures on canonical product spaces (`ginibre F m n` on `Fin m → Fin n → F.K`, `gammaVec F m` on `Fin m → ℝ` with coordinate `k` the variable $\gamma_{k+1,\beta}$, `benchLaw` their product with a Gaussian column). Indices are 0-based. Mathlib's `gammaMeasure` takes shape and **rate**, so $\gamma_{k,\beta}$ is `gammaMeasure (βk/2) (β/2)`. The Study determinant is written through the identity $\det_{\mathbb R}(A)=\operatorname{Sdet}(A)^4$ of p. 6 ($A$ acting on $\mathbb H^n$ as a real-linear map). $\kappa_{n,\beta}$ is the closed form (22) of the limit (20). The matrix order is stated for rank-one outer products, the only matrices it is applied to, using $\operatorname{Re}\operatorname{tr}(Tvv^*)=\operatorname{Re}(v^*Tv)$. The scalar order and the standard Gaussian vector law $N(0,I_d)$ of item 8 are the published `StochasticOrders_LaplaceTransform_LaplaceOrder` and `SmoothBerr_stdGaussianVec`.
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §1, p. 1; §1.1, p. 3 (Definitions 1.3–1.4, cofactor columns); §1.2, p. 4; §2, p. 4 (gamma variables); Definition 2.2, pp. 5–6; §3.1, pp. 6–7 ($F_{T,L}$); §3.2, p. 9; §3.5, pp. 12–13, Eqs. (20), (22) (PDF SHA-256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_SmoothBerr_stdGaussianVec

/-!
# Ginibre ensembles over ℝ, ℂ, ℍ, the row-ordered permanent, cofactors and gamma benchmarks

Frederic Koehler, Pui Kuen Leung, *Anticoncentration of the Permanent in Ginibre Ensembles*,
STOC 2027 submission #977 (October 2026): §1, p. 1 (row-ordered permanent, standard
`K`-Gaussian); Definitions 1.3–1.4, p. 3 (Laplace-transform orders); §1.1, p. 3 (cofactor
columns); §1.2, p. 4 (inner products, `X_n`, `Δ_n`); §2, p. 4 (gamma variables, `Π_{m,β}`);
Definition 2.2 and p. 6 (Study determinant); §3.1, pp. 6–7 (`F_{T,L}`); §3.2, p. 9 (`φ_n^K`);
§3.5, pp. 12–13 (`κ_{n,β}` (22), `ω_β`).

Conventions. The scalar domain is one of three concrete carriers, selected by a tag
`F : Scalar`; `β = dim_ℝ K ∈ {1, 2, 4}`. Indices are 0-based: source index `j` is Lean `j - 1`.
Products in the permanent are taken in increasing row order. Laws are measures on the
canonical sample spaces (products of Gaussian/gamma laws); random variables are functions on
them.
-/

namespace GinibrePermanent977.Anticoncentration

open MeasureTheory ProbabilityTheory Matrix
open scoped Quaternion BigOperators Nat

/-! ## The three scalar domains -/

/-- Tag for the scalar domain `K ∈ {ℝ, ℂ, ℍ}`. -/
inductive Scalar
  | real
  | complex
  | quaternion
  deriving DecidableEq

/-- The concrete carrier `K` of a scalar tag: `ℝ`, `ℂ`, or Hamilton's quaternions `ℍ[ℝ]`. -/
def Scalar.K : Scalar → Type
  | .real => ℝ
  | .complex => ℂ
  | .quaternion => ℍ[ℝ]

/-- `β = dim_ℝ K`. -/
def Scalar.beta : Scalar → ℕ
  | .real => 1
  | .complex => 2
  | .quaternion => 4

noncomputable instance Scalar.instNormedRing : (F : Scalar) → NormedRing F.K
  | .real => inferInstanceAs (NormedRing ℝ)
  | .complex => inferInstanceAs (NormedRing ℂ)
  | .quaternion => inferInstanceAs (NormedRing ℍ[ℝ])

noncomputable instance Scalar.instStarRing : (F : Scalar) → StarRing F.K
  | .real => inferInstanceAs (StarRing ℝ)
  | .complex => inferInstanceAs (StarRing ℂ)
  | .quaternion => inferInstanceAs (StarRing ℍ[ℝ])

noncomputable instance Scalar.instInnerProductSpace : (F : Scalar) → InnerProductSpace ℝ F.K
  | .real => inferInstanceAs (InnerProductSpace ℝ ℝ)
  | .complex => inferInstanceAs (InnerProductSpace ℝ ℂ)
  | .quaternion => inferInstanceAs (InnerProductSpace ℝ ℍ[ℝ])

/-- Lebesgue measure on the underlying Euclidean space `ℝ^β` (orthonormal real coordinates
`1`; `1, i`; `1, i, j, k`), with the Borel σ-algebra. -/
noncomputable instance Scalar.instMeasureSpace : (F : Scalar) → MeasureSpace F.K
  | .real => inferInstanceAs (MeasureSpace ℝ)
  | .complex => inferInstanceAs (MeasureSpace ℂ)
  | .quaternion =>
      letI : MeasurableSpace ℍ[ℝ] := borel ℍ[ℝ]
      haveI : BorelSpace ℍ[ℝ] := ⟨rfl⟩
      (measureSpaceOfInnerProductSpace : MeasureSpace ℍ[ℝ])

instance Scalar.instBorelSpace : (F : Scalar) → BorelSpace F.K
  | .real => inferInstanceAs (BorelSpace ℝ)
  | .complex => inferInstanceAs (BorelSpace ℂ)
  | .quaternion => ⟨rfl⟩

/-! ## Standard `K`-Gaussians and Ginibre matrices (p. 1) -/

/-- The quaternion `v₀ + v₁ i + v₂ j + v₃ k` with real coordinates `v`. -/
def quatOfCoords : (Fin 4 → ℝ) →ₗ[ℝ] ℍ[ℝ] where
  toFun v := ⟨v 0, v 1, v 2, v 3⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The standard `K`-Gaussian: its `β` real coordinates (in the basis `1`; `1, i`;
`1, i, j, k`) are independent `N(0, 1/β)`. -/
noncomputable def gaussian : (F : Scalar) → Measure F.K
  | .real => gaussianReal 0 1
  | .complex =>
      ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))).map
        (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
  | .quaternion =>
      (Measure.pi fun _ : Fin 4 => gaussianReal 0 (1 / 4)).map quatOfCoords

instance gaussian_isProbabilityMeasure (F : Scalar) : IsProbabilityMeasure (gaussian F) := by
  cases F
  · exact inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
  · refine Measure.isProbabilityMeasure_map ?_
    exact (Complex.equivRealProdCLM.symm.continuous.measurable).aemeasurable
  · have hB := Scalar.instBorelSpace .quaternion
    refine Measure.isProbabilityMeasure_map ?_
    exact Measurable.aemeasurable (Continuous.measurable (γ := Scalar.quaternion.K)
      quatOfCoords.continuous_of_finiteDimensional)

/-- Law of a standard `K`-Gaussian column in `K^m`: independent standard `K`-Gaussian
coordinates. -/
noncomputable def gaussVec (F : Scalar) (m : ℕ) : Measure (Fin m → F.K) :=
  Measure.pi fun _ => gaussian F

/-- Law of an `m × n` matrix with i.i.d. standard `K`-Gaussian entries (row index first);
for `m = n` this is the standard `K`-Ginibre matrix `G_n^K`, and for `m = n - 1` the matrix
`B_n` of §1.1 and §3.2. -/
noncomputable def ginibre (F : Scalar) (m n : ℕ) : Measure (Fin m → Fin n → F.K) :=
  Measure.pi fun _ => Measure.pi fun _ => gaussian F

/-! ## Row-ordered permanent, Cayley determinant, cofactor columns (pp. 1, 3, 9) -/

section Algebra

variable {K : Type*} [Ring K]

/-- The row-ordered permanent `per_K A = ∑_σ a_{1,σ(1)} a_{2,σ(2)} ⋯ a_{n,σ(n)}`, the factors
multiplied in increasing row order. The `0 × 0` permanent is `1`. -/
def perK {n : ℕ} (A : Fin n → Fin n → K) : K :=
  ∑ σ : Equiv.Perm (Fin n), (List.ofFn fun i => A i (σ i)).prod

/-- The signed row-ordered (Cayley) determinant `∑_σ sgn(σ) a_{1,σ(1)} ⋯ a_{n,σ(n)}`.
Over the commutative fields `ℝ`, `ℂ` this is the ordinary determinant (Leibniz formula); it is
used only there. -/
def cdetK {n : ℕ} (A : Fin n → Fin n → K) : K :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : K) * (List.ofFn fun i => A i (σ i)).prod

/-- The increasing enumeration of the columns `≠ j`: `k ↦ k` for `k < j`, `k ↦ k + 1`
otherwise. -/
def skipCol {n : ℕ} (j : Fin n) (k : Fin (n - 1)) : Fin n :=
  if h : k.val < j.val then ⟨k.val, by omega⟩ else ⟨k.val + 1, by omega⟩

/-- `(B)_{-j}`: the `(n-1) × (n-1)` matrix obtained from `B` by deleting column `j`, rows and
remaining columns kept in increasing order. -/
def minor {n : ℕ} (B : Fin (n - 1) → Fin n → K) (j : Fin n) : Fin (n - 1) → Fin (n - 1) → K :=
  fun i k => B i (skipCol j k)

/-- The permanental cofactor column `(C_n)_j = per_K((B)_{-j})`. For `n = 1` it is `(1)`. -/
def perCofactor {n : ℕ} (B : Fin (n - 1) → Fin n → K) : Fin n → K :=
  fun j => perK (minor B j)

/-- The signed determinantal cofactor column `(C_n^{det})_j = (-1)^{j-1} det((B)_{-j})`
(source index `j`, Lean index `j - 1`). For `n = 1` it is `(1)`. -/
def detCofactor {n : ℕ} (B : Fin (n - 1) → Fin n → K) : Fin n → K :=
  fun j => (-1 : K) ^ (j : ℕ) * cdetK (minor B j)

end Algebra

/-! ## Study determinant (Definition 2.2, pp. 5–6) -/

/-- Left multiplication `v ↦ A v` of a quaternionic matrix on columns `ℍ^n`, as a real-linear
map of the underlying real space `ℝ^{4n}`. -/
noncomputable def realMulVec {n : ℕ} (A : Fin n → Fin n → ℍ[ℝ]) :
    (Fin n → ℍ[ℝ]) →ₗ[ℝ] (Fin n → ℍ[ℝ]) where
  toFun v := Matrix.of A *ᵥ v
  map_add' v w := Matrix.mulVec_add _ v w
  map_smul' c v := by simp [Matrix.mulVec_smul]

/-- The Study determinant `Sdet A = ∏_j σ_j(A)` (Definition 2.2), the product of the
quaternionic singular values, written through the identity `det_ℝ(A) = Sdet(A)^4` of p. 6 for
`A` regarded as a real-linear operator: `Sdet A = det_ℝ(A)^{1/4}`. -/
noncomputable def studyDet {n : ℕ} (A : Fin n → Fin n → ℍ[ℝ]) : ℝ :=
  (LinearMap.det (realMulVec A)) ^ (1 / 4 : ℝ)

/-! ## Gamma benchmarks (§2, p. 4) -/

/-- `γ_{k,β} ∼ Gamma(βk/2, 2/β)` (shape, scale), i.e. shape `βk/2` and **rate** `β/2`,
Mathlib's `gammaMeasure` convention. -/
noncomputable def gammaLaw (F : Scalar) (k : ℕ) : Measure ℝ :=
  gammaMeasure ((F.beta : ℝ) * k / 2) ((F.beta : ℝ) / 2)

lemma beta_pos (F : Scalar) : (0 : ℝ) < F.beta := by
  cases F <;> norm_num [Scalar.beta]

instance gammaLaw_succ_isProbabilityMeasure (F : Scalar) (k : ℕ) :
    IsProbabilityMeasure (gammaLaw F (k + 1)) :=
  isProbabilityMeasure_gammaMeasure (by have := beta_pos F; positivity)
    (by have := beta_pos F; positivity)

/-- Joint law of independent `γ_{1,β}, …, γ_{m,β}`; the coordinate `k : Fin m` is
`γ_{k+1,β}`. -/
noncomputable def gammaVec (F : Scalar) (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun k : Fin m => gammaLaw F (k.val + 1)

/-- `Π_{m,β} = ∏_{k=2}^m γ_{k,β}` as a function of `(γ_1, …, γ_m)`; the empty product is `1`,
so `Π_{0,β} = Π_{1,β} = 1`. -/
def gammaPi {m : ℕ} (γ : Fin m → ℝ) : ℝ :=
  ∏ k ∈ Finset.univ.filter (fun k : Fin m => 1 ≤ k.val), γ k

/-- Law of `√Π_{n-1,β} g_n` with `g_n` a standard `K`-Gaussian column in `K^n` independent of
the gamma variables: the product law of `(γ_1, …, γ_{n-1})` and `g_n`. -/
noncomputable def benchLaw (F : Scalar) (n : ℕ) : Measure ((Fin (n - 1) → ℝ) × (Fin n → F.K)) :=
  (gammaVec F (n - 1)).prod (gaussVec F n)

/-- The benchmark vector `√Π_{n-1,β} · g_n` on the sample space of `benchLaw`. -/
noncomputable def benchVec {F : Scalar} {n : ℕ} (p : (Fin (n - 1) → ℝ) × (Fin n → F.K)) :
    Fin n → F.K :=
  Real.sqrt (gammaPi p.1) • p.2

/-! ## Inner products, quadratic forms, Laplace-transform orders (pp. 3–4) -/

section Pairing

variable {K : Type*} [NormedRing K] [StarRing K] [InnerProductSpace ℝ K]

/-- `(z, w)_ℝ = Re⟨z, w⟩ = Re ∑_j \bar z_j w_j`, the Euclidean inner product of the underlying
real space `ℝ^{βm}`, written as the sum of the real inner products of the coordinates. -/
def realInner {m : ℕ} (z w : Fin m → K) : ℝ :=
  ∑ j, inner ℝ (z j) (w j)

/-- The real quadratic form `Re(v^* T v) = Re tr(T v v^*)` of a `K`-matrix `T`, with
`(T v)_i = ∑_j T_{ij} v_j`. -/
def quadForm {m : ℕ} (T : Matrix (Fin m) (Fin m) K) (v : Fin m → K) : ℝ :=
  realInner v (T *ᵥ v)

/-- `T` is Hermitian (`T^* = T`) and positive semidefinite (`Re(v^* T v) ≥ 0` for every
`v ∈ K^m`). Singular `T`, including `T = 0`, are allowed. -/
def IsHermPSD {m : ℕ} (T : Matrix (Fin m) (Fin m) K) : Prop :=
  T.conjTranspose = T ∧ ∀ v : Fin m → K, 0 ≤ quadForm T v

/-- Matrix-variate Laplace-transform order for rank-one outer products (Definition 1.4, (3)):
`X X^* ⪯_{Lt} Y Y^*` for a random column `X` on `(Ω, μ)` and `Y` on `(Ω', ν)`, i.e.
`E exp(-Re tr(T X X^*)) ≥ E exp(-Re tr(T Y Y^*))` for every Hermitian `T ⪰ 0`; here
`Re tr(T v v^*) = Re(v^* T v)`. -/
def OuterLaplaceOrder {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {m : ℕ}
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → Fin m → K) (Y : Ω' → Fin m → K) : Prop :=
  ∀ T : Matrix (Fin m) (Fin m) K, IsHermPSD T →
    ∫ ω, Real.exp (-quadForm T (Y ω)) ∂ν ≤ ∫ ω, Real.exp (-quadForm T (X ω)) ∂μ

/-- Characteristic function `E exp(i (z, X)_ℝ)` of a random column `X : Ω → K^m` under `μ`. -/
noncomputable def charFunK {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (μ : Measure Ω)
    (X : Ω → Fin m → K) (z : Fin m → K) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (realInner z (X ω) : ℂ)) ∂μ

/-- Euclidean norm `‖z‖₂ = (∑_j |z_j|²)^{1/2}` of `z ∈ K^m`. -/
noncomputable def norm2 {m : ℕ} (z : Fin m → K) : ℝ :=
  Real.sqrt (∑ j, ‖z j‖ ^ 2)

end Pairing

/-! ## The bilinear Gaussian characteristic function (§3.1, pp. 6–7) -/

/-- `F_{T,L}(a, b) = E_{X,Y} exp(i(X^* T Y + X^* L b + Y^* L a))`, `X, Y` independent standard
Gaussian columns in `ℝ^d` (`T ∈ ℝ^{d×d}`, `L ∈ ℝ^{d×k}`, `a, b ∈ ℝ^k`). -/
noncomputable def bilinChar {d k : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (a b : Fin k → ℝ) : ℂ :=
  ∫ p : (Fin d → ℝ) × (Fin d → ℝ),
    Complex.exp (Complex.I *
      ((p.1 ⬝ᵥ (T *ᵥ p.2) + p.1 ⬝ᵥ (L *ᵥ b) + p.2 ⬝ᵥ (L *ᵥ a) : ℝ) : ℂ))
    ∂((SmoothBerr.stdGaussianVec d).prod (SmoothBerr.stdGaussianVec d))

/-! ## Normalized permanent and the density constants (pp. 2, 12–13) -/

/-- `W_n^K = per_K G / √(n!)`. -/
noncomputable def normPer {F : Scalar} {n : ℕ} (G : Fin n → Fin n → F.K) : F.K :=
  (Real.sqrt (n ! : ℝ))⁻¹ • perK G

/-- `κ_{n,β} = (n!)^{β/2} π^{-β/2} (β/2)^{βn/2} Γ(β/2) / Γ(βn/2)`, the closed form (22),
p. 12, of `lim_{s→∞} (s/π)^{β/2} E e^{-sΔ_n^K}` (20). -/
noncomputable def kappa (F : Scalar) (n : ℕ) : ℝ :=
  ((n ! : ℝ)) ^ ((F.beta : ℝ) / 2) * Real.pi ^ (-((F.beta : ℝ) / 2)) *
    ((F.beta : ℝ) / 2) ^ ((F.beta : ℝ) * n / 2) * Real.Gamma ((F.beta : ℝ) / 2) /
      Real.Gamma ((F.beta : ℝ) * n / 2)

/-- `ω_β = π^{β/2} / Γ(β/2 + 1)`, the volume of the unit ball of `ℝ^β` (p. 13). -/
noncomputable def omegaBall (F : Scalar) : ℝ :=
  Real.pi ^ ((F.beta : ℝ) / 2) / Real.Gamma ((F.beta : ℝ) / 2 + 1)

end GinibrePermanent977.Anticoncentration


