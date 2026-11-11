-- Prove2me | Definitions.Def_ApproxSyzygies_Smoothed_Bombieri
-- name    : ApproxSyzygies_Smoothed_Bombieri
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:02:12.411799+00:00
-- url     : https://prove2.me/theorems/c2e2aaae-64cf-4d78-9ea8-cc167cce410f
-- title:
--   Homogeneous polynomial spaces $\mathbb R[x]_{=d}$ with the Bombieri inner product, multiplication maps, syzygies, Koszul syzygies, gradations and the smoothed model
-- statement:
--   Variables are indexed by a finite set $\sigma$ ($x=(x_1,\dots,x_n)$, or $x=(y,z)$ for a coordinate split, variables `Y ⊕ Z`). For an integer $d$, $\mathbb R[x]_{=d}$ is the space of homogeneous real polynomials of degree $d$, with the convention $\mathbb R[x]_{=d}=\{0\}$ for $d<0$ and $\mathbb R[x]_{=0}=\mathbb R$.
--
--   **Bombieri inner product.** Distinct monomials are orthogonal and $\langle x^\alpha,x^\alpha\rangle=\alpha!/d!$ for $|\alpha|=d$, $\alpha!=\prod_i\alpha_i!$. Equivalently, writing $p=\sum_{|\alpha|=d}p_\alpha\sqrt{d!/\alpha!}\,x^\alpha$,
--   $$\|p\|^2=\sum_{|\alpha|=d}p_\alpha^2 .$$
--   `Hom σ d` is the Euclidean space of coordinate vectors $(p_\alpha)_{|\alpha|=d}$ (empty index set for $d<0$); `toPoly` gives the polynomial and `ofPoly d f` reads the coefficients of a polynomial $f$ in degree $d$, so $\|$`ofPoly d f`$\|$ is the Bombieri norm of $f\in\mathbb R[x]_{=d}$. A tuple $h=(h_1,\dots,h_m)\in\bigoplus_i\mathbb R[x]_{=e_i}$ (`Tup σ e`) carries the product norm $\|h\|^2=\sum_i\|h_i\|^2$; `tupNorm p` is this norm of a family $p$.
--
--   **Multiplication map and syzygies (Definition 3.1).** For $p_i\in\mathbb R[x]_{=e_i}$, $M^{(t)}_p:\bigoplus_i\mathbb R[x]_{=t-e_i}\to\mathbb R[x]_{=t}$, $h\mapsto\sum_ip_ih_i$ (`mulMap p t`), and $\mathrm{Syz}^{(t)}_p=\ker M^{(t)}_p$ (`syz`).
--
--   **Koszul syzygies (Definition 3.2).** $\mathcal K^{(t)}_p$ (`koszul p t`) is the set of $h$ with $h_i=\sum_j\Omega_{ij}p_j$ for some $\Omega_{ij}=-\Omega_{ji}\in\mathbb R[x]_{=t-e_i-e_j}$ (zero when $t-e_i-e_j<0$). $\mathrm{dist}(h,E)=\inf_{h'\in E}\|h-h'\|$ is `Metric.infDist`.
--
--   **Powers, gradation, ideals.** `powHom a D` $=a^D\in\mathbb R[x]_{=dD}$. For $x=(y,z)$, $f[r]$ (`grade r f`) is the sum of the terms of $z$-degree $r$, $f[0:r]=(f[0],\dots,f[r])$ (`gradeSeg`), $f[0]$ as a polynomial in $y$ is `yPart f` ($z\mapsto0$), `liftY`, `liftZ` embed $\mathbb R[y]$, $\mathbb R[z]$ into $\mathbb R[y,z]$. `idealDeg p s` $=\langle p_1,\dots,p_m\rangle_{=s}$ is the image of $M^{(s)}_p$; `pinvNorm M` is the operator norm of the Moore–Penrose pseudoinverse of $M$ (the least $\tau\ge0$ with $\|u\|\le\tau\|Mu\|$ for $u\perp\ker M$), and `tauOf p₀ t` $=\max_{0\le s<t}\|W^{(s)}_{p}[0]\|_{op}$. `KernelCond p₀ t` says $\ker M^{(s)}_{p}[0]=\mathcal K^{(s)}_{p}[0]$ for $0\le s<t$. For the proof of Theorem 4.1: `modGen d D i c a` is $\tilde b^{(i)}$ ($c$ in slot $i$, $b_j=a_j^{D_j}$ elsewhere), `Jpiece` is $J_i=\langle b_1[0],\dots,a_i[0],\dots,b_m[0]\rangle_{t-d_iD_i}$, and `gVec` is $g$, $g_i=\Pi^\perp_{J_i}h_i[0]$.
--
--   **Smoothed polynomials.** A $\rho$-perturbed polynomial with center $\bar a\in\mathbb R[x]_{=d}$ is $a=\bar a+\rho\sum_{|\alpha|=d}\zeta_\alpha\sqrt{d!/\alpha!}\,x^\alpha$ with independent $\zeta_\alpha\sim N(0,1)$ (`perturb`): every Bombieri-normalised coefficient is perturbed by $N(0,\rho^2)$. `gaussCoeffs n m d` is the product law of all $\zeta_{i,\alpha}$ for $m$ independent polynomials.
--
--   **Formalization Note.** Degrees are integers, so $\mathbb R[x]_{=t-d_iD_i}$ is the zero space when $t<d_iD_i$ (no truncated subtraction). `pinvNorm` is an infimum over a nonempty set bounded below by $0$ in finite dimension.
-- source:
--   Bhaskara, Guo, Sinha, Srinivas, Vijayaraghavan, Approximate Syzygies of Smoothed Polynomials and Applications, STOC 2027 submission (manuscript sha256 9c17d04e…), pp. 16-17 (§3, Definitions 3.1, 3.2), pp. 19-20 (§4.1), p. 29 (§4.4)

import Mathlib

open MvPolynomial MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed

/-! ### Homogeneous polynomial spaces `ℝ[x]_{=d}` with the Bombieri inner product

Bhaskara, Guo, Sinha, Srinivas, Vijayaraghavan, *Approximate Syzygies of Smoothed Polynomials
and Applications*, STOC 2027 submission, §3 (pp. 16–17).

The variables are indexed by a finite type `σ` (`Fin n` for `x = (x_1, …, x_n)`, `Y ⊕ Z` for a
coordinate split `x = (y, z)`). Degrees are integers: `ℝ[x]_{=d} = {0}` for `d < 0` is built in,
because there are no multi-indices of negative total degree. -/

/-- The multi-indices `α ∈ ℤ_{≥0}^σ` with `|α| = d`; empty when `d < 0`. -/
noncomputable def monos (σ : Type*) [Fintype σ] [DecidableEq σ] (d : ℤ) : Finset (σ →₀ ℕ) :=
  if 0 ≤ d then Finset.finsuppAntidiag Finset.univ d.toNat else ∅

/-- `ℝ[x]_{=d}` in the coordinates of the Bombieri-orthonormal basis `√(d!/α!) x^α`, `|α| = d`.
A vector `p = (p_α)` stands for the polynomial `∑_α p_α √(d!/α!) x^α` (`toPoly`), so the
Euclidean inner product of `Hom σ d` is the Bombieri inner product `⟨x^α, x^α⟩ = α!/d!`
(distinct monomials orthogonal) and its norm is the Bombieri norm. `Hom σ d = 0` for `d < 0`. -/
abbrev Hom (σ : Type*) [Fintype σ] [DecidableEq σ] (d : ℤ) :=
  EuclideanSpace ℝ (monos σ d)

/-- `α! = ∏_i α_i!`. -/
noncomputable def mfact {σ : Type*} [Fintype σ] (α : σ →₀ ℕ) : ℝ :=
  ∏ i, ((α i).factorial : ℝ)

/-- The Bombieri-normalised monomial `√(|α|!/α!) x^α`. -/
noncomputable def bmono {σ : Type*} [Fintype σ] (α : σ →₀ ℕ) : MvPolynomial σ ℝ :=
  monomial α (Real.sqrt (((Finsupp.degree α).factorial : ℝ) / mfact α))

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The polynomial `∑_{|α| = d} p_α √(d!/α!) x^α` represented by `p ∈ Hom σ d`. -/
noncomputable def toPoly {d : ℤ} (p : Hom σ d) : MvPolynomial σ ℝ :=
  ∑ α : monos σ d, p α • bmono (α : σ →₀ ℕ)

/-- `toPoly` as a linear map. -/
noncomputable def toPolyL (d : ℤ) : Hom σ d →ₗ[ℝ] MvPolynomial σ ℝ where
  toFun := toPoly
  map_add' p q := by
    simp [toPoly, add_smul, Finset.sum_add_distrib]
  map_smul' c p := by
    simp [toPoly, Finset.smul_sum, smul_smul]

/-- The degree-`d` part of a polynomial `f`, read in Bombieri-orthonormal coordinates:
`(ofPoly d f)_α = f_α √(α!/d!)` for `|α| = d`, where `f_α` is the coefficient of `x^α`.
For `f ∈ ℝ[x]_{=d}`, `toPoly (ofPoly d f) = f`, and `‖ofPoly d f‖` is the Bombieri norm of `f`. -/
noncomputable def ofPoly (d : ℤ) (f : MvPolynomial σ ℝ) : Hom σ d :=
  WithLp.toLp 2 fun α => coeff (α : σ →₀ ℕ) f * Real.sqrt (mfact (α : σ →₀ ℕ) / (d.toNat.factorial : ℝ))

/-- `ofPoly d` as a linear map. -/
noncomputable def ofPolyL (d : ℤ) : MvPolynomial σ ℝ →ₗ[ℝ] Hom σ d where
  toFun := ofPoly d
  map_add' f g := by
    ext α
    simp [ofPoly, add_mul]
  map_smul' c f := by
    ext α
    simp [ofPoly, mul_assoc]

/-- The subspace `ℝ[x]_{=d}` of `ℝ[x]` (the image of `toPoly`; it is `{0}` for `d < 0`). -/
noncomputable def homSpace (σ : Type*) [Fintype σ] [DecidableEq σ] (d : ℤ) :
    Submodule ℝ (MvPolynomial σ ℝ) :=
  LinearMap.range (toPolyL (σ := σ) d)

/-- A tuple `(h_1, …, h_m) ∈ ⨁_i ℝ[x]_{=e_i}` with the product Bombieri norm
`‖h‖² = ∑_i ‖h_i‖²`. -/
abbrev Tup (σ : Type*) [Fintype σ] [DecidableEq σ] {m : ℕ} (e : Fin m → ℤ) :=
  PiLp 2 fun i : Fin m => Hom σ (e i)

/-! ### Multiplication maps, syzygies and Koszul syzygies (Definitions 3.1 and 3.2, pp. 17–18) -/

/-- The polynomial `∑_i p_i h_i`. -/
noncomputable def mulSum {m : ℕ} {e e' : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) (h : Tup σ e') :
    MvPolynomial σ ℝ :=
  ∑ i, toPoly (p i) * toPoly (h i)

/-- Definition 3.1: the multiplication map `M_p^{(t)} : ⨁_i ℝ[x]_{=t - deg p_i} → ℝ[x]_{=t}`,
`(h_1, …, h_m) ↦ ∑_i p_i h_i`, for generators `p_i ∈ ℝ[x]_{=e_i}`. -/
noncomputable def mulMap {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) (t : ℤ) :
    Tup σ (fun i => t - e i) →ₗ[ℝ] Hom σ t :=
  ∑ i, (ofPolyL t) ∘ₗ (LinearMap.mulLeft ℝ (toPoly (p i))) ∘ₗ (toPolyL (t - e i)) ∘ₗ
    (PiLp.projₗ 2 (fun i : Fin m => Hom σ (t - e i)) i)

/-- Definition 3.1: the degree-`t` syzygy space `Syz_p^{(t)} = ker M_p^{(t)}`. -/
noncomputable def syz {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) (t : ℤ) :
    Submodule ℝ (Tup σ (fun i => t - e i)) :=
  LinearMap.ker (mulMap p t)

/-- Definition 3.2: the degree-`t` Koszul syzygies of `p = (p_1, …, p_m)`, `p_i ∈ ℝ[x]_{=e_i}`:
the tuples `(h_1, …, h_m)` with `h_i = ∑_j Ω_{ij} p_j` for some `Ω_{ij} = −Ω_{ji} ∈ ℝ[x]_{=t−e_i−e_j}`
(`Ω_{ij} = 0` when `t − e_i − e_j < 0`). -/
def koszul {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) (t : ℤ) :
    Set (Tup σ (fun i => t - e i)) :=
  {h | ∃ Ω : Fin m → Fin m → MvPolynomial σ ℝ,
    (∀ i j, Ω i j ∈ homSpace σ (t - e i - e j)) ∧ (∀ i j, Ω i j = -Ω j i) ∧
    ∀ i, toPoly (h i) = ∑ j, Ω i j * toPoly (p j)}

/-- The power `a^D ∈ ℝ[x]_{=dD}` of `a ∈ ℝ[x]_{=d}`. -/
noncomputable def powHom {d : ℤ} (a : Hom σ d) (D : ℕ) : Hom σ (d * D) :=
  ofPoly (d * D) (toPoly a ^ D)

/-! ### Gradations for a coordinate split `x = (y, z)` (§3, p. 18) -/

section Gradation

variable {Y Z : Type*} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- The `z`-degree `∑_{z} α_z` of a multi-index on `Y ⊕ Z`. -/
def zdeg (α : (Y ⊕ Z) →₀ ℕ) : ℕ := ∑ z : Z, α (Sum.inr z)

/-- The gradation piece `f[r]`: the sum of the terms of `f` of `z`-degree exactly `r`. -/
noncomputable def grade (r : ℕ) {d : ℤ} (f : Hom (Y ⊕ Z) d) : Hom (Y ⊕ Z) d :=
  WithLp.toLp 2 fun α => if zdeg (α : (Y ⊕ Z) →₀ ℕ) = r then f α else 0

/-- `h[r]` for a tuple, coordinatewise. -/
noncomputable def gradeTup (r : ℕ) {m : ℕ} {e : Fin m → ℤ} (h : Tup (Y ⊕ Z) e) : Tup (Y ⊕ Z) e :=
  WithLp.toLp 2 fun i => grade r (h i)

/-- `f[0 : r] = (f[0], …, f[r])`, with the product norm. -/
noncomputable def gradeSeg (r : ℕ) {d : ℤ} (f : Hom (Y ⊕ Z) d) :
    PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) d :=
  WithLp.toLp 2 fun r' => grade (r' : ℕ) f

/-- The pure-`y` part `f[0]` as a polynomial in `y` alone (`z` set to `0`). -/
noncomputable def yPart {d : ℤ} (f : Hom (Y ⊕ Z) d) : Hom Y d :=
  ofPoly d (aeval (Sum.elim X (fun _ : Z => (0 : MvPolynomial Y ℝ))) (toPoly f))

/-- `h[0]` for a tuple, as a tuple of polynomials in `y`. -/
noncomputable def yPartTup {m : ℕ} {e : Fin m → ℤ} (h : Tup (Y ⊕ Z) e) : Tup Y e :=
  WithLp.toLp 2 fun i => yPart (h i)

/-- A polynomial in `y` regarded as a polynomial in `x = (y, z)`. -/
noncomputable def liftY {d : ℤ} (u : Hom Y d) : Hom (Y ⊕ Z) d :=
  ofPoly d (rename Sum.inl (toPoly u))

/-- A polynomial in `z` regarded as a polynomial in `x = (y, z)`. -/
noncomputable def liftZ {d : ℤ} (u : Hom Z d) : Hom (Y ⊕ Z) d :=
  ofPoly d (rename Sum.inr (toPoly u))

end Gradation

/-! ### Pseudoinverse norms and ideal pieces (§4.1, p. 20) -/

/-- The operator norm `‖W‖_op` of the Moore–Penrose pseudoinverse `W` of a linear map `M`
between finite-dimensional inner product spaces: the least `τ ≥ 0` with `‖u‖ ≤ τ ‖M u‖` for
every `u ⊥ ker M` (it is `0` when `M = 0`, and `1 / σ_min⁺(M)` otherwise). -/
noncomputable def pinvNorm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (M : E →ₗ[ℝ] F) : ℝ :=
  sInf {τ : ℝ | 0 ≤ τ ∧ ∀ u ∈ (LinearMap.ker M)ᗮ, ‖u‖ ≤ τ * ‖M u‖}

/-- `τ = max_{0 ≤ s < t} ‖W_p^{(s)}[0]‖_op` for generators `p_i ∈ ℝ[y]_{=e_i}` (the pure-`y`
parts), with `W_p^{(s)}[0]` the pseudoinverse of `M_p^{(s)}[0]`. It is `0` for `t = 0`. -/
noncomputable def tauOf {Y : Type*} [Fintype Y] [DecidableEq Y] {m : ℕ} {e : Fin m → ℤ}
    (p : ∀ i, Hom Y (e i)) (t : ℕ) : ℝ :=
  ⨆ s : Fin t, pinvNorm (mulMap p (s : ℤ))

/-- The degree-`s` ideal `⟨p_1, …, p_m⟩_{=s} = I_p^{(s)}`, the image of `M_p^{(s)}`. -/
noncomputable def idealDeg {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) (s : ℤ) :
    Submodule ℝ (Hom σ s) :=
  LinearMap.range (mulMap p s)

/-! ### The objects of the proof of Theorem 4.1 (§4.1, pp. 19–20; §4.4, p. 29) -/

/-- The product Bombieri norm `‖p‖ = (∑_i ‖p_i‖²)^{1/2}` of a family of homogeneous
polynomials of possibly different degrees. -/
noncomputable def tupNorm {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) : ℝ :=
  ‖(WithLp.toLp 2 p : Tup σ e)‖

/-- `p[0] = (p_1[0], …, p_m[0])`, the pure-`y` parts of a family over `x = (y, z)`. -/
noncomputable def yParts {Y Z : Type*} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom (Y ⊕ Z) (e i)) : ∀ i, Hom Y (e i) :=
  fun i => yPart (p i)

/-- The kernel condition of Lemma 4.3 for a family `p[0]` over `y`: `ker M_p^{(s)}[0] = K_p^{(s)}[0]`
for every `0 ≤ s < t` (`K_p^{(s)}[0]` is the Koszul syzygy space of `p[0]` over `ℝ[y]`). -/
def KernelCond {m : ℕ} {e : Fin m → ℤ} (p₀ : ∀ i, Hom σ (e i)) (t : ℕ) : Prop :=
  ∀ s : ℕ, s < t → (LinearMap.ker (mulMap p₀ (s : ℤ)) : Set (Tup σ (fun i => (s : ℤ) - e i))) =
    koszul p₀ (s : ℤ)

/-- The degrees of the modified family `b̃^{(i)}`: `d_i` in slot `i`, `d_j D_j` in slot `j ≠ i`. -/
def modDeg {m : ℕ} (d D : Fin m → ℕ) (i j : Fin m) : ℤ :=
  if j = i then (d j : ℤ) else (d j : ℤ) * (D j : ℤ)

/-- The modified family `b̃^{(i)} = (a_1^{D_1}, …, a_{i−1}^{D_{i−1}}, c, a_{i+1}^{D_{i+1}}, …)`:
the polynomial `c` in slot `i` (of degree `d_i`) and `b_j = a_j^{D_j}` in every slot `j ≠ i`. -/
noncomputable def modGen {m : ℕ} (d D : Fin m → ℕ) (i : Fin m) (c : MvPolynomial σ ℝ)
    (a : ∀ j, Hom σ (d j : ℤ)) : ∀ j, Hom σ (modDeg d D i j) :=
  fun j => ofPoly (modDeg d D i j) (if j = i then c else toPoly (a j) ^ D j)

/-- The ideal piece `J_i = ⟨b_1[0], …, b_{i−1}[0], a_i[0], b_{i+1}[0], …, b_m[0]⟩_{t − d_i D_i}
⊆ ℝ[y]_{=t − d_i D_i}`, for the pure-`y` parts `a₀ = (a_1[0], …, a_m[0])` and `b_j[0] = a_j[0]^{D_j}`. -/
noncomputable def Jpiece {Y : Type*} [Fintype Y] [DecidableEq Y] {m : ℕ} (d D : Fin m → ℕ)
    (t : ℕ) (a₀ : ∀ j, Hom Y (d j : ℤ)) (i : Fin m) :
    Submodule ℝ (Hom Y ((t : ℤ) - (d i : ℤ) * (D i : ℤ))) :=
  idealDeg (modGen d D i (toPoly (a₀ i)) a₀) ((t : ℤ) - (d i : ℤ) * (D i : ℤ))

/-- The important part `g = (g_1, …, g_m)`, `g_i = Π^⊥_{J_i} h_i[0]`, of the pure-`y` part
`h₀ = h[0]` of a coefficient vector. -/
noncomputable def gVec {Y : Type*} [Fintype Y] [DecidableEq Y] {m : ℕ} (d D : Fin m → ℕ)
    (t : ℕ) (a₀ : ∀ j, Hom Y (d j : ℤ))
    (h₀ : Tup Y (fun i => (t : ℤ) - (d i : ℤ) * (D i : ℤ))) :
    Tup Y (fun i => (t : ℤ) - (d i : ℤ) * (D i : ℤ)) :=
  WithLp.toLp 2 fun i => (Jpiece d D t a₀ i)ᗮ.starProjection (h₀ i)

/-! ### Smoothed polynomials (§3, p. 17) -/

/-- The law of the standard Gaussian coefficients of `m` smoothed polynomials of degrees
`d_1, …, d_m` in `n` variables: one independent `N(0, 1)` for every `i` and every multi-index
`α` with `|α| = d_i`. -/
noncomputable def gaussCoeffs (n m : ℕ) (d : Fin m → ℤ) :
    Measure ((i : Fin m) → monos (Fin n) (d i) → ℝ) :=
  Measure.pi fun i => Measure.pi fun _ : monos (Fin n) (d i) => gaussianReal 0 1

/-- The `ρ`-perturbed polynomial with center `ā ∈ ℝ[x]_{=d}` and standard Gaussian coefficients
`ζ`: `a = ā + ∑_{|α| = d} ρ ζ_α √(d!/α!) x^α`, i.e. every Bombieri-normalised coefficient of
`ā` is perturbed by an independent `N(0, ρ²)`. -/
noncomputable def perturb {n : ℕ} {d : ℤ} (abar : Hom (Fin n) d) (ρ : ℝ)
    (ζ : monos (Fin n) d → ℝ) : Hom (Fin n) d :=
  abar + ρ • WithLp.toLp 2 ζ

end ApproxSyzygies.Smoothed


