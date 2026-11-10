-- Prove2me | Definitions.Def_SliceLinearity_Tests_BiasedAnalysis
-- name    : SliceLinearity_Tests_BiasedAnalysis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:38:01.316898+00:00
-- url     : https://prove2.me/theorems/287abf9a-b8a7-4509-a5ff-0ca8600fb63b
-- title:
--   Characters, the $p$-biased measure $\mu_p$, $\mu_p^\circ$, weighted inner products, Fourier coefficients and biased Krawtchouk polynomials on $\mathbb F_2^n$
-- statement:
--   Measures on $\mathbb F_2^n$ are real weight functions.
--
--   1. **Characters.** $\chi_\xi(x)=(-1)^{\langle\xi,x\rangle}$ for $\xi\in\mathbb F_2^n$ (Definition 2.2). Following §6, characters and unweighted Fourier expansions are on the ambient cube.
--   2. **Biased measures.** $\mu_p=\mathrm{Ber}(p)^{\otimes n}$ gives $x$ the weight $\prod_i p^{x_i}(1-p)^{1-x_i}$. $H_{\rm even}=\{x:\sum_ix_i=0\}$ is the even-weight subspace, and $\mu_p^\circ=\mu_p(\,\cdot\mid H_{\rm even})$. $\nu$ uniform on a set $S$ gives each point of $S$ the weight $1/\#S$.
--   3. **Inner products and norms** (Definition 2.1). $\langle f,g\rangle_\mu=\mathbb E_{x\sim\mu}[f(x)\overline{g(x)}]$ and $\|f\|_{2,\mu}=(\mathbb E_{x\sim\mu}|f(x)|^2)^{1/2}$, for real or complex functions. $\max_\chi|\langle f,\chi\rangle_\mu|$ is the largest character correlation.
--   4. **Fourier coefficients.** $\hat g(\chi_\xi)=\mathbb E_{x\sim\mathbb F_2^n}[g(x)\chi_\xi(x)]$ and $\|\hat g\|_{\ell_1}=\sum_\xi|\hat g(\chi_\xi)|$. For a measure, $\hat\nu(\chi)=\langle1,\chi\rangle_\nu$.
--   5. **Agreement under a measure.** $\mathrm{agr}_\mu(f,g)=\Pr_{x\sim\mu}[f(x)=g(x)]$, together with its maximum over affine maps.
--   6. **Ignored coordinates.** $g$ ignores $B\subseteq[n]$ if $g(x)$ does not depend on $x_i$ for $i\in B$.
--   7. **Biased Krawtchouk polynomials** (Definition 6.8). $K_j(|z|)=\binom nj^{-1/2}\sum_{|B|=j}\prod_{i\in B}\frac{z_i-p}{\sqrt{p(1-p)}}$. These are orthonormal under $\mu_p$.
--
--   **Formalization Note** The inner product is written once for any `RCLike` scalar field ($\mathbb R$ or $\mathbb C$). Maxima over characters are `Finset.sup'` over the nonempty finite cube, so they are true maxima. $\mu_p^\circ$ divides by $\mu_p(H_{\rm even})=(1+(1-2p)^n)/2$, which is positive for $0<p<1$.
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §2 pp. 8–10 (PDF 10–12): Definitions 2.1, 2.2, 2.4; §6 p. 36 (PDF 38); §6.2 pp. 42–44 (PDF 44–46): μ°_p, Definition 6.8

import Mathlib
import Definitions.Def_SliceLinearity_Tests_SliceTests

set_option autoImplicit false

namespace SliceLinearity.Tests

/-! # Characters, biased measures, weighted inner products and Fourier coefficients on `F₂ⁿ`

Aydin, Larsen, Mittal, Richelson, Roy, *Low Soundness Linearity Testing on Subsets of the Hypercube*,
STOC 2027 submission (manuscript sha256 457be236…), §2 pp. 8–10 (PDF 10–12, Definitions 2.1, 2.2,
2.4), §6 p. 36 (PDF 38), §6.2 pp. 42–44 (PDF 44–46, Definition 6.8).

Measures on the cube are real weight functions `μ : Cube n → ℝ`. Characters `χ_ξ(x) = (−1)^{⟨ξ,x⟩}`
and unweighted Fourier expansions are on the ambient cube (§6). -/

/-- The character `χ_ξ(x) = (−1)^{⟨ξ, x⟩}` of `F₂ⁿ`, as a real number `±1`. -/
def chi {n : ℕ} (ξ x : Cube n) : ℝ :=
  if linMap ξ x = 0 then 1 else -1

/-- `μ` is a probability distribution on the finite type `α`. -/
def IsDistW {α : Type*} [Fintype α] (μ : α → ℝ) : Prop :=
  (∀ a, 0 ≤ μ a) ∧ ∑ a, μ a = 1

/-- The Bernoulli(`p`) law of one bit. -/
def bitBer (p : ℝ) (b : ZMod 2) : ℝ :=
  if b = 1 then p else 1 - p

/-- The `p`-biased product measure `μ_p = Ber(p)^{⊗n}`. -/
noncomputable def muP (p : ℝ) {n : ℕ} (x : Cube n) : ℝ :=
  ∏ i, bitBer p (x i)

/-- The even-weight subspace `H_even = {x : ∑ᵢ xᵢ = 0}` of `F₂ⁿ`. -/
def evenCube (n : ℕ) : Finset (Cube n) :=
  Finset.univ.filter fun x => ∑ i, x i = 0

/-- The mass `μ(S)` of a set. -/
noncomputable def massOn {n : ℕ} (μ : Cube n → ℝ) (S : Finset (Cube n)) : ℝ :=
  ∑ x ∈ S, μ x

/-- `μ°_p = μ_p( · | H_even)`, the `p`-biased measure conditioned on even weight. -/
noncomputable def muPEven (p : ℝ) {n : ℕ} (x : Cube n) : ℝ :=
  if x ∈ evenCube n then muP p x / massOn (muP p) (evenCube n) else 0

/-- The uniform distribution on a finite set `S` (e.g. `ν` uniform on a slice). -/
noncomputable def unifOn {n : ℕ} (S : Finset (Cube n)) (x : Cube n) : ℝ :=
  if x ∈ S then 1 / (S.card : ℝ) else 0

/-- `E_{x∼μ}[g(x)]` for a real function. -/
noncomputable def expW {n : ℕ} (μ : Cube n → ℝ) (g : Cube n → ℝ) : ℝ :=
  ∑ x, μ x * g x

/-- `⟨f, g⟩_μ = E_{x∼μ}[f(x) · conj(g(x))]` (Definition 2.1), for real or complex functions. -/
noncomputable def innerW {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (μ : Cube n → ℝ) (f g : Cube n → 𝕜) : 𝕜 :=
  ∑ x, (μ x : 𝕜) * f x * (starRingEnd 𝕜) (g x)

/-- `‖f‖_{2,μ} = (E_{x∼μ}|f(x)|²)^{1/2}` (Definition 2.1). -/
noncomputable def norm2W {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (μ : Cube n → ℝ) (f : Cube n → 𝕜) : ℝ :=
  Real.sqrt (∑ x, μ x * ‖f x‖ ^ 2)

/-- `max_χ |⟨f, χ⟩_μ|`, the largest character correlation of `f` under `μ`. -/
noncomputable def maxCorr {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (μ : Cube n → ℝ) (f : Cube n → 𝕜) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun ξ : Cube n => ‖innerW μ f (fun x => (chi ξ x : 𝕜))‖

/-- The unweighted Fourier coefficient `ĝ(χ_ξ) = E_{x ∼ F₂ⁿ}[g(x) χ_ξ(x)]` on the ambient cube. -/
noncomputable def fourierCoeff {n : ℕ} (g : Cube n → ℝ) (ξ : Cube n) : ℝ :=
  (∑ x, g x * chi ξ x) / (2 : ℝ) ^ n

/-- `‖ĝ‖_{ℓ1} = ∑_χ |ĝ(χ)|`. -/
noncomputable def fourierL1 {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  ∑ ξ, |fourierCoeff g ξ|

/-- The Fourier coefficient of a measure, `ν̂(χ) = ⟨1, χ⟩_ν = E_{x∼ν}[χ(x)]` (Definition 2.2). -/
noncomputable def measFourier {n : ℕ} (ν : Cube n → ℝ) (ξ : Cube n) : ℝ :=
  ∑ x, ν x * chi ξ x

/-- Agreement under a measure, `agr_μ(f, g) = Pr_{x∼μ}[f(x) = g(x)]` (Definition 2.4). -/
noncomputable def agrW {n : ℕ} (μ : Cube n → ℝ) (f g : Cube n → ZMod 2) : ℝ :=
  ∑ x, μ x * if f x = g x then 1 else 0

/-- `max_{χ, σ} agr_μ(f, σχ)`: the best agreement under `μ` with an affine map (signed character). -/
noncomputable def maxAffAgrW {n : ℕ} (μ : Cube n → ℝ) (f : Cube n → ZMod 2) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun ac : Cube n × ZMod 2 => agrW μ f (affMap ac.1 ac.2)

/-- `g` ignores the coordinates in `B`: its value does not depend on them. -/
def IgnoresCoords {n : ℕ} {β : Type*} (g : Cube n → β) (B : Finset (Fin n)) : Prop :=
  ∀ x y : Cube n, (∀ i, i ∉ B → x i = y i) → g x = g y

/-- The `p`-biased Krawtchouk polynomial (Definition 6.8), as a function of `z ∈ F₂ⁿ`:
`K_j(|z|) = C(n,j)^{−1/2} ∑_{|B|=j} ∏_{i∈B} (zᵢ − p)/√(p(1−p))`, with `zᵢ ∈ {0,1}` read as a real. -/
noncomputable def krawtchouk (p : ℝ) (n j : ℕ) (z : Cube n) : ℝ :=
  Real.sqrt ((n.choose j : ℝ))⁻¹ *
    ∑ B ∈ Finset.powersetCard j (Finset.univ : Finset (Fin n)),
      ∏ i ∈ B, (((z i).val : ℝ) - p) / Real.sqrt (p * (1 - p))

end SliceLinearity.Tests


