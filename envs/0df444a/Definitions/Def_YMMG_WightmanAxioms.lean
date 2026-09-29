-- Prove2me | Definitions.Def_YMMG_WightmanAxioms
-- name    : YMMG_WightmanAxioms
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T16:07:51.627986+00:00
-- url     : https://prove2.me/theorems/33033fb5-1b94-4455-8ae8-77bee97c4051
-- title:
--   Wightman axioms R0–R5 and the Euclidean restriction of Wightman distributions
-- statement:
--   The file states axioms **R0–R5** for Wightman distributions $\mathfrak W_n\in\mathcal S'(\mathbb R^{4n})$ of a hermitian scalar field, as listed by Osterwalder–Schrader (§3, following Streater–Wightman p. 117): temperedness ($\mathfrak W_0=1$), invariance under the restricted Poincaré group, positivity, local commutativity, the cluster property, and the spectral condition. With Mathlib's Fourier convention, the spectral condition says that $\widehat{\mathfrak W_n}$ is supported where $k_1+\dots+k_n=0$ and $-(k_1+\dots+k_j)\in\overline V_+$ for $1\le j<n$.
--
--   It also defines the correspondence $\mathfrak S\leftrightarrow\mathfrak W$ used by the reconstruction theorems. For each $n$ there is a function $F$, holomorphic on the forward tube, such that:
--   - $\mathfrak W_n$ is the boundary value of $F$;
--   - $\mathfrak S_n$ is its restriction to the Euclidean points $(ix^0,\vec x)$ with $x_1^0<\dots<x_n^0$.
-- source:
--   K. Osterwalder, R. Schrader, *Axioms for Euclidean Green's Functions*, Commun. Math. Phys. 31, 83–112 (1973), https://doi.org/10.1007/BF01645738, §3 (axioms R0–R5), §4–5 (analytic continuation); R. F. Streater, A. S. Wightman, PCT, Spin and Statistics, and All That (1964), p. 117

module

public import Mathlib
public import Definitions.Def_YMMG_OSAxioms

/-!
# Wightman axioms for Wightman distributions, and the Euclidean ↔ Minkowski correspondence

Axioms `R0`–`R5` for a sequence of Wightman distributions `𝔚ₙ ∈ 𝒮'(ℝ⁴ⁿ)` of a single hermitian
scalar field, as listed in Osterwalder–Schrader (1973), §3 (following Streater–Wightman,
*PCT, Spin and Statistics, and All That*, p. 117).

Conventions (signature `(+,-,-,-)`): `𝔚ₙ(x₁,…,xₙ) = ⟨Ω, φ(x₁)⋯φ(xₙ)Ω⟩`,
`φ(x + a) = U(a) φ(x) U(a)⁻¹`, `U(a) = e^{i(H a⁰ - P⃗·a⃗)}`. The Fourier transform is Mathlib's
`𝓕 g(k) = ∫ e^{-2πi⟨x,k⟩} g(x) dx` (Euclidean pairing of coordinates), and the Fourier transform
of a tempered distribution is `(𝓕𝔚)(g) = 𝔚(𝓕g)`.
-/

@[expose] public section

noncomputable section

namespace YangMillsMassGap

open scoped ComplexOrder FourierTransform
open Filter Topology

/-- Apply the Poincaré transformation `x ↦ Λx + a` to every point. -/
def Config.poincareMove {n : ℕ} (Λ : Matrix (Fin 4) (Fin 4) ℝ) (a : Spacetime) (x : Config n) :
    Config n :=
  Config.mk (fun i => matAct Λ (x.pt i) + a)

/-- `h = fₙ* ⊗ gₘ` pointwise: `h(x₁,…,x_{n+m}) = conj fₙ(xₙ,…,x₁) · gₘ(x_{n+1},…,x_{n+m})`. -/
def IsStarTimes {n m : ℕ} (f : SchwartzMap (Config n) ℂ) (g : SchwartzMap (Config m) ℂ)
    (h : SchwartzMap (Config (n + m)) ℂ) : Prop :=
  ∀ x : Config (n + m),
    h x = (starRingEnd ℂ) (f (Config.mk fun i => x.fst.pt (Fin.rev i))) * g x.snd

/-- The support region of the Fourier transform of `𝔚ₙ` allowed by the spectral condition:
`{k = (k₁,…,kₙ) : k₁ + ⋯ + kₙ = 0 and -(k₁ + ⋯ + k_j) ∈ V̄₊ for 1 ≤ j < n}`.
(With the conventions above this is exactly the statement that, in difference variables
`ξⱼ = xⱼ - x_{j+1}`, the Fourier transform of `𝔚ₙ` is supported in `V̄₊ⁿ⁻¹`.) -/
def spectralSupport (n : ℕ) : Set (Config n) :=
  {k | (∑ i : Fin n, k.pt i) = 0 ∧
    ∀ j : ℕ, 1 ≤ j → j < n → -(∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), k.pt i) ∈ closedForwardCone}

/-- **R0** (temperedness): `𝔚₀ = 1`; each `𝔚ₙ` is a tempered distribution (built into the type). -/
def W_R0 (W : DistributionFamily) : Prop :=
  ∀ f : SchwartzMap (Config 0) ℂ, W 0 f = f 0

/-- **R1** (relativistic invariance): `𝔚ₙ(f) = 𝔚ₙ(f_{(a,Λ)})` for every `Λ ∈ L↑₊` and `a ∈ ℝ⁴`,
where `f_{(a,Λ)}(x₁,…,xₙ) = f(Λx₁ + a, …, Λxₙ + a)`. -/
def W_R1 (W : DistributionFamily) : Prop :=
  ∀ (n : ℕ) (Λ : Matrix (Fin 4) (Fin 4) ℝ) (a : Spacetime) (f g : SchwartzMap (Config n) ℂ),
    Λ ∈ restrictedLorentz → (∀ x, g x = f (x.poincareMove Λ a)) → W n f = W n g

/-- **R2** (positivity): `∑_{n,m} 𝔚_{n+m}(fₙ* ⊗ fₘ) ≥ 0` for every terminating sequence
`(f₀, …, f_N)` of Schwartz functions. -/
def W_R2 (W : DistributionFamily) : Prop :=
  ∀ (N : ℕ) (f : (n : Fin (N + 1)) → SchwartzMap (Config n) ℂ)
    (h : (n m : Fin (N + 1)) → SchwartzMap (Config (n + m)) ℂ),
    (∀ n m, IsStarTimes (f n) (f m) (h n m)) →
    0 ≤ ∑ n : Fin (N + 1), ∑ m : Fin (N + 1), W ((n : ℕ) + m) (h n m)

/-- **R3** (local commutativity): `𝔚ₙ(…, xⱼ, x_{j+1}, …) = 𝔚ₙ(…, x_{j+1}, xⱼ, …)` when
`xⱼ - x_{j+1}` is spacelike; in smeared form, for every test function supported in
`{x : (xⱼ - x_{j+1})² < 0}`. -/
def W_R3 (W : DistributionFamily) : Prop :=
  ∀ (n : ℕ) (j j' : Fin n) (f g : SchwartzMap (Config n) ℂ),
    (j' : ℕ) = j + 1 →
    tsupport f ⊆ {x | IsSpacelike (x.pt j - x.pt j')} →
    (∀ x, g x = f (x.permute (Equiv.swap j j'))) → W n f = W n g

/-- **R4** (cluster property): for spacelike `a`,
`lim_{λ→∞} 𝔚_{n+m}(f ⊗ g_{(λa)}) = 𝔚ₙ(f) 𝔚ₘ(g)`, where
`(f ⊗ g_{(λa)})(x₁,…,x_{n+m}) = f(x₁,…,xₙ) g(x_{n+1} + λa, …, x_{n+m} + λa)`. -/
def W_R4 (W : DistributionFamily) : Prop :=
  ∀ (n m : ℕ) (a : Spacetime) (f : SchwartzMap (Config n) ℂ) (g : SchwartzMap (Config m) ℂ)
    (h : ℝ → SchwartzMap (Config (n + m)) ℂ),
    IsSpacelike a →
    (∀ t x, h t x = f x.fst * g (x.snd.poincareMove 1 (t • a))) →
    Tendsto (fun t : ℝ => W (n + m) (h t)) atTop (𝓝 (W n f * W m g))

/-- **R5** (spectral condition): the Fourier transform of `𝔚ₙ` is supported in
`spectralSupport n`, i.e. `𝔚ₙ(𝓕g) = 0` for every Schwartz `g` whose (closed) support does not meet
`spectralSupport n`. -/
def W_R5 (W : DistributionFamily) : Prop :=
  ∀ (n : ℕ) (g : SchwartzMap (Config n) ℂ),
    Disjoint (tsupport g) (spectralSupport n) → W n (𝓕 g) = 0

/-- Wightman distributions of a hermitian scalar field satisfying `R0`–`R5`. -/
structure SatisfiesWightmanAxioms (W : DistributionFamily) : Prop where
  r0 : W_R0 W
  r1 : W_R1 W
  r2 : W_R2 W
  r3 : W_R3 W
  r4 : W_R4 W
  r5 : W_R5 W

/-- Complexified `n`-point configurations `(z₁,…,zₙ) ∈ (ℂ⁴)ⁿ`. -/
abbrev ComplexConfig (n : ℕ) := Fin n → Fin 4 → ℂ

/-- The imaginary part of a point of `ℂ⁴`, as a point of `ℝ⁴`. -/
def imPart (z : Fin 4 → ℂ) : Spacetime := WithLp.toLp 2 (fun μ => (z μ).im)

/-- The forward tube `{z : Im(z_{j+1}) - Im(zⱼ) ∈ V₊ for 1 ≤ j < n}` (no condition if `n ≤ 1`). -/
def forwardTube (n : ℕ) : Set (ComplexConfig n) :=
  {z | ∀ i j : Fin n, (j : ℕ) = i + 1 → imPart (z j) - imPart (z i) ∈ openForwardCone}

/-- The complex point `x + iεη`. -/
def shiftIm {n : ℕ} (x : Config n) (ε : ℝ) (η : Fin n → Spacetime) : ComplexConfig n :=
  fun i μ => (x (i, μ) : ℂ) + (ε * η i μ : ℝ) * Complex.I

/-- The Euclidean point `(ix⁰, x⃗)` of a Euclidean configuration, as a complex configuration. -/
def wickRotate {n : ℕ} (x : Config n) : ComplexConfig n :=
  fun i μ => if μ = 0 then Complex.I * (x (i, 0) : ℂ) else (x (i, μ) : ℂ)

/-- `S` is the Euclidean restriction of the analytic continuation of `W`
(the correspondence of Osterwalder–Schrader 1973, §4–§5): for every `n` there is a function
`F` holomorphic on the forward tube such that
* `𝔚ₙ` is the boundary value of `F`: `∫ F(x + iεη) f(x) dx → 𝔚ₙ(f)` as `ε → 0⁺`, for every
  `f ∈ 𝒮(ℝ⁴ⁿ)` and every `η` with `η_{j+1} - ηⱼ ∈ V₊`;
* `𝔖ₙ` is the restriction of `F` to Euclidean points:
  `𝔖ₙ(f) = ∫ F(ix₁⁰, x⃗₁, …, ixₙ⁰, x⃗ₙ) f(x) dx` for every `f ∈ ⁰𝒮(ℝ⁴ⁿ)` vanishing with all
  derivatives outside `{x₁⁰ < ⋯ < xₙ⁰}`. -/
def IsEuclideanRestriction (W S : DistributionFamily) : Prop :=
  ∀ n : ℕ, ∃ F : ComplexConfig n → ℂ,
    DifferentiableOn ℂ F (forwardTube n) ∧
    (∀ η : Fin n → Spacetime,
      (∀ i j : Fin n, (j : ℕ) = i + 1 → η j - η i ∈ openForwardCone) →
      ∀ f : SchwartzMap (Config n) ℂ,
        Tendsto (fun ε : ℝ => ∫ x, F (shiftIm x ε η) * f x) (𝓝[>] 0) (𝓝 (W n f))) ∧
    (∀ f : SchwartzMap (Config n) ℂ, VanishesOnCoincidences f →
      DerivsVanishOutside f (timeOrdered n) → S n f = ∫ x, F (wickRotate x) * f x)

end YangMillsMassGap

end


