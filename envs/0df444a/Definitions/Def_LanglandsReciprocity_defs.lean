-- Prove2me | Definitions.Def_LanglandsReciprocity_defs
-- name    : LanglandsReciprocity_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T01:53:15.009095+00:00
-- url     : https://prove2.me/theorems/50ff14ce-f5cc-4659-ac6b-7797f01385a6
-- title:
--   Artin representations, cusp forms on $\mathrm{GL}_n(\mathbb A_K)$, Hecke eigenvalues and the reciprocity correspondence
-- statement:
--   This file sets up both sides of the Langlands reciprocity conjecture for $\mathrm{GL}(n)$ over a number field $K$.
--
--   **Galois side.**
--   1. $G_K=\mathrm{Gal}(\bar K/K)$ with the Krull topology; an Artin representation is a continuous homomorphism $\rho:G_K\to\mathrm{GL}_n(\mathbb C)$.
--   2. `IsIrreducible ρ`: $n\ge 1$ and the only $\rho(G_K)$-stable subspaces of $\mathbb C^n$ are $0$ and $\mathbb C^n$.
--   3. For a maximal ideal $\mathfrak p$ of $\mathcal O_K$ with norm $N\mathfrak p=\#(\mathcal O_K/\mathfrak p)$ and a prime $\mathfrak P$ of the ring $\mathcal O_{\bar K}$ of algebraic integers of $\bar K$ lying over $\mathfrak p$: $\sigma$ is in the inertia group of $\mathfrak P$ if $\sigma x\equiv x \pmod{\mathfrak P}$ for all $x\in\mathcal O_{\bar K}$, and $\sigma$ is an (arithmetic) Frobenius element at $\mathfrak P$ if $\sigma x\equiv x^{N\mathfrak p}\pmod{\mathfrak P}$ for all $x$.
--   4. `IsUnramifiedAt ρ 𝔭`: $\rho$ is trivial on every inertia group above $\mathfrak p$; `eigenvalues A` is the multiset of roots of the characteristic polynomial of $A$.
--
--   **Automorphic side.**
--   1. `IsCuspForm φ`: $\varphi:\mathrm{GL}_n(\mathbb A_K)\to\mathbb C$ is continuous and bounded, $\varphi(\gamma g)=\varphi(g)$ for $\gamma\in\mathrm{GL}_n(K)$, $\varphi(zg)=\omega(z)\varphi(g)$ for central $z\in\mathbb A_K^\times$ and some unitary $\omega$, and all constant terms $\int_{N_r(K)\backslash N_r(\mathbb A_K)}\varphi(ug)\,du$ vanish ($0<r<n$, $N_r$ the unipotent radical of the standard parabolic of type $(r,n-r)$). The integral is taken over any measurable fundamental domain for $N_r(K)$ in $N_r(\mathbb A_K)\cong\mathbb A_K^{r(n-r)}$, with respect to any Haar measure.
--   2. `maxCompactAt n 𝔭` is $\mathrm{GL}_n(\mathcal O_{\mathfrak p})$ placed at the $\mathfrak p$-component of $\mathrm{GL}_n(\mathbb A_K)$; `heckeDoubleCoset n 𝔭 i` is $\mathrm{GL}_n(\mathcal O_{\mathfrak p})\,\mathrm{diag}(\varpi^{(i)},1^{(n-i)})\,\mathrm{GL}_n(\mathcal O_{\mathfrak p})$, described via the Cartan decomposition: $A$ and $\varpi A^{-1}$ are integral and $\det A\in\varpi^i\mathcal O_{\mathfrak p}^\times$.
--   3. `IsSphericalHeckeEigen φ 𝔭 λ`: $\varphi$ is right $\mathrm{GL}_n(\mathcal O_{\mathfrak p})$-invariant and $\sum_{r\in R}\varphi(gr)=\lambda_i\,\varphi(g)$ for every finite system $R$ of representatives of the left cosets in the $i$-th double coset, $1\le i\le n$.
--
--   **Correspondence.** `Corresponds ρ φ` holds when $\varphi\neq 0$ is such a cusp form and, outside a finite set $S$ of primes, $\rho$ is unramified and $\varphi$ is a spherical Hecke eigenfunction with eigenvalues $N\mathfrak p^{i(n-i)/2}e_i(\rho(\sigma))$ for every Frobenius element $\sigma$ above $\mathfrak p$. `IsAutomorphic ρ` means some $\varphi$ corresponds to $\rho$.
--
--   These definitions are the common language of every statement in the mission.
--
--   **Formalization Note** The adele ring is Mathlib's `AdeleRing (𝓞 K) K`, and $\mathrm{GL}_n(\mathbb A_K)$ carries the unit-group topology, which agrees with the restricted-product topology. With the Hecke operator $\varphi\mapsto\sum_x\varphi(gx)$, the eigenvalue of $T_{\mathfrak p,i}$ on the spherical vector of an unramified $\pi_{\mathfrak p}$ with Satake parameters $\alpha$ is $N\mathfrak p^{i(n-i)/2}e_i(\alpha)$, where $L(s,\pi_{\mathfrak p})=\prod_j(1-\alpha_jN\mathfrak p^{-s})^{-1}$. Restricting to bounded cusp forms with unitary central character loses nothing for Artin representations, since the corresponding cuspidal representation has finite-order central character.
-- source:
--   Langlands program (Wikipedia article, uploaded PDF), section Reciprocity and section Status; https://en.wikipedia.org/wiki/Langlands_program

import Mathlib

/-!
# Langlands reciprocity for `GL(n)` over a number field: the objects

This file sets up the two sides of the Langlands reciprocity conjecture for `GL(n)` over a
number field `K`, as described in the article *Langlands program* (section *Reciprocity*).

**Galois side.** An *Artin representation* of `K` is a continuous homomorphism
`ρ : Gal(K̄/K) → GL(n, ℂ)` (the absolute Galois group carries the Krull topology).
At a maximal ideal `𝔭` of `𝓞 K` we use the ring `𝓞_{K̄}` of algebraic integers of `K̄` and a
prime `𝔓` of it lying over `𝔭`:
* `σ` is in the *inertia group* of `𝔓` if `σ x ≡ x (mod 𝔓)` for all `x ∈ 𝓞_{K̄}`;
* `σ` is an *(arithmetic) Frobenius element* at `𝔓` if `σ x ≡ x ^ N𝔭 (mod 𝔓)` for all
  `x ∈ 𝓞_{K̄}`.
`ρ` is unramified at `𝔭` if it kills every inertia group above `𝔭`; then the local Artin
`L`-factor is `det(1 - ρ(Frob_𝔭) N𝔭^{-s})⁻¹ = ∏ᵢ (1 - βᵢ N𝔭^{-s})⁻¹`, where `β₁, …, βₙ` are the
eigenvalues of `ρ(Frob_𝔭)`.

**Automorphic side.** Let `𝔸_K` be the adele ring of `K`.  We use bounded cusp forms on
`GL(n, 𝔸_K)` with unitary central character: continuous bounded functions
`φ : GL(n, 𝔸_K) → ℂ`, left invariant under `GL(n, K)`, transforming under the centre by a
unitary character, whose constant terms along the unipotent radicals of all standard maximal
parabolic subgroups vanish.  At a maximal ideal `𝔭`, `φ` is *spherical* if it is right
invariant under `GL(n, 𝒪_𝔭)` (embedded in the `𝔭`-component), and the spherical Hecke operators
are `T_{𝔭,i} φ (g) = ∑_{x ∈ GL(n,𝒪_𝔭) tᵢ GL(n,𝒪_𝔭) / GL(n,𝒪_𝔭)} φ (g x)` with
`tᵢ = diag(ϖ, …, ϖ, 1, …, 1)` (`i` copies of a uniformizer `ϖ`).  If `π_𝔭` is unramified with
Satake parameters `α₁, …, αₙ`, so that `L(s, π_𝔭) = ∏ᵢ (1 - αᵢ N𝔭^{-s})⁻¹`, then `T_{𝔭,i}` acts
on the spherical vector by `N𝔭^{i(n-i)/2} eᵢ(α₁, …, αₙ)`.

The correspondence `ρ ↔ π` of the reciprocity conjecture is the equality of local `L`-factors
at almost all primes, which in these terms says that a nonzero cusp form is, at almost every
prime, a spherical Hecke eigenform with eigenvalues `N𝔭^{i(n-i)/2} eᵢ(β₁, …, βₙ)`.
-/

namespace LanglandsReciprocity

open NumberField IsDedekindDomain MeasureTheory

/-! ### The Galois side -/

section Galois

variable {K : Type*} [Field K] [NumberField K]

/-- The ring of algebraic integers of `K̄`, i.e. the integral closure of `ℤ` (equivalently of
`𝓞 K`) in the algebraic closure of `K`. -/
noncomputable abbrev AlgIntegers (K : Type*) [Field K] : Subalgebra ℤ (AlgebraicClosure K) :=
  integralClosure ℤ (AlgebraicClosure K)

/-- The absolute norm `N𝔭 = #(𝓞 K / 𝔭)` of a maximal ideal `𝔭` of `𝓞 K`. -/
noncomputable def absNorm (𝔭 : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.card (𝓞 K ⧸ 𝔭.asIdeal)

/-- `𝔓` is a prime ideal of the algebraic integers of `K̄` lying over the prime `𝔭` of `𝓞 K`. -/
def LiesOver (𝔭 : HeightOneSpectrum (𝓞 K)) (𝔓 : Ideal (AlgIntegers K)) : Prop :=
  𝔓.IsPrime ∧
    ∀ (a : 𝓞 K) (b : AlgIntegers K),
      (b : AlgebraicClosure K) = algebraMap K (AlgebraicClosure K) (a : K) →
        (b ∈ 𝔓 ↔ a ∈ 𝔭.asIdeal)

/-- `σ` lies in the inertia group of `𝔓`: `σ x ≡ x (mod 𝔓)` for every algebraic integer `x`. -/
def IsInertiaElement (𝔓 : Ideal (AlgIntegers K)) (σ : Gal(AlgebraicClosure K/K)) : Prop :=
  ∀ x y : AlgIntegers K, (y : AlgebraicClosure K) = σ (x : AlgebraicClosure K) → y - x ∈ 𝔓

/-- `σ` is an arithmetic Frobenius element at the prime `𝔓` above `𝔭`:
`σ x ≡ x ^ N𝔭 (mod 𝔓)` for every algebraic integer `x`. -/
def IsFrobeniusElement (𝔭 : HeightOneSpectrum (𝓞 K)) (𝔓 : Ideal (AlgIntegers K))
    (σ : Gal(AlgebraicClosure K/K)) : Prop :=
  ∀ x y : AlgIntegers K,
    (y : AlgebraicClosure K) = σ (x : AlgebraicClosure K) → y - x ^ absNorm 𝔭 ∈ 𝔓

/-- An `n`-dimensional complex representation `ρ` of `Gal(K̄/K)` is irreducible: `n ≥ 1` and
the only `ρ`-stable subspaces of `ℂⁿ` are `0` and `ℂⁿ`. -/
def IsIrreducible {n : ℕ} (ρ : Gal(AlgebraicClosure K/K) →* GL (Fin n) ℂ) : Prop :=
  0 < n ∧
    ∀ W : Submodule ℂ (Fin n → ℂ),
      (∀ σ, ∀ v ∈ W, (ρ σ : Matrix (Fin n) (Fin n) ℂ).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

/-- `ρ` is unramified at `𝔭`: it is trivial on the inertia group of every prime above `𝔭`. -/
def IsUnramifiedAt {n : ℕ} (ρ : Gal(AlgebraicClosure K/K) →* GL (Fin n) ℂ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ 𝔓, LiesOver 𝔭 𝔓 → ∀ σ, IsInertiaElement 𝔓 σ → ρ σ = 1

/-- The multiset of eigenvalues (with algebraic multiplicity) of a complex square matrix. -/
noncomputable def eigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Multiset ℂ :=
  A.charpoly.roots

end Galois

/-! ### The automorphic side -/

section Automorphic

variable {K : Type*} [Field K] [NumberField K]

/-- The adele ring `𝔸_K = K_∞ × 𝔸_{K,f}` of the number field `K`. -/
abbrev Adeles (K : Type*) [Field K] [NumberField K] : Type _ := AdeleRing (𝓞 K) K

/-- `GL(n, K)` embedded diagonally in `GL(n, 𝔸_K)`. -/
noncomputable def principalEmb (n : ℕ) : GL (Fin n) K →* GL (Fin n) (Adeles K) :=
  Matrix.GeneralLinearGroup.map (algebraMap K (Adeles K))

/-- The centre `𝔸_K^× ↪ GL(n, 𝔸_K)`, `z ↦ z · 1`. -/
noncomputable def scalarEmb (n : ℕ) : (Adeles K)ˣ →* GL (Fin n) (Adeles K) :=
  Units.map (algebraMap (Adeles K) (Matrix (Fin n) (Fin n) (Adeles K))).toMonoidHom

/-- Positions `(i, j)` of the upper-right `r × (n - r)` block of an `n × n` matrix. -/
def BlockIdx (n r : ℕ) : Type := {p : Fin n × Fin n // p.1.val < r ∧ r ≤ p.2.val}

/-- The unipotent matrix `[[1, X], [0, 1]]` with upper-right `r × (n - r)` block `X`. -/
def unipotentMatrix {R : Type*} [CommRing R] (n r : ℕ) (X : BlockIdx n r → R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j =>
    if i = j then 1 else if h : i.val < r ∧ r ≤ j.val then X ⟨(i, j), h⟩ else 0

theorem det_unipotentMatrix {R : Type*} [CommRing R] (n r : ℕ) (X : BlockIdx n r → R) :
    (unipotentMatrix n r X).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [unipotentMatrix]
  · intro i j hij
    have hne : i ≠ j := fun h => (lt_irrefl _ (h ▸ hij))
    have hlt : j.val < i.val := hij
    simp only [unipotentMatrix, if_neg hne]
    rw [dif_neg]
    omega

/-- The element `[[1, X], [0, 1]]` of the unipotent radical `N_r(𝔸_K)` of the standard maximal
parabolic subgroup of type `(r, n - r)` of `GL(n)`. -/
noncomputable def unipotent (n r : ℕ) (X : BlockIdx n r → Adeles K) : GL (Fin n) (Adeles K) :=
  Matrix.SpecialLinearGroup.toGL ⟨unipotentMatrix n r X, det_unipotentMatrix n r X⟩

/-- The rational points `N_r(K) ≅ K^{r(n-r)}` inside `N_r(𝔸_K) ≅ 𝔸_K^{r(n-r)}`. -/
noncomputable def rationalBlocks (K : Type*) [Field K] [NumberField K] (n r : ℕ) :
    AddSubgroup (BlockIdx n r → Adeles K) :=
  AddSubgroup.pi Set.univ fun _ => (algebraMap K (Adeles K)).range.toAddSubgroup

/-- Vanishing of all constant terms along standard maximal parabolic subgroups:
for every `0 < r < n` and every `g`, `∫_{N_r(K) \ N_r(𝔸_K)} φ(u g) du = 0`.  The integral over
the compact quotient is computed on a measurable fundamental domain for the translation action of
`N_r(K)` on `N_r(𝔸_K) ≅ 𝔸_K^{r(n-r)}` (Borel σ-algebra), with respect to a Haar measure; the
condition is required for every Haar measure and every fundamental domain. -/
def IsCuspidal {n : ℕ} (φ : GL (Fin n) (Adeles K) → ℂ) : Prop :=
  ∀ r : ℕ, 0 < r → r < n → ∀ g : GL (Fin n) (Adeles K),
    letI : MeasurableSpace (BlockIdx n r → Adeles K) := borel _
    ∀ μ : Measure (BlockIdx n r → Adeles K), μ.IsAddHaarMeasure →
      ∀ F : Set (BlockIdx n r → Adeles K), IsAddFundamentalDomain (rationalBlocks K n r) F μ →
        ∫ X in F, φ (unipotent n r X * g) ∂μ = 0

/-- `φ` is a bounded cusp form on `GL(n, 𝔸_K)` with unitary central character:
1. `φ` is continuous and bounded;
2. `φ(γ g) = φ(g)` for all `γ ∈ GL(n, K)`;
3. there is a unitary function `ω` on `𝔸_K^×` with `φ(z g) = ω(z) φ(g)` for all central `z`;
4. `φ` is cuspidal. -/
def IsCuspForm {n : ℕ} (φ : GL (Fin n) (Adeles K) → ℂ) : Prop :=
  Continuous φ ∧
    (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧
    (∀ (γ : GL (Fin n) K) (g : GL (Fin n) (Adeles K)), φ (principalEmb n γ * g) = φ g) ∧
    (∃ ω : (Adeles K)ˣ → ℂ, (∀ z, ‖ω z‖ = 1) ∧ ∀ z g, φ (scalarEmb n z * g) = ω z * φ g) ∧
    IsCuspidal φ

/-- The component at the finite place `𝔭` of a matrix over `𝔸_K`. -/
noncomputable def localComponent {n : ℕ} (𝔭 : HeightOneSpectrum (𝓞 K))
    (g : Matrix (Fin n) (Fin n) (Adeles K)) : Matrix (Fin n) (Fin n) (𝔭.adicCompletion K) :=
  g.map fun a => a.2 𝔭

/-- `g ∈ GL(n, 𝔸_K)` is concentrated at `𝔭`: all of its components away from `𝔭`
(archimedean and finite) are the identity. -/
def IsConcentratedAt {n : ℕ} (𝔭 : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (Adeles K)) : Prop :=
  (g : Matrix (Fin n) (Fin n) (Adeles K)).map Prod.fst = 1 ∧
    ∀ w, w ≠ 𝔭 → (g : Matrix (Fin n) (Fin n) (Adeles K)).map (fun a => a.2 w) = 1

/-- A matrix over `K_𝔭` with all entries in `𝒪_𝔭`. -/
def IsIntegralMatrix {n : ℕ} {𝔭 : HeightOneSpectrum (𝓞 K)}
    (A : Matrix (Fin n) (Fin n) (𝔭.adicCompletion K)) : Prop :=
  ∀ i j, A i j ∈ 𝔭.adicCompletionIntegers K

/-- The maximal compact subgroup `GL(n, 𝒪_𝔭)`, placed at the `𝔭`-component of `GL(n, 𝔸_K)`. -/
def maxCompactAt (n : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) : Set (GL (Fin n) (Adeles K)) :=
  {k | IsConcentratedAt 𝔭 k ∧ IsIntegralMatrix (localComponent 𝔭 (k : Matrix (Fin n) (Fin n) (Adeles K))) ∧
    IsIntegralMatrix (localComponent 𝔭 ((k⁻¹ : GL (Fin n) (Adeles K)) : Matrix (Fin n) (Fin n) (Adeles K)))}

/-- The double coset `GL(n, 𝒪_𝔭) diag(ϖ, …, ϖ, 1, …, 1) GL(n, 𝒪_𝔭)` (`i` entries equal to a
uniformizer `ϖ`), placed at the `𝔭`-component of `GL(n, 𝔸_K)`.  By the Cartan decomposition an
element `A ∈ GL(n, K_𝔭)` lies in it iff `A` and `ϖ A⁻¹` have entries in `𝒪_𝔭` and
`det A ∈ ϖ^i 𝒪_𝔭^×`; the uniformizer is taken to be the image of some `a ∈ 𝔭 \ 𝔭²`. -/
def heckeDoubleCoset (n : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) (i : ℕ) :
    Set (GL (Fin n) (Adeles K)) :=
  {g | IsConcentratedAt 𝔭 g ∧
    ∃ a : 𝓞 K, a ∈ 𝔭.asIdeal ∧ a ∉ 𝔭.asIdeal ^ 2 ∧
      IsIntegralMatrix (localComponent 𝔭 (g : Matrix (Fin n) (Fin n) (Adeles K))) ∧
      IsIntegralMatrix (algebraMap K (𝔭.adicCompletion K) (a : K) •
        localComponent 𝔭 ((g⁻¹ : GL (Fin n) (Adeles K)) : Matrix (Fin n) (Fin n) (Adeles K))) ∧
      ∃ u : 𝔭.adicCompletion K, u ∈ 𝔭.adicCompletionIntegers K ∧
        u⁻¹ ∈ 𝔭.adicCompletionIntegers K ∧
        (localComponent 𝔭 (g : Matrix (Fin n) (Fin n) (Adeles K))).det =
          algebraMap K (𝔭.adicCompletion K) (a : K) ^ i * u}

/-- `R` is a finite system of representatives of the left cosets `d H` contained in `D`. -/
def IsCosetReps {G : Type*} [Group G] (D H : Set G) (R : Finset G) : Prop :=
  (↑R ⊆ D) ∧ ∀ d ∈ D, ∃! r, r ∈ R ∧ r⁻¹ * d ∈ H

/-- `φ` is spherical at `𝔭` (right invariant under `GL(n, 𝒪_𝔭)`) and an eigenfunction of the
spherical Hecke operators `T_{𝔭,i}`, `1 ≤ i ≤ n`, with eigenvalue `eigenval i`, where
`(T_{𝔭,i} φ)(g) = ∑_{r ∈ R} φ(g r)` for a system `R` of representatives of
`GL(n, 𝒪_𝔭) tᵢ GL(n, 𝒪_𝔭) / GL(n, 𝒪_𝔭)`. -/
def IsSphericalHeckeEigen {n : ℕ} (φ : GL (Fin n) (Adeles K) → ℂ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (eigenval : ℕ → ℂ) : Prop :=
  (∀ g, ∀ k ∈ maxCompactAt n 𝔭, φ (g * k) = φ g) ∧
    ∀ i, 1 ≤ i → i ≤ n → ∀ R : Finset (GL (Fin n) (Adeles K)),
      IsCosetReps (heckeDoubleCoset n 𝔭 i) (maxCompactAt n 𝔭) R →
        ∀ g, ∑ r ∈ R, φ (g * r) = eigenval i * φ g

end Automorphic

/-! ### The reciprocity correspondence -/

section Correspondence

variable {K : Type*} [Field K] [NumberField K]

/-- The cusp form `φ` *corresponds* to the Artin representation `ρ`: `φ` is a nonzero bounded
cusp form on `GL(n, 𝔸_K)` with unitary central character and there is a finite set `S` of
primes such that for every `𝔭 ∉ S`, `ρ` is unramified at `𝔭` and, for every Frobenius element
`σ` at a prime above `𝔭`, `φ` is spherical at `𝔭` and a Hecke eigenfunction with
`T_{𝔭,i} φ = N𝔭^{i(n-i)/2} eᵢ(ρ(σ)) φ` for `1 ≤ i ≤ n`, where `eᵢ(ρ(σ))` is the `i`-th elementary
symmetric function of the eigenvalues of `ρ(σ)`.  Equivalently, the cuspidal automorphic
representation generated by `φ` has the same local `L`-factors as `ρ` at all `𝔭 ∉ S`. -/
def Corresponds {n : ℕ} (ρ : Gal(AlgebraicClosure K/K) →* GL (Fin n) ℂ)
    (φ : GL (Fin n) (Adeles K) → ℂ) : Prop :=
  φ ≠ 0 ∧ IsCuspForm φ ∧
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ 𝔭 ∉ S,
      IsUnramifiedAt ρ 𝔭 ∧
        ∀ 𝔓, LiesOver 𝔭 𝔓 → ∀ σ, IsFrobeniusElement 𝔭 𝔓 σ →
          IsSphericalHeckeEigen φ 𝔭 fun i =>
            (Real.sqrt (absNorm 𝔭 : ℝ) : ℂ) ^ (i * (n - i)) *
              (eigenvalues (ρ σ : Matrix (Fin n) (Fin n) ℂ)).esymm i

/-- `ρ` is *automorphic*: some cusp form on `GL(n, 𝔸_K)` corresponds to it. -/
def IsAutomorphic {n : ℕ} (ρ : Gal(AlgebraicClosure K/K) →* GL (Fin n) ℂ) : Prop :=
  ∃ φ : GL (Fin n) (Adeles K) → ℂ, Corresponds ρ φ

end Correspondence

end LanglandsReciprocity


