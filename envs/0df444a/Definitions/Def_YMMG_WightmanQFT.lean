-- Prove2me | Definitions.Def_YMMG_WightmanQFT
-- name    : YMMG_WightmanQFT
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T16:08:45.655985+00:00
-- url     : https://prove2.me/theorems/4f7f990b-efb2-428b-b51d-c4b3bd48514a
-- title:
--   Wightman quantum field theory on Hilbert space; mass gap
-- statement:
--   A **Wightman QFT** is defined as in Jaffe–Witten §3 and Streater–Wightman Ch. 3. It consists of the following data:
--
--   - a Hilbert space $\mathcal H$ with a dense domain $D$;
--   - a unit vacuum $\Omega\in D$;
--   - a strongly continuous unitary representation $U(a,\Lambda)$ of the restricted Poincaré group that preserves $D$;
--   - a vacuum that is invariant, and unique up to scalars;
--   - spectral condition: the Fourier transform of $a\mapsto\langle u,U(a,1)v\rangle$ is supported in $\overline V_+$;
--   - hermitian field multiplets $\varphi_{i,c}(f)$ acting on $D$ that are tempered, covariant under finite-dimensional representations $S_i$ of $L^\uparrow_+$, and local;
--   - cyclicity of $\Omega$.
--
--   The file also defines the following notions:
--   - **Mass gap** $\Delta$: the Hamiltonian has no spectrum in $(0,\Delta)$, expressed through the Fourier support of $t\mapsto\langle u,e^{iHt}v\rangle$.
--   - **Finite mass**: $\operatorname{spec}H\neq\{0\}$.
--   - **Generalized free field**: Wick factorization of all vacuum expectation values.
--   - The Wightman family of a field component.
--   - Scalar multiplets.
--   - Local operator algebras.
--   - Translated operators $O(a)=U(a)OU(a)^{-1}$.
-- source:
--   A. Jaffe, E. Witten, *Quantum Yang–Mills Theory* (Clay Mathematics Institute Millennium Problem description), https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf, §3 and §4 (mass gap definition); Streater–Wightman (1964), §3.1

module

public import Mathlib
public import Definitions.Def_YMMG_WightmanAxioms

/-!
# Wightman quantum field theories on Hilbert space, and the mass gap

Following Jaffe–Witten, *Quantum Yang–Mills Theory*, §3–§4 and the Gårding–Wightman axioms
(Streater–Wightman, Ch. 3): a Hilbert space `ℋ` with a strongly continuous unitary
representation `U` of the restricted Poincaré group, a unique invariant vacuum `Ω`, positive
energy (joint energy–momentum spectrum in the closed forward cone), and local quantum fields —
operator-valued tempered distributions on a common dense invariant domain `D` which transform
covariantly under `U`, commute at spacelike separation and generate `ℋ` from `Ω`.

The fields come in multiplets `φ_{i,c}` (`i : ι` a multiplet label, `c : κ i` its components)
transforming under a finite-dimensional representation `S_i` of `L↑₊`; all components are
hermitian (bosonic, real) fields, as is appropriate for the gauge-invariant local polynomials in
the curvature of a Yang–Mills theory.

Conventions: `φ(x + a) = U(a) φ(x) U(a)⁻¹` and `U(a) = e^{i(H a⁰ - P⃗·a⃗)}` with `H ≥ 0`;
Mathlib's Fourier transform `𝓕 g(k) = ∫ e^{-2πi⟨x,k⟩} g(x) dx`.  With these conventions the
distribution `a ↦ ⟨u, U(a)v⟩` has Fourier transform `𝓕` supported in `2π⁻¹·spec(P)` — which is
why spectral sets appear divided by `2π` below.
-/

@[expose] public section

noncomputable section

namespace YangMillsMassGap

open scoped ComplexOrder FourierTransform InnerProductSpace
open Filter Topology

lemma one_mem_restrictedLorentz : (1 : Matrix (Fin 4) (Fin 4) ℝ) ∈ restrictedLorentz := by
  simp [restrictedLorentz]

/-- A Wightman quantum field theory with hermitian field multiplets `φ_{i,c}` (`i : ι`,
`c : κ i`) on the Hilbert space `H`. -/
structure WightmanQFT (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ι : Type) (κ : ι → Type) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] where
  /-- The common dense domain of the fields. -/
  D : Submodule ℂ H
  D_dense : Dense (D : Set H)
  /-- The vacuum vector. -/
  Ω : H
  Ω_mem : Ω ∈ D
  Ω_norm : ‖Ω‖ = 1
  /-- The representation `(a, Λ) ↦ U(a, Λ)` of the restricted Poincaré group
  (only its values for `Λ ∈ L↑₊` matter). -/
  U : Spacetime → Matrix (Fin 4) (Fin 4) ℝ → (H →L[ℂ] H)
  U_unitary : ∀ a Λ, Λ ∈ restrictedLorentz → U a Λ ∈ unitary (H →L[ℂ] H)
  U_one : U 0 1 = 1
  U_mul : ∀ a b Λ M, Λ ∈ restrictedLorentz → M ∈ restrictedLorentz →
    U a Λ * U b M = U (a + matAct Λ b) (Λ * M)
  U_strongCont : ∀ v : H,
    ContinuousOn (fun p : Spacetime × Matrix (Fin 4) (Fin 4) ℝ => U p.1 p.2 v)
      (Set.univ ×ˢ restrictedLorentz)
  U_domain : ∀ a Λ, Λ ∈ restrictedLorentz → ∀ v ∈ D, U a Λ v ∈ D
  /-- The vacuum is Poincaré invariant ... -/
  Ω_invariant : ∀ a Λ, Λ ∈ restrictedLorentz → U a Λ Ω = Ω
  /-- ... and it is the unique invariant vector up to a scalar. -/
  Ω_unique : ∀ v : H, (∀ a Λ, Λ ∈ restrictedLorentz → U a Λ v = v) → ∃ c : ℂ, v = c • Ω
  /-- Spectral condition: for all `u, v`, the Fourier transform of the bounded continuous function
  `a ↦ ⟨u, U(a,1) v⟩` is supported in the closed forward cone `V̄₊`. -/
  spectrum_condition : ∀ (u v : H) (g : SchwartzMap Spacetime ℂ),
    Disjoint (tsupport g) closedForwardCone → ∫ a, (𝓕 g) a * ⟪u, U a 1 v⟫_ℂ = 0
  /-- The finite-dimensional representation `S_i` of `L↑₊` carried by the multiplet `i`. -/
  S : (i : ι) → Matrix (Fin 4) (Fin 4) ℝ → Matrix (κ i) (κ i) ℂ
  S_one : ∀ i, S i 1 = 1
  S_mul : ∀ i Λ M, Λ ∈ restrictedLorentz → M ∈ restrictedLorentz → S i (Λ * M) = S i Λ * S i M
  S_cont : ∀ i, ContinuousOn (S i) restrictedLorentz
  /-- The smeared fields `f ↦ φ_{i,c}(f)`, linear in the test function, acting on `D`. -/
  φ : (i : ι) → κ i → (SchwartzMap Spacetime ℂ →ₗ[ℂ] Module.End ℂ D)
  /-- Temperedness: `f ↦ ⟨u, φ_{i,c}(f) v⟩` is a tempered distribution for `u, v ∈ D`. -/
  φ_tempered : ∀ i c (u v : D),
    Continuous (fun f : SchwartzMap Spacetime ℂ => ⟪(u : H), (φ i c f v : H)⟫_ℂ)
  /-- Hermiticity: `φ_{i,c}(f)* ⊇ φ_{i,c}(f̄)` on `D`. -/
  φ_hermitian : ∀ i c (f f' : SchwartzMap Spacetime ℂ), (∀ x, f' x = (starRingEnd ℂ) (f x)) →
    ∀ u v : D, ⟪(φ i c f u : H), (v : H)⟫_ℂ = ⟪(u : H), (φ i c f' v : H)⟫_ℂ
  /-- Covariance: `U(a,Λ) φ_{i,c}(f) U(a,Λ)⁻¹ = ∑_{c'} S_i(Λ⁻¹)_{c c'} φ_{i,c'}(f_{(a,Λ)})` on `D`,
  where `f_{(a,Λ)}(x) = f(Λ⁻¹(x - a))`. -/
  φ_covariant : ∀ i c a Λ (f g : SchwartzMap Spacetime ℂ), Λ ∈ restrictedLorentz →
    (∀ x, g x = f (matAct Λ⁻¹ (x - a))) →
    ∀ v w : D, (w : H) = U a Λ v →
      U a Λ (φ i c f v : H) = ∑ c', S i Λ⁻¹ c c' • (φ i c' g w : H)
  /-- Locality: fields smeared with test functions of spacelike separated supports commute. -/
  φ_local : ∀ i c j d (f g : SchwartzMap Spacetime ℂ),
    (∀ x ∈ tsupport f, ∀ y ∈ tsupport g, IsSpacelike (x - y)) →
    ∀ v : D, φ i c f (φ j d g v) = φ j d g (φ i c f v)
  /-- Cyclicity of the vacuum: polynomials in the smeared fields applied to `Ω` are dense. -/
  cyclic : Dense {w : H | ∃ T ∈ Algebra.adjoin ℂ
      {T : Module.End ℂ D | ∃ i c f, T = φ i c f}, w = (T ⟨Ω, Ω_mem⟩ : H)}

namespace WightmanQFT

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type} {κ : ι → Type} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  (Q : WightmanQFT H ι κ)

/-- The vacuum as an element of the domain `D`. -/
def ΩD : Q.D := ⟨Q.Ω, Q.Ω_mem⟩

/-- Vacuum expectation value `⟨Ω, T₁ T₂ ⋯ T_k Ω⟩` of a product of operators on `D`. -/
def vev (l : List (Module.End ℂ Q.D)) : ℂ := ⟪Q.Ω, (l.prod Q.ΩD : H)⟫_ℂ

/-- The space-time translation `U(a, 1)` restricted to the invariant domain `D`. -/
def UD (a : Spacetime) : Module.End ℂ Q.D :=
  ((Q.U a 1 : H →L[ℂ] H) : H →ₗ[ℂ] H).restrict
    (fun v hv => Q.U_domain a 1 one_mem_restrictedLorentz v hv)

/-- The translate `O(a) = U(a) O U(a)⁻¹` of an operator `O` on `D`. -/
def translateOp (a : Spacetime) (O : Module.End ℂ Q.D) : Module.End ℂ Q.D :=
  Q.UD a * O * Q.UD (-a)

/-- The time-translation group `t ↦ U((t, 0⃗), 1) = e^{iHt}`. -/
def timeTranslation (t : ℝ) : H →L[ℂ] H := Q.U (ofTime t) 1

/-- **Mass gap** `Δ` (Jaffe–Witten §4): the Hamiltonian `H` has no spectrum in `(0, Δ)`.
Stated spectrally: for all `u, v ∈ ℋ` the Fourier transform of `t ↦ ⟨u, e^{iHt} v⟩` is supported
in `{0} ∪ [Δ/2π, ∞)` (with `𝓕` as in Mathlib, this is `2π⁻¹ · spec(H)`). -/
def HasMassGap (Δ : ℝ) : Prop :=
  ∀ (u v : H) (g : SchwartzMap ℝ ℂ),
    Disjoint (tsupport g) ({0} ∪ Set.Ici (Δ / (2 * Real.pi))) →
    ∫ t, (𝓕 g) t * ⟪u, Q.timeTranslation t v⟫_ℂ = 0

/-- The mass `m = sup {Δ : H has no spectrum in (0, Δ)}` is finite, i.e. `spec(H) ≠ {0}`:
some vector is not invariant under time translations. -/
def MassIsFinite : Prop :=
  ∃ (v : H) (t : ℝ), Q.timeTranslation t v ≠ v

/-- The field component `φ_{i,c}` is a **generalized free field**: all vacuum expectation values
of products of smeared `φ_{i,c}` obey the Wick recursion
`⟨T R₁⋯Rₖ⟩ = ⟨T⟩⟨R₁⋯Rₖ⟩ + ∑ⱼ (⟨T Rⱼ⟩ - ⟨T⟩⟨Rⱼ⟩) ⟨R₁⋯R̂ⱼ⋯Rₖ⟩`. -/
def IsGeneralizedFreeField (i : ι) (c : κ i) : Prop :=
  ∀ (f : SchwartzMap Spacetime ℂ) (gs : List (SchwartzMap Spacetime ℂ)),
    let T := Q.φ i c f
    let R := gs.map (Q.φ i c)
    Q.vev (T :: R) = Q.vev [T] * Q.vev R +
      ∑ j : Fin R.length, (Q.vev [T, R.get j] - Q.vev [T] * Q.vev [R.get j]) *
        Q.vev (R.eraseIdx j)

/-- `W` is the family of Wightman distributions of the field component `φ_{i,c}`:
`𝔚ₙ(f₁ ⊗ ⋯ ⊗ fₙ) = ⟨Ω, φ_{i,c}(f₁) ⋯ φ_{i,c}(fₙ) Ω⟩` for all product test functions
(by the nuclear theorem this determines `𝔚ₙ`). -/
def IsWightmanFamilyOf (i : ι) (c : κ i) (W : DistributionFamily) : Prop :=
  ∀ (n : ℕ) (fs : Fin n → SchwartzMap Spacetime ℂ) (F : SchwartzMap (Config n) ℂ),
    (∀ x, F x = ∏ j, fs j (x.pt j)) → W n F = Q.vev (List.ofFn fun j => Q.φ i c (fs j))

/-- The multiplet `i` consists of Lorentz scalars: `S_i(Λ) = 1` for all `Λ ∈ L↑₊`. -/
def IsScalarMultiplet (i : ι) : Prop := ∀ Λ, Λ ∈ restrictedLorentz → Q.S i Λ = 1

/-- The algebra of local operators localized in the ball of radius `R`: polynomials in the
fields `φ_{i,c}(f)` with `supp f ⊆ {|x| ≤ R}`. -/
def localAlgebra (R : ℝ) : Subalgebra ℂ (Module.End ℂ Q.D) :=
  Algebra.adjoin ℂ {T | ∃ (i : ι) (c : κ i) (f : SchwartzMap Spacetime ℂ),
    tsupport f ⊆ Metric.closedBall (0 : Spacetime) R ∧ T = Q.φ i c f}

end WightmanQFT

end YangMillsMassGap

end


