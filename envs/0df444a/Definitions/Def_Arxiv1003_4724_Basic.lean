-- Prove2me | Definitions.Def_Arxiv1003_4724_Basic
-- name    : Arxiv1003_4724_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T23:54:05.03384+00:00
-- url     : https://prove2.me/theorems/e8f1b063-7e61-4c33-9cae-0a395fcf4bd2
-- title:
--   Equilibrium averages, Green functions, correlation functions and principal values for the dielectric function of Coulomb systems
-- statement:
--   Objects of Sections I-III of Bobrov, Trigger, van Heijst and Schram (2010).
--
--   1. **Observables, average, evolution.** Observables are the elements of a complex $*$-algebra $A$. The grand canonical average $\langle\cdot\rangle$ is a *state*: a linear functional with $\langle 1\rangle=1$ and $\langle X^*X\rangle\ge0$ for every $X$. The Heisenberg evolution $X\mapsto X(t)=\tau_t X$ is a one-parameter group of $*$-automorphisms ($\tau_0=\mathrm{id}$, $\tau_{s+t}=\tau_s\tau_t$). The state is stationary: $\langle X(t)\rangle=\langle X\rangle$.
--   2. **Charges and densities.** Species $a$ have charge $z_ae$ and mass $m_a$. $N_a$ is the self-adjoint particle-number operator, and $n_a=\langle N_a\rangle/V$ is the average density in volume $V$. Quasi-neutrality (eq. 3) is $\sum_a e z_a n_a=0$. The total charge is $Z=\sum_a z_a e N_a$, and $\langle\delta N_a\delta N_b\rangle$ with $\delta N_a=N_a-\langle N_a\rangle$ are the number fluctuations (eq. 22). The squared inverse screening length is $\kappa^2=4\pi\langle Z^2\rangle/(TV)$ (eq. 23), and the squared plasma frequency is $\omega_p^2=\sum_a4\pi z_a^2e^2n_a/m_a$ (eq. 21).
--   3. **Current and dipole.** $P^\beta$ and $I^\beta$, $\beta=1,2,3$, are the Cartesian components of the total charge dipole moment and the total current. A *long-wavelength model* (Secs. II-III) is a stationary state and evolution in which $P^\beta$ and $I^\beta$ are self-adjoint and $dP^\beta(t)/dt=I^\beta(t)$ (eq. 26) holds inside averages: $\frac{d}{dt}\langle P^\beta(t)B\rangle=\langle I^\beta(t)B\rangle$ and $\frac{d}{dt}\langle BP^\beta(t)\rangle=\langle BI^\beta(t)\rangle$ for every $B$. The commutator correlations $\langle[X(t),Y]\rangle$, $X,Y\in\{P^\beta,I^\beta\}$, are continuous and bounded in $t$.
--   4. **Green functions (eqs. 2, 20, 25).** The retarded Green function is $\langle\!\langle X|Y\rangle\!\rangle_z=-\frac{i}{\hbar}\int_0^\infty e^{izt}\langle[X(t),Y]\rangle\,dt$ for $\operatorname{Im}z>0$. From it, $\varphi(z)=\frac{4\pi}{3V}\langle\!\langle I^\beta|I^\beta\rangle\!\rangle_z$ and the Kubo conductivity is $\sigma(z)=-\frac{1}{3V}\langle\!\langle I^\beta|P^\beta\rangle\!\rangle_z$, with summation over $\beta$.
--   5. **Time correlation functions (eqs. 30, 31, 33).** $\sigma(t)=\frac{i}{3\hbar V}\langle[I^\beta(t),P^\beta]\rangle$ and $\varphi(t)=-\frac{i}{3\hbar V}\langle[I^\beta(t),I^\beta]\rangle$. The dipole correlation is $\frac{i}{3\hbar V}\langle[P^\beta(t),P^\beta]\rangle$. The real-frequency transform is $\sigma^{(0)}(\omega)=\int_0^\infty e^{i\omega t}\sigma(t)\,dt$.
--   6. **Principal values.** For a finite set $S$ of singular points, $P\!\int_{-\infty}^\infty f=L$ means that $\int f$ over $\{|\xi|\le R,\ |\xi-s|\ge\delta\ \forall s\in S\}$ tends to $L$ as $\delta\to0^+$ and $R\to\infty$ jointly.
--
--   **Formalization Note** The paper's operators act on the Fock space of a Coulomb system in the thermodynamic limit, which Mathlib cannot construct. Here they are elements of an arbitrary complex $*$-algebra, and the grand canonical average is an arbitrary stationary state on it. Only the properties the paper's arguments use are imposed. The densities $n_a$ are $\operatorname{Re}\langle N_a\rangle/V$; $\langle N_a\rangle$ is real because $N_a$ is self-adjoint.
-- source:
--   Bobrov, Trigger, van Heijst and Schram, Kramers-Kronig relations for the dielectric function and the static conductivity of Coulomb systems, arXiv:1003.4724v1 (2010), Sec. I eqs. (1)-(3), (7)-(8); Sec. II eqs. (18)-(28); Sec. III eqs. (29)-(33); Sec. IV eqs. (36)-(38)

import Mathlib

/-!
Bobrov, Trigger, van Heijst and Schram, *Kramers-Kronig relations for the dielectric function and
the static conductivity of Coulomb systems*, arXiv:1003.4724v1 (2010): the equilibrium average,
time evolution, charge, current and dipole operators, retarded Green functions, time correlation
functions and the long-wavelength permittivity of Sections I-III (eqs. (1)-(3), (20)-(26),
(29)-(31), (33)), and the principal-value integrals of the Kramers-Kronig relations (7)-(8),
(27)-(28).

Observables are the elements of a complex `*`-algebra `A`; the grand canonical average `<...>`
is a linear functional on `A`, and the Heisenberg evolution `X ↦ X(t)` is a one-parameter group
of `*`-automorphisms of `A`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace Arxiv1003_4724

section Algebraic

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- Sec. I, after eq. (2): the angle brackets `<...>` are an equilibrium average, i.e. a state:
a normalised (`<1> = 1`) positive (`<X* X>` real and `≥ 0`) linear functional on observables. -/
def IsState (ω : A →ₗ[ℂ] ℂ) : Prop :=
  ω 1 = 1 ∧ ∀ X : A, (ω (star X * X)).im = 0 ∧ 0 ≤ (ω (star X * X)).re

/-- Sec. I, eq. (2): the Heisenberg representation `X(t) = τ t X` is a one-parameter group of
`*`-automorphisms: `X(0) = X` and `X(s + t) = τ s (X(t))`. -/
def IsDynamics (τ : ℝ → A ≃⋆ₐ[ℂ] A) : Prop :=
  (∀ X, τ 0 X = X) ∧ ∀ s t X, τ (s + t) X = τ s (τ t X)

/-- Sec. I: the grand canonical average is an equilibrium average, invariant under the
time evolution: `<X(t)> = <X>`. -/
def IsStationary (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) : Prop :=
  ∀ t X, ω (τ t X) = ω X

/-- The commutator time correlation function `<[X(t), Y(0)]>` of eq. (2) and eq. (31). -/
def commCorr (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (X Y : A) (t : ℝ) : ℂ :=
  ω ⁅τ t X, Y⁆

/-- Eq. (26), first identity, `dP^β(t)/dt = I^β(t)`, in the weak sense in which it enters
averages: for every observable `B`, `d/dt <P^β(t) B> = <I^β(t) B>` and
`d/dt <B P^β(t)> = <B I^β(t)>`. Here `Dip β = P^β` (eq. (25)) and `Cur β = I^β` (eq. (21)). -/
def DipoleDerivIsCurrent (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (Dip Cur : Fin 3 → A) : Prop :=
  ∀ (β : Fin 3) (B : A) (t : ℝ),
    HasDerivAt (fun s => ω (τ s (Dip β) * B)) (ω (τ t (Cur β) * B)) t ∧
      HasDerivAt (fun s => ω (B * τ s (Dip β))) (ω (B * τ t (Cur β))) t

/-- The standing setting of Secs. II-III: `<...>` is a stationary state for the Heisenberg
evolution `τ`; the components `P^β` of the total charge dipole moment (eq. (25)) and `I^β` of the
total current (eq. (21)) are self-adjoint; `dP^β/dt = I^β` (eq. (26)); and the commutator
correlation functions of these operators, which enter the time integrals (2), (20), (25), (30),
are continuous and bounded in `t`. -/
def IsLongWaveModel (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (Dip Cur : Fin 3 → A) : Prop :=
  IsState ω ∧ IsDynamics τ ∧ IsStationary ω τ ∧
    (∀ β, IsSelfAdjoint (Dip β) ∧ IsSelfAdjoint (Cur β)) ∧
    DipoleDerivIsCurrent ω τ Dip Cur ∧
    ∀ β, ∀ X ∈ ({Dip β, Cur β} : Set A), ∀ Y ∈ ({Dip β, Cur β} : Set A),
      Continuous (commCorr ω τ X Y) ∧ ∃ M : ℝ, ∀ t, ‖commCorr ω τ X Y t‖ ≤ M

/-- Eq. (2): the retarded Green function
`<<X | Y>>_z = -(i/ħ) ∫_0^∞ exp(i z t) <[X(t), Y(0)]> dt`, `Im z > 0`
(so that `χ^R(q,z) = V⁻¹ <<ρ_q | ρ_{-q}>>_z`). -/
def retardedGreen (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (hbar : ℝ) (X Y : A) (z : ℂ) : ℂ :=
  -(Complex.I / hbar) * ∫ t in Set.Ioi (0 : ℝ), Complex.exp (Complex.I * z * t) * commCorr ω τ X Y t

/-- Eq. (20): `φ(z) = (4π/3V) <<I^β | I^β>>_z`, summed over `β`. -/
def phiFn (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (hbar V : ℝ) (Cur : Fin 3 → A) (z : ℂ) : ℂ :=
  4 * Real.pi / (3 * V) * ∑ β, retardedGreen ω τ hbar (Cur β) (Cur β) z

/-- Eq. (25), Kubo formula: `σ(z) = -(1/3V) <<I^β | P^β>>_z`, summed over `β`. -/
def kuboSigma (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (hbar V : ℝ) (Dip Cur : Fin 3 → A) (z : ℂ) :
    ℂ :=
  -(1 / (3 * V)) * ∑ β, retardedGreen ω τ hbar (Cur β) (Dip β) z

/-- Eq. (31): `σ(t) = (i/3ħV) <[I^β(t), P^β(0)]>`, summed over `β`. -/
def sigmaCorr (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (hbar V : ℝ) (Dip Cur : Fin 3 → A) (t : ℝ) :
    ℂ :=
  Complex.I / (3 * hbar * V) * ∑ β, commCorr ω τ (Cur β) (Dip β) t

/-- Eq. (31): `φ(t) = -(i/3ħV) <[I^β(t), I^β(0)]>`, summed over `β`. -/
def phiCorr (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (hbar V : ℝ) (Cur : Fin 3 → A) (t : ℝ) : ℂ :=
  -(Complex.I / (3 * hbar * V)) * ∑ β, commCorr ω τ (Cur β) (Cur β) t

/-- Eq. (33), right-hand side before the limit: `(i/3ħV) <[P^β(t), P^β(0)]>`, summed over `β`. -/
def dipoleCorr (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (hbar V : ℝ) (Dip : Fin 3 → A) (t : ℝ) : ℂ :=
  Complex.I / (3 * hbar * V) * ∑ β, commCorr ω τ (Dip β) (Dip β) t

/-- Eq. (30): `σ^(0)(ω) = ∫_0^∞ exp(i ω t) σ(t) dt` for real frequency `ω`. -/
def sigma0 (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (hbar V : ℝ) (Dip Cur : Fin 3 → A) (x : ℝ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), Complex.exp (Complex.I * x * t) * sigmaCorr ω τ hbar V Dip Cur t

variable {ι : Type*}

/-- Sec. I: the average density `n_a = <N_a>/V` of species `a`, `N_a` the particle-number
operator of species `a`. -/
def meanDensity (ω : A →ₗ[ℂ] ℂ) (N : ι → A) (V : ℝ) (a : ι) : ℝ :=
  (ω (N a)).re / V

/-- Eq. (3): the quasi-neutrality condition `∑_a e z_a n_a = 0`. -/
def IsQuasiNeutral [Fintype ι] (ω : A →ₗ[ℂ] ℂ) (N : ι → A) (z : ι → ℝ) (e V : ℝ) : Prop :=
  ∑ a, e * z a * meanDensity ω N V a = 0

/-- Eq. (23): the operator of the total charge `Z = ∑_a z_a e N_a`. -/
def totalCharge [Fintype ι] (N : ι → A) (z : ι → ℝ) (e : ℝ) : A :=
  ∑ a, ((z a * e : ℝ) : ℂ) • N a

/-- Eq. (22): the number fluctuation correlation `<δN_a δN_b>`, `δN_a = N_a - <N_a>`. -/
def numberCov (ω : A →ₗ[ℂ] ℂ) (N : ι → A) (a b : ι) : ℂ :=
  ω ((N a - ω (N a) • (1 : A)) * (N b - ω (N b) • (1 : A)))

/-- Eq. (23): `κ² = (4π/T) <Z²>/V`. -/
def kappaSq [Fintype ι] (ω : A →ₗ[ℂ] ℂ) (N : ι → A) (z : ι → ℝ) (e T V : ℝ) : ℂ :=
  4 * Real.pi / T * ω (totalCharge N z e * totalCharge N z e) / V

/-- Eq. (21): the square of the plasma frequency, `ω_p² = ∑_a 4π z_a² e² n_a / m_a`. -/
def plasmaFreqSq [Fintype ι] (z : ι → ℝ) (e : ℝ) (n m : ι → ℝ) : ℝ :=
  ∑ a, 4 * Real.pi * z a ^ 2 * e ^ 2 * n a / m a

end Algebraic

/-- The truncation `{ξ : |ξ| ≤ R, |ξ - s| ≥ δ for every s ∈ S}` used for a principal-value
integral with singular points `S`. -/
def pvDomain (S : Set ℝ) (δ R : ℝ) : Set ℝ :=
  {ξ | |ξ| ≤ R ∧ ∀ s ∈ S, δ ≤ |ξ - s|}

/-- Eqs. (7)-(8), (27)-(28): `P ∫_{-∞}^{∞} f(ξ) dξ = L`, the principal value with singular points
`S`: the integrals over `pvDomain S δ R` tend to `L` as `δ → 0⁺` and `R → ∞`. -/
def HasPVIntegral (f : ℝ → ℝ) (S : Set ℝ) (L : ℝ) : Prop :=
  Tendsto (fun p : ℝ × ℝ => ∫ ξ in pvDomain S p.1 p.2, f ξ) (𝓝[>] (0 : ℝ) ×ˢ atTop) (𝓝 L)

end Arxiv1003_4724


