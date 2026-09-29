-- Prove2me | Definitions.Def_YMMG_Spacetime
-- name    : YMMG_Spacetime
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T15:53:12.580986+00:00
-- url     : https://prove2.me/theorems/3a2713b9-e275-412f-be15-a6a9a4452f98
-- title:
--   Space-time geometry of $\mathbb R^4$ (Euclidean and Minkowski)
-- statement:
--   Basic geometry used throughout the mission. Space-time is $\mathbb R^4$ (`EuclideanSpace ℝ (Fin 4)`), and coordinate $0$ is time. An $n$-point configuration $(x_1,\dots,x_n)$ is a point of $\mathbb R^{n\times 4}$. The file defines:
--
--   - time reflection $\vartheta(x^0,\vec x)=(-x^0,\vec x)$;
--   - the Minkowski form $x^2=(x^0)^2-|\vec x|^2$, spacelike vectors, and the closed and open forward cones $\overline V_+$ and $V_+$;
--   - the restricted Lorentz group $L^\uparrow_+=\{\Lambda:\Lambda^T\eta\Lambda=\eta,\ \det\Lambda=1,\ \Lambda^0{}_0\ge1\}$ and the rotation group $SO(4)$;
--   - the coincidence set $\{x: x_i=x_j \text{ for some } i<j\}$;
--   - the Osterwalder–Schrader test-function conditions: ${}^0\mathcal S$ (the function and all its derivatives vanish at coinciding points) and $\mathcal S_+$ (the function and all its derivatives vanish unless $0<x_1^0<\dots<x_n^0$).
-- source:
--   K. Osterwalder, R. Schrader, *Axioms for Euclidean Green's Functions*, Commun. Math. Phys. 31, 83–112 (1973), https://doi.org/10.1007/BF01645738, §2 (test function spaces); A. Jaffe, E. Witten, *Quantum Yang–Mills Theory* (Clay Mathematics Institute Millennium Problem description), https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf, §3

module

public import Mathlib

/-!
# Space-time geometry for the Yang–Mills existence and mass gap mission

Coordinates on `ℝ⁴` are indexed by `Fin 4`; index `0` is the time direction
(`x⁰`), indices `1, 2, 3` are the space directions.  The same underlying space
`ℝ⁴` is used both as Euclidean space (Osterwalder–Schrader side) and as
Minkowski space (Wightman side); only the geometric structure that is used
differs.

An `n`-point configuration `(x₁, …, xₙ)` is an element of
`EuclideanSpace ℝ (Fin n × Fin 4) ≅ ℝ⁴ⁿ`, so that Schwartz functions,
Lebesgue measure and the Fourier transform of Mathlib apply directly.
-/

@[expose] public section

noncomputable section

namespace YangMillsMassGap

open scoped Matrix

/-- A point of space-time `ℝ⁴`. Coordinate `0` is time. -/
abbrev Spacetime := EuclideanSpace ℝ (Fin 4)

/-- A point of space `ℝ³`. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- An `n`-point configuration `(x₁, …, xₙ) ∈ (ℝ⁴)ⁿ`, stored as a point of `ℝ^{n × 4}`. -/
abbrev Config (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin 4)

/-- The `i`-th point `xᵢ ∈ ℝ⁴` of a configuration. -/
def Config.pt {n : ℕ} (x : Config n) (i : Fin n) : Spacetime :=
  WithLp.toLp 2 (fun μ => x (i, μ))

/-- Assemble a configuration from its points. -/
def Config.mk {n : ℕ} (p : Fin n → Spacetime) : Config n :=
  WithLp.toLp 2 (fun iμ => p iμ.1 iμ.2)

/-- The time coordinate `x⁰`. -/
def time (x : Spacetime) : ℝ := x 0

/-- The spatial part of a space-time point. -/
def spatial (x : Spacetime) : Space := WithLp.toLp 2 (fun k : Fin 3 => x k.succ)

/-- The space-time point `(0, a)` with vanishing time component. -/
def ofSpace (a : Space) : Spacetime :=
  WithLp.toLp 2 (Fin.cases 0 (fun k => a k))

/-- The space-time point `(t, 0)` (pure time translation). -/
def ofTime (t : ℝ) : Spacetime := WithLp.toLp 2 (Fin.cases t (fun _ => 0))

/-- Euclidean time reflection `ϑ(x⁰, x⃗) = (-x⁰, x⃗)`. -/
def timeReflect (x : Spacetime) : Spacetime :=
  WithLp.toLp 2 (fun μ => if μ = 0 then -x μ else x μ)

/-- Action of a real `4 × 4` matrix on space-time. -/
def matAct (A : Matrix (Fin 4) (Fin 4) ℝ) (x : Spacetime) : Spacetime :=
  WithLp.toLp 2 (A *ᵥ x.ofLp)

/-- The Minkowski quadratic form `x² = (x⁰)² - |x⃗|²` (signature `(+,-,-,-)`). -/
def minkowskiSq (x : Spacetime) : ℝ := x 0 ^ 2 - (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2)

/-- The Minkowski metric `η = diag(1, -1, -1, -1)`. -/
def minkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun μ => if μ = 0 then 1 else -1)

/-- `x` is spacelike: `x² < 0`. -/
def IsSpacelike (x : Spacetime) : Prop := minkowskiSq x < 0

/-- The closed forward light cone `V̄₊ = {p : p⁰ ≥ 0, p² ≥ 0}`. -/
def closedForwardCone : Set Spacetime := {p | 0 ≤ p 0 ∧ 0 ≤ minkowskiSq p}

/-- The open forward light cone `V₊ = {p : p⁰ > 0, p² > 0}`. -/
def openForwardCone : Set Spacetime := {p | 0 < p 0 ∧ 0 < minkowskiSq p}

/-- The restricted (proper orthochronous) Lorentz group `L↑₊`:
real `4 × 4` matrices `Λ` with `Λᵀ η Λ = η`, `det Λ = 1` and `Λ⁰₀ ≥ 1`. -/
def restrictedLorentz : Set (Matrix (Fin 4) (Fin 4) ℝ) :=
  {Λ | Λᵀ * minkowskiMetric * Λ = minkowskiMetric ∧ Λ.det = 1 ∧ 1 ≤ Λ 0 0}

/-- The rotation group `SO(4)` of Euclidean space-time. -/
def rotationGroup : Set (Matrix (Fin 4) (Fin 4) ℝ) :=
  (Matrix.specialOrthogonalGroup (Fin 4) ℝ : Set (Matrix (Fin 4) (Fin 4) ℝ))

/-- The set of configurations with (at least) two coinciding points,
`{x : xᵢ = xⱼ for some i < j}`. -/
def coincidenceSet (n : ℕ) : Set (Config n) :=
  {x | ∃ i j : Fin n, i < j ∧ x.pt i = x.pt j}

/-- The space `⁰𝒮(ℝ⁴ⁿ)` of Osterwalder–Schrader (1973, §2): a Schwartz function belongs to it
iff it vanishes together with all its partial derivatives at every configuration with two
coinciding points. -/
def VanishesOnCoincidences {n : ℕ} (f : SchwartzMap (Config n) ℂ) : Prop :=
  ∀ (k : ℕ) (x : Config n), x ∈ coincidenceSet n → iteratedFDeriv ℝ k f x = 0

/-- `f` and all its derivatives vanish outside the set `A` (the support condition used by
Osterwalder–Schrader to define `𝒮_{st}`, `𝒮₊`, `𝒮_<`). -/
def DerivsVanishOutside {n : ℕ} (f : SchwartzMap (Config n) ℂ) (A : Set (Config n)) : Prop :=
  ∀ (k : ℕ) (x : Config n), x ∉ A → iteratedFDeriv ℝ k f x = 0

/-- Time-ordered configurations `x₁⁰ < x₂⁰ < ⋯ < xₙ⁰`. -/
def timeOrdered (n : ℕ) : Set (Config n) :=
  {x | ∀ i j : Fin n, i < j → time (x.pt i) < time (x.pt j)}

/-- Positive-time ordered configurations `0 < x₁⁰ < x₂⁰ < ⋯ < xₙ⁰`. -/
def positiveTimeOrdered (n : ℕ) : Set (Config n) :=
  {x | x ∈ timeOrdered n ∧ ∀ i : Fin n, 0 < time (x.pt i)}

/-- `𝒮₊(ℝ⁴ⁿ)` of Osterwalder–Schrader: Schwartz functions which vanish with all derivatives
unless `0 < x₁⁰ < ⋯ < xₙ⁰`. -/
def IsPositiveTimeTest {n : ℕ} (f : SchwartzMap (Config n) ℂ) : Prop :=
  DerivsVanishOutside f (positiveTimeOrdered n)

end YangMillsMassGap

end


