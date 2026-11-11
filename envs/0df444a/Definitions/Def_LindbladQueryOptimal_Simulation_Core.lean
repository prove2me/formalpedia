-- Prove2me | Definitions.Def_LindbladQueryOptimal_Simulation_Core
-- name    : LindbladQueryOptimal_Simulation_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:30.586073+00:00
-- url     : https://prove2.me/theorems/84a9a8ac-cc8d-4219-9750-4cf41904c6c8
-- title:
--   Finite matrix, oracle-access, normalization and evolution interfaces
-- statement:
--   Finite qubit registers are indexed by binary words. Rectangular block encodings use the leading-zero isometries of Definition 2, exact unitary compression, positive normalization, and a spectral-norm error tolerance. The matrix on matrix-unit coordinates is the standard generator
--   $$\mathcal L(X)=-i[H,X]+\sum_j\left(L_jXL_j^\dagger-\tfrac12\{L_j^\dagger L_j,X\}\right).$$
--   Its evolution is the actual matrix exponential on that matrix-unit basis. The dissipative normalization is $\Lambda_D=\sum_j\alpha_j^2$, the full normalization is $\alpha_H+\Lambda_D$, and $c(\tau,\epsilon)$ is precisely Eq. (33), including $c(0,\epsilon)=1$. A finite Kraus characterization specifies CPTP maps on all input matrices.
--
--   These are mathematical interfaces, not a simulator circuit or a resource certificate. The trace and diamond norms are imported from the two published references.
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), §§2.1–2.2, pp. 6–8; Eqs. (1), (4)–(7), (33), pp. 2–3, 6–7, 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_RandomDimReduction_Channel_Diamond

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev Op (a : Type) := Matrix a a ℂ

/-- Spectral norm; never the elementwise matrix norm. -/
def spectral {a b : Type} [Fintype a] [Fintype b] (A : Matrix a b ℂ) : ℝ := ‖A‖

def unitary {a : Type} [Fintype a] [DecidableEq a] (U : Op a) : Prop :=
  Uᴴ * U = 1 ∧ U * Uᴴ = 1

/-- Definition 2: leading zero padding, with the system in the final coordinates. -/
def padding (k n : ℕ) : Matrix (Bits n) (Bits k) ℂ := fun x y =>
  if (∀ i : Fin n, i.val < n-k → x i = false) ∧
    (∀ i : Fin k, ∀ j : Fin n, j.val = n-k+i.val → x j = y i) then 1 else 0

def blockEncoding {k l n : ℕ} (α ε : ℝ) (U : Op (Bits n))
    (A : Matrix (Bits k) (Bits l) ℂ) : Prop :=
  k ≤ n ∧ l ≤ n ∧ 0 < α ∧ 0 ≤ ε ∧ unitary U ∧
  spectral (A - (α : ℂ) • ((padding k n)ᴴ * U * padding l n)) ≤ ε

/-- Eq. (1) as an actual matrix on the matrix-unit basis; this generic
finite-dimensional generator is separate from the oracle model. -/
def generator {a : Type} [Fintype a] [DecidableEq a] {m : ℕ}
    (H : Op a) (L : Fin m → Op a) : Op (a × a) := fun x y =>
  -Complex.I * (H x.1 y.1 * (if x.2 = y.2 then 1 else 0) -
    (if x.1 = y.1 then 1 else 0) * H y.2 x.2) +
  ∑ j, (L j x.1 y.1 * star (L j x.2 y.2) - (1/2 : ℂ) *
    (((L j)ᴴ * L j) x.1 y.1 * (if x.2 = y.2 then 1 else 0) +
    (if x.1 = y.1 then 1 else 0) * ((L j)ᴴ * L j) y.2 x.2))

/-- The actual superoperator exponential, not an arbitrary supplied channel. -/
def evolution {a : Type} [Fintype a] [DecidableEq a] {m : ℕ}
    (H : Op a) (L : Fin m → Op a) (t : ℝ) (X : Op a) : Op a :=
  let E := NormedSpace.exp ((t : ℂ) • generator H L)
  fun i j => ∑ y : a × a, E (i,j) y * X y.1 y.2

def dissipativeEvolution {a : Type} [Fintype a] [DecidableEq a]
    (L : Op a) (t : ℝ) : Op a → Op a :=
  evolution 0 (fun _ : Fin 1 => L) t

def dissipativeNormalization {m : ℕ} (α : Fin m → ℝ) : ℝ := ∑ j, α j ^ 2

def normalization {m : ℕ} (αH : ℝ) (α : Fin m → ℝ) : ℝ :=
  αH + dissipativeNormalization α

/-- Eq. (33), including the separate zero-time value. -/
def queryScale (τ ε : ℝ) : ℝ :=
  if τ = 0 then 1 else
    1 + τ + Real.log (1/ε) / Real.log (Real.exp 1 + Real.log (1/ε)/τ)

/-- Finite Kraus characterization of a CPTP map, on all matrices. -/
def channel {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (Φ : Op a → Op b) : Prop :=
  ∃ k : ℕ, ∃ K : Fin k → Matrix b a ℂ,
    (∑ j, (K j)ᴴ * K j) = 1 ∧ ∀ X, Φ X = ∑ j, K j * X * (K j)ᴴ

end LindbladQueryOptimal.Simulation


