-- Prove2me | Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
-- name    : InfoLossLAR_WorstCase_LatticeProblems
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:04:30.245581+00:00
-- url     : https://prove2.me/theorems/dab03888-bf3a-4432-bd8a-ff1eaa5be3d4
-- title:
--   Successive minima $\lambda_1,\lambda_N$ and worst-case $\mathrm{GapSVP}_\gamma$, $\mathrm{SIVP}_\gamma$ in dimension $N$
-- statement:
--   For a nonsingular $B\in\mathbb Z^{N\times N}$ the lattice is $\mathcal L(B)=B\mathbb Z^N\subseteq\mathbb R^N$ with the Euclidean norm. $\lambda_1(\mathcal L)$ is the least length of a nonzero lattice vector and $\lambda_N(\mathcal L)$ the least $r$ such that the ball of radius $r$ contains $N$ linearly independent lattice vectors.
--
--   **GapSVP$_\gamma$**: on input $(B,\delta)$ with $\delta>0$ rational, YES if $\lambda_1(\mathcal L(B))\le\delta$, NO if $\lambda_1(\mathcal L(B))>\gamma\delta$. A one-bit algorithm $A$ **solves it in dimension $N$** if for every nonsingular $B\in\mathbb Z^{N\times N}$ and every $\delta>0$
--   $$\lambda_1\le\delta\Rightarrow\Pr[A(B,\delta)=1]\ge\tfrac23,\qquad \lambda_1>\gamma\delta\Rightarrow\Pr[A(B,\delta)=1]\le\tfrac13 .$$
--   **SIVP$_\gamma$**: a multi-output algorithm **solves it in dimension $N$** if on every nonsingular $B\in\mathbb Z^{N\times N}$, with probability at least $\frac23$, its output begins with the code of $N$ linearly independent vectors of $\mathcal L(B)$, each of length at most $\gamma\,\lambda_N(\mathcal L(B))$.
--
--   **Formalization Note.** Worst case over every integer basis given in binary; bounded error $\frac23$ (any constant above $\frac12$ is equivalent by repetition). Lattice vectors of an integer basis are integer vectors and are output as such. $\lambda_1,\lambda_N$ are infima, attained for nonsingular $B$ and $N\ge1$.
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 13 Definition 2.1; p. 60 §10.1; pp. 132–133 Appendix I.1

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_QPT

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

/-!
# Worst-case GapSVP_γ and SIVP_γ in dimension `N`

Chen Qian, *Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices*,
arXiv:2611.05136 (held version, sha256 2ebdfbf3…), Definition 2.1, p. 13 (`L(B) = Bℤ^n`), §10.1,
p. 60 ("GapSVP_γ is the decision shortest-vector problem with approximation gap γ, and SIVP_γ asks
for N independent lattice vectors of length at most γ times the last successive minimum"),
Appendix I.1, pp. 132–133 (via Regev's reduction).

Conventions (the standard ones of the cited [Reg05], which the paper does not restate):
* An instance lattice is `L(B) = Bℤ^N ⊆ ℝ^N` for a nonsingular integer basis `B ∈ ℤ^{N×N}`,
  given in binary; lengths are Euclidean (`‖·‖₂`, `EuclideanSpace`).
* `λ₁(L)` is the least length of a nonzero lattice vector; `λ_N(L)` is the least `r` such that
  the ball of radius `r` contains `N` linearly independent lattice vectors.
* GapSVP_γ: input `(B, δ)` with `δ > 0` rational; YES if `λ₁(L(B)) ≤ δ`, NO if
  `λ₁(L(B)) > γ·δ`. Solving it means accepting every YES instance and rejecting every NO
  instance, each with probability at least `2/3`.
* SIVP_γ: input `B`; output `N` linearly independent vectors of `L(B)` of length at most
  `γ·λ_N(L(B))`, with probability at least `2/3` on every instance. The output string must begin
  with the binary code of the `N` integer vectors (any trailing bits are ignored).
-/

/-- The lattice vector `Bz ∈ ℝ^N` (Euclidean space) for integer coefficients `z`. -/
def latVec {N : ℕ} (B : Matrix (Fin N) (Fin N) ℤ) (z : Fin N → ℤ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => ((B.mulVec z) i : ℝ))

/-- An integer vector as a point of `ℝ^N` (Euclidean space). -/
def intVecE {N : ℕ} (y : Fin N → ℤ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => (y i : ℝ))

/-- The lattice `L(B) = Bℤ^N ⊆ ℝ^N` (Definition 2.1). -/
def lattice {N : ℕ} (B : Matrix (Fin N) (Fin N) ℤ) : Set (EuclideanSpace ℝ (Fin N)) :=
  Set.range (latVec B)

/-- The first successive minimum `λ₁(L(B))`: the infimum of the Euclidean lengths of the nonzero
lattice vectors (attained for a nonsingular `B` and `N ≥ 1`). -/
noncomputable def lam1 {N : ℕ} (B : Matrix (Fin N) (Fin N) ℤ) : ℝ :=
  sInf {r : ℝ | ∃ v ∈ lattice B, v ≠ 0 ∧ ‖v‖ = r}

/-- The `N`-th successive minimum `λ_N(L(B))`: the infimum of the radii `r` for which there are
`N` linearly independent lattice vectors of length at most `r` (attained for a nonsingular
`B`). -/
noncomputable def lamN {N : ℕ} (B : Matrix (Fin N) (Fin N) ℤ) : ℝ :=
  sInf {r : ℝ | ∃ v : Fin N → EuclideanSpace ℝ (Fin N),
    (∀ i, v i ∈ lattice B) ∧ LinearIndependent ℝ v ∧ ∀ i, ‖v i‖ ≤ r}

/-- The binary code of a GapSVP instance `(B, δ)`. -/
def encGapInstance {N : ℕ} (B : Matrix (Fin N) (Fin N) ℤ) (δ : ℚ) : Str :=
  encPair (encMat encI B) (encQ δ)

/-- The one-bit algorithm `A` solves worst-case GapSVP_γ in dimension `N`: for every nonsingular
`B ∈ ℤ^{N×N}` and rational `δ > 0`, it accepts with probability `≥ 2/3` if `λ₁(L(B)) ≤ δ` and
with probability `≤ 1/3` if `λ₁(L(B)) > γ·δ`. -/
def SolvesGapSVP (A : Family) (N : ℕ) (γ : ℝ) : Prop :=
  ∀ B : Matrix (Fin N) (Fin N) ℤ, B.det ≠ 0 → ∀ δ : ℚ, 0 < δ →
    (lam1 B ≤ δ → (2 : ℝ) / 3 ≤ acceptProb A (encGapInstance B δ)) ∧
    (γ * δ < lam1 B → acceptProb A (encGapInstance B δ) ≤ (1 : ℝ) / 3)

/-- The multi-output algorithm `A` solves worst-case SIVP_γ in dimension `N`: on input (the code
of) every nonsingular `B ∈ ℤ^{N×N}`, with probability `≥ 2/3` its output begins with the code of
`N` integer vectors `y_1, …, y_N` that lie in `L(B)`, are linearly independent, and each have
Euclidean length at most `γ·λ_N(L(B))`. -/
def SolvesSIVP (A : MFamily) (N : ℕ) (γ : ℝ) : Prop :=
  ∀ B : Matrix (Fin N) (Fin N) ℤ, B.det ≠ 0 →
    (2 : ℝ) / 3 ≤ outputProb A (encMat encI B) fun out =>
      ∃ y : Fin N → Fin N → ℤ, encVec (encVec encI) y <+: out ∧
        (∀ i, intVecE (y i) ∈ lattice B) ∧ LinearIndependent ℝ (fun i => intVecE (y i)) ∧
        ∀ i, ‖intVecE (y i)‖ ≤ γ * lamN B

end InfoLossLAR.WorstCase


