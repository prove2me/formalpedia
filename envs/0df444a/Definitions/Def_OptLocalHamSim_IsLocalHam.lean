-- Prove2me | Definitions.Def_OptLocalHamSim_IsLocalHam
-- name    : OptLocalHamSim_IsLocalHam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:45.241179+00:00
-- url     : https://prove2.me/theorems/01dcd44e-a8bb-4b36-85d5-2b8f03b21908
-- title:
--   Geometrically local Hamiltonian $H=\sum_{Z\subseteq\Lambda}h_Z$ of range $R$ and local strength $J$ (Eq. (1)); $H_Y$, $e^{-iHt}$
-- statement:
--   The input Hamiltonian is specified by Hermitian local matrices $h_Z$, one for each set of sites $Z\subseteq\Lambda$, acting on the data qubits of $Z$ and as the identity elsewhere:
--
--   $$
--   H:=\sum_{Z\subseteq\Lambda}h_Z,\qquad \mathrm{diam}(Z)\le R,\qquad \max_{x\in\Lambda}\sum_{Z\ni x}\|h_Z\|\le J .
--   $$
--
--   Every term carries a nonempty declared set of sites $Z$ (a scalar term is located as well), $\|\cdot\|$ is the operator norm, and the local strength sums over the **declared** sets. For a region $Y\subseteq\Lambda$ the restriction keeps the interactions declared inside $Y$,
--
--   $$
--   H_Y:=\sum_{Z\subseteq Y}h_Z ,
--   $$
--
--   and $e^{-iGt}$ denotes the evolution under a Hermitian $G$; the Heisenberg evolution is $\tau_t(O)=e^{iGt}Oe^{-iGt}$.
--
--   Eq. (1) is the class of Hamiltonians for which the paper's simulation bounds hold.
--
--   **Formalization Note** $h$ is a function on all finite sets of sites; $Z$ carries an interaction exactly when $h_Z\ne0$, and then $Z$ is nonempty with $\mathrm{diam}(Z)\le R$. Several terms on the same set are summed, which loses nothing; in particular $h_\emptyset=0$. "Acting on the qubits of $Z$" is the entrywise condition that $h_Z=m\otimes I$ with $m$ on the data qubits of $Z$.
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), §1.1, eq. (1), p.4; §2.1, eq. (4), p.11; App. D, p.59

import Mathlib
import Definitions.Def_OptLocalHamSim_Site

open scoped Matrix Matrix.Norms.L2Operator

namespace OptLocalHamSim

/-- A matrix on the basis states `ι → Bool` of a set of qubits `ι` is **supported on** `S ⊆ ι` if it acts
as the identity on the qubits outside `S`: its entry `(x, y)` vanishes unless `x` and `y` agree off `S`,
and otherwise depends only on the restrictions of `x` and `y` to `S`. Equivalently `A = m ⊗ I_{S^c}`
(Shen, Wu, Yao, Yuan, Zhang, STOC 2027 submission, held version, sha256 44a9768a…, §1.1, p.4: "We write
supp(A) for the smallest set on which A acts nontrivially"). -/
def SupportedOn {ι : Type} (S : Set ι) (A : Matrix (ι → Bool) (ι → Bool) ℂ) : Prop :=
  (∀ x y, (∃ i, i ∉ S ∧ x i ≠ y i) → A x y = 0) ∧
  (∀ x y x' y', (∀ i, i ∉ S → x i = y i) → (∀ i, i ∉ S → x' i = y' i) →
    (∀ i, i ∈ S → x i = x' i ∧ y i = y' i) → A x y = A x' y')

variable {D : ℕ} {L : Fin D → ℕ} {q : ℕ}

/-- The data qubits at the sites of `Z`. -/
def qubitsOf (q : ℕ) (Z : Finset (Site L)) : Set (Dat L q) := {d | d.1 ∈ Z}

/-- **The input Hamiltonian, Eq. (1)** (§1.1, p.4): explicit Hermitian local matrices `h_Z`, one for
each declared set of sites `Z ⊆ Λ`, with `H := ∑_{Z⊆Λ} h_Z`, `diam(Z) ≤ R` and
`max_{x∈Λ} ∑_{Z∋x} ‖h_Z‖ ≤ J`. "Each term is assigned a nonempty set of lattice sites Z".

**Formalization Note**
* `h` is a function on all `Finset`s of sites; a set carrying no interaction has `h Z = 0`, and a term
  is present exactly when `h Z ≠ 0`. Several terms on one `Z` are their sum, so nothing is lost; in
  particular the empty set carries no term (`h ∅ = 0`), and a scalar term sits on a nonempty `Z`.
* `h Z` acts on the data qubits of the sites in `Z` and as the identity elsewhere (`SupportedOn`).
* The local strength `∑_{Z∋x} ‖h_Z‖` runs over the **declared** sets `Z`, as in the paper.
* `‖·‖` is the operator norm (`Matrix.Norms.L2Operator`). `R` is real; distances are natural numbers. -/
def IsLocalHam (R J : ℝ) (h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ) : Prop :=
  (∀ Z, (h Z).IsHermitian) ∧
  (∀ Z, SupportedOn (qubitsOf q Z) (h Z)) ∧
  (∀ Z, h Z ≠ 0 → Z.Nonempty ∧ (diam Z : ℝ) ≤ R) ∧
  (∀ x : Site L, ∑ Z ∈ Finset.univ.filter (fun Z : Finset (Site L) => x ∈ Z), ‖h Z‖ ≤ J)

/-- `H := ∑_{Z⊆Λ} h_Z`, Eq. (1). -/
def Ham (h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ) :
    Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ :=
  ∑ Z, h Z

/-- `H_Y := ∑_{Z⊆Y} h_Z`, Eq. (4), p.11: the interactions whose declared supports lie in `Y`. -/
def HamOn (h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ) (Y : Finset (Site L)) :
    Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ :=
  ∑ Z ∈ Finset.univ.filter (fun Z : Finset (Site L) => Z ⊆ Y), h Z

/-- The evolution `e^{−iGt}` of a matrix `G` for time `t`, the matrix exponential of `−i t G`. -/
noncomputable def evol {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n ℂ) (t : ℝ) :
    Matrix n n ℂ :=
  NormedSpace.exp ((-(Complex.I * (t : ℂ))) • G)

/-- The Heisenberg evolution `τ_t(O) := U(t)† O U(t)` with `U(t) = e^{−iGt}` (App. D, p.59). -/
noncomputable def heis {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n ℂ) (t : ℝ)
    (O : Matrix n n ℂ) : Matrix n n ℂ :=
  (evol G t)ᴴ * O * evol G t

end OptLocalHamSim


