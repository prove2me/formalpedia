-- Prove2me | Definitions.Def_LindbladShallow_gksl
-- name    : LindbladShallow_gksl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:14:02.796504+00:00
-- url     : https://prove2.me/theorems/1a031447-5103-488f-9f74-4884a57a7dfa
-- title:
--   Superoperator exponential, GKSL generators, Cayley gates and the reduced jump channel
-- statement:
--   For a superoperator $\mathcal L$ on $n\times n$ complex matrices and real $t$, $e^{t\mathcal L}=\sum_k t^k\mathcal L^k/k!$. The **Hamiltonian superoperator** is $\mathcal H_H(Z)=-i[H,Z]$, the **dissipator** of one jump operator is $Z\mapsto LZL^\dagger-\tfrac12\{L^\dagger L,Z\}$, and the **GKSL generator** with Hamiltonian $H$ and jump list $(L_\mu)$ is
--   $$\mathcal L(\rho)=-i[H,\rho]+\sum_\mu\Big(L_\mu\rho L_\mu^\dagger-\tfrac12\{L_\mu^\dagger L_\mu,\rho\}\Big).$$
--   A superoperator is a GKSL generator if it has this form for some Hermitian $H$ and finitely many $L_\mu$.
--
--   The **Cayley map** is $A\mapsto (I-iA/2)(I+iA/2)^{-1}$; the Hamiltonian collision gate is $V_{H,h}=\mathrm{cayley}(hH)$. For a stacked jump map $J\psi=\sum_\mu|\mu\rangle L_\mu\psi$ the coupling on system $\otimes$ bath is
--   $$G_J=\begin{pmatrix}0&J^\dagger\\ J&0\end{pmatrix},\qquad V_{J,h}=(I-i\sqrt h\,G_J/2)(I+i\sqrt h\,G_J/2)^{-1},$$
--   where the bath has basis $\{0,1,\dots,d\}$, $0$ is the vacuum and value $\mu+1$ carries the component $L_\mu$. The stacked dissipator is $\mathcal D_J(Z)=\sum_\mu L_\mu ZL_\mu^\dagger-\tfrac12\{J^\dagger J,Z\}$, and the **reduced Cayley channel** is $\Phi_{J,h}(Z)=\mathrm{Tr}_{\mathrm{bath}}[V_{J,h}(Z\otimes|0\rangle\langle0|)V_{J,h}^\dagger]$.
--
--   These are the local building blocks of the collision representation (§2.3) and of the error analysis of Appendix A.
--
--   **Formalization Note** The exponential is Mathlib's `NormedSpace.exp` applied to the matrix of $\mathcal L$ in the standard basis of matrix space; it does not depend on the basis or on any norm. The matrix inverse in the Cayley map is Mathlib's (junk value $0$ on singular matrices), but $I+iA/2$ is invertible for Hermitian $A$, which is the only case used.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Eq. (1), p.1; §2.2, p.10; §2.3, p.12; Lemma A.1, p.58

import Mathlib
import Definitions.Def_LindbladShallow_dnorm

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- The exponential `e^{tℒ}` of a superoperator `ℒ` on `n × n` complex matrices, for real `t`
(arXiv:2610.05362, held version sha256 8f4637ef…: the target channel `e^{Tℒ}`, Eq. (1), p.1;
`e^{hℒ_e}`, Lemma A.3, p.60).

**Formalization Note** `ℒ` is written as a matrix in the standard basis of `Matrix n n ℂ` and
`NormedSpace.exp` (the power series `Σ_k (tℒ)^k / k!`) is taken there; since the matrix
representation is an algebra isomorphism, the result does not depend on the basis or on any
norm. -/
noncomputable def supExp {n : Type*} [Fintype n] [DecidableEq n] (t : ℝ)
    (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  (LinearMap.toMatrixAlgEquiv (Matrix.stdBasis ℂ n n)).symm
    (NormedSpace.exp ((t : ℂ) • LinearMap.toMatrixAlgEquiv (Matrix.stdBasis ℂ n n) L))

/-- The Hamiltonian superoperator `ℋ_H(Z) := −i[H, Z]` (arXiv:2610.05362, §2.2, p.10). -/
noncomputable def hamSup {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  (-Complex.I) • (LinearMap.mulLeft ℂ H - LinearMap.mulRight ℂ H)

/-- The dissipator of one jump operator, `Z ↦ L Z L† − ½{L†L, Z}` (arXiv:2610.05362, Eq. (1),
p.1). -/
noncomputable def jumpSup {n : Type*} [Fintype n] [DecidableEq n] (L : Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  LinearMap.mulLeft ℂ L ∘ₗ LinearMap.mulRight ℂ Lᴴ -
    (1 / 2 : ℂ) • (LinearMap.mulLeft ℂ (Lᴴ * L) + LinearMap.mulRight ℂ (Lᴴ * L))

/-- The Gorini–Kossakowski–Sudarshan–Lindblad generator with Hamiltonian `H` and jump operators
`Ls`: `ℒ(ρ) = −i[H, ρ] + Σ_{L ∈ Ls} (L ρ L† − ½{L†L, ρ})` (arXiv:2610.05362, Eq. (1), p.1). -/
noncomputable def gksl {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (Ls : List (Matrix n n ℂ)) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  hamSup H + (Ls.map jumpSup).sum

/-- `ℒ` is a (finite-dimensional) GKSL generator: `ℒ = −i[H, ·] + Σ_µ (L_µ · L_µ† − ½{L_µ†L_µ, ·})`
for some Hermitian `H` and some finite list of jump operators (arXiv:2610.05362, Lemma A.3,
p.60; form of Eq. (1)). -/
def IsGKSL {n : Type*} [Fintype n] [DecidableEq n] (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    Prop :=
  ∃ H : Matrix n n ℂ, H.IsHermitian ∧ ∃ Ls : List (Matrix n n ℂ), L = gksl H Ls

/-- The Cayley map `A ↦ (I − iA/2)(I + iA/2)^{−1}` (arXiv:2610.05362, §2.3, p.12:
`V_{H,h} = cayley (h H)`, `V_{J,h} = cayley (√h G_J)`; Lemma A.2, p.59: `C_H(h) = cayley (h H)`).

**Formalization Note** `⁻¹` is Mathlib's matrix inverse (`0` on singular matrices); for Hermitian
`A` the matrix `I + iA/2` is invertible, so no junk value arises where the paper uses it. -/
noncomputable def cayley {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Matrix n n ℂ :=
  (1 - (Complex.I / 2) • A) * (1 + (Complex.I / 2) • A)⁻¹

/-- The occupied value of a bath basis state: `0` (vacuum) ↦ `none`, `µ + 1` ↦ `some µ`. -/
def occ {d : ℕ} (μ : Fin (d + 1)) : Option (Fin d) :=
  Fin.cases (motive := fun _ => Option (Fin d)) none (fun k => some k) μ

/-- The coupling `G_J := [[0, J†], [J, 0]]` on system ⊗ bath for a stacked jump map
`J ψ = Σ_µ |µ⟩ L_µ ψ` (arXiv:2610.05362, §2.3, p.12). The bath has basis `Fin (d + 1)`: value `0`
is the vacuum and value `µ + 1` carries the jump component `µ : Fin d`; `J` is the matrix
`(Fin d × σ) × σ` with blocks `L_µ`. `G_J` couples the vacuum sector with the occupied sector. -/
def gJ {σ : Type*} {d : ℕ} (J : Matrix (Fin d × σ) σ ℂ) :
    Matrix (σ × Fin (d + 1)) (σ × Fin (d + 1)) ℂ :=
  Matrix.of fun p q =>
    match occ p.2, occ q.2 with
    | some k, none => J (k, p.1) q.1
    | none, some k => star (J (k, q.1) p.1)
    | _, _ => 0

/-- The jump Cayley gate `V_{J,h} := (I − i√h G_J/2)(I + i√h G_J/2)^{−1}` on system ⊗ bath
(arXiv:2610.05362, §2.3, p.12). -/
noncomputable def cayleyJ {σ : Type*} [Fintype σ] [DecidableEq σ] {d : ℕ} (h : ℝ)
    (J : Matrix (Fin d × σ) σ ℂ) : Matrix (σ × Fin (d + 1)) (σ × Fin (d + 1)) ℂ :=
  cayley (((Real.sqrt h : ℝ) : ℂ) • gJ J)

/-- The `µ`-th block `L_µ` of a stacked jump map `J = Σ_µ |µ⟩ ⊗ L_µ`. -/
def jblock {σ : Type*} {d : ℕ} (J : Matrix (Fin d × σ) σ ℂ) (μ : Fin d) : Matrix σ σ ℂ :=
  Matrix.of fun i j => J (μ, i) j

/-- The dissipator of a stacked jump map, `𝒟_J(Z) := Σ_µ L_µ Z L_µ† − ½{J†J, Z}`
(arXiv:2610.05362, §2.2, p.10; `J†J = Σ_µ L_µ†L_µ`). -/
noncomputable def dissJ {σ : Type*} [Fintype σ] [DecidableEq σ] {d : ℕ}
    (J : Matrix (Fin d × σ) σ ℂ) : Matrix σ σ ℂ →ₗ[ℂ] Matrix σ σ ℂ :=
  ∑ μ, jumpSup (jblock J μ)

/-- The reduced Cayley channel `Φ_{J,h}(Z) := Tr_bath[V_{J,h}(Z ⊗ |0⟩⟨0|)V_{J,h}†]` of one jump
Cayley gate on one fresh vacuum bath (arXiv:2610.05362, §2.3, p.12; Lemma A.1, p.58). -/
noncomputable def reducedJ {σ : Type*} [Fintype σ] [DecidableEq σ] {d : ℕ} (h : ℝ)
    (J : Matrix (Fin d × σ) σ ℂ) : QAlgorithms.Superop σ σ :=
  isoChannel (cayleyJ h J * vacIso (0 : Fin (d + 1)))

end LindbladShallow


