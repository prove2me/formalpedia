-- Prove2me | Definitions.Def_ChapterNavierStokesFlow
-- name    : ChapterNavierStokesFlow
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:21:24.157388+00:00
-- url     : https://prove2.me/theorems/ddbd468e-1ebc-4113-bda2-7b5d3f85243b
-- title:
--   Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical Field Theory and Navier–Stokes equatio ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesFlow`, source chapter `BookProof/ChapterNavierStokesFlow.lean`).
--
--   Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical Field Theory and Navier–Stokes equations"*, §*"Free field parametrization in Navier–Stokes equations"* (`book.tex` ~4133–4216). The correspondence between the book's text and the theorems proved here is:
--
--   * ~4151–4173, degrees of freedom, derivatives treated as fields: `fieldTaylor`, `field_evaluates_to_value`; * ~4163–4170, the canonical commutation relations of the modes: `ccr_field`, `derivativeField_momentum`, `secondDerivativeField_momentum`; * ~4184–4189, the Navier–Stokes Hamiltonian: `nsHamiltonian`, `nsHamiltonian_hermitian`; * ~4199, "polynomial of low degree in the fields": `nsHamiltonian_isPolynomial` (words of length ≤ 3); * ~4191–4197, the divergence constraint and its resolution: `nsDivergenceConstraint_resolution`, `nsBrst_nilpotent`; * ~4199–4208, self-adjointness: `nsHamiltonian_hasZeroDeficiency`, `nsHamiltonian_hasZeroDeficiencyOn` (**truncation only**) and the conditional `ns_esa_of_farisLavine`, `ns_esa_of_farisLavine_dense`; * ~4210–4216, existence and uniqueness of the solution: `nsFlow_group`, `nsFlow_groupOnEvolved`, `nsFlow_noBlowup` (**truncation only**); the differential form — the evolution equation `ψ̇ = i H_N ψ` and the unique solvability of its Cauchy problem — is in the companion module `BookProof.ChapterNavierStokesCauchy`.
--
--   Let `H_N` be the Navier–Stokes Hamiltonian **restricted to a finite truncation** (finitely many field modes `u_k`, `u_{k,j}`, `u_{k,jj}`, each realized by a Hermitian matrix on a finite-dimensional state space, the modes commuting with one another as multiplication operators do). Then
--
--   * `nsHamiltonian_hermitian` — `H_Nᴴ = H_N`; * `nsHamiltonian_isPolynomial` — every term of `H_N` is a word of length at most three in the generators `u_k`, `π_i` (the "low degree in the fields" hypothesis of `book.tex` ~4199); * `nsFlow_zero`, `nsFlow_group`, `nsFlow_unitary` — `U(t) = e^{i t H_N}` is a one-parameter **unitary group**, defined for *every* real time: the flow of the truncation is complete; * `nsFlow_norm_preserving`, `nsFlow_noBlowup` — the flow preserves the `ℓ²` mass and every coefficient of the evolved state stays bounded by the initial mass, uniformly in `t`: **no finite-time singularity on the truncation**; * `nsHamiltonian_hasZeroDeficiency` — the truncated Hamiltonian has vanishing deficiency: `H_N ψ = ± i ψ` forces `ψ = 0`.
--
--   Alongside the truncation the file records the algebraic core of the surrounding construction: the derivatives-as-fields Taylor operator (`Part A`), the Lagrangian change of variables and the volume-preservation constraint (`Part B`), the BRST ghost charge (`Part E`), and the Faris–Lavine framing of the continuum essential-self-adjointness question (`Part G`).
--
--   The essential self-adjointness of the **untruncated continuum** operator `H = ∫ a†(πⁱ(u_j u_{i,j} − ν u_{i,jj}) + h.c.) a`, and with it global existence and uniqueness for the Navier–Stokes equations, is **not** claimed anywhere in this file. The project's own ODE chapter is the standing warning: for `ẋ = x²` the Hamiltonian `x²p̂ − i x̂` is a polynomial of degree 3 whose classical flow `x₀/(1 − t x₀)` is incomplete, so a low-degree polynomial Hamiltonian need *not* be essentially self-adjoint. Accordingly:
--
--   * the degree bound `nsHamiltonian_isPolynomial` is recorded as a **symmetry** statement (a well-defined polynomial operator), never as self-adjointness; * `HasZeroDeficiency` is the deficiency-index-`(0,0)` condition *for the operator itself*; on a finite-dimensional space (where the operator is bounded and everywhere defined) this is exactly essential self-adjointness, and it is proved for the truncation. For an unbounded operator the deficiency spaces are those of the *adjoint*, so the finite statement does not transfer; * `ns_esa_of_farisLavine` and i
--
--   ...
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterFreeFieldConstraint
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterU

import Mathlib
import Mathlib

import Mathlib

import Mathlib

/-!
# Chapter "Free field parametrization … Navier–Stokes": the truncated
Navier–Stokes Hamiltonian generates a **complete flow**

Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical
Field Theory and Navier–Stokes equations"*, §*"Free field parametrization in
Navier–Stokes equations"* (`book.tex` ~4133–4216).  The correspondence between
the book's text and the theorems proved here is:

* ~4151–4173, degrees of freedom, derivatives treated as fields:
  `fieldTaylor`, `field_evaluates_to_value`;
* ~4163–4170, the canonical commutation relations of the modes: `ccr_field`,
  `derivativeField_momentum`, `secondDerivativeField_momentum`;
* ~4184–4189, the Navier–Stokes Hamiltonian: `nsHamiltonian`,
  `nsHamiltonian_hermitian`;
* ~4199, "polynomial of low degree in the fields":
  `nsHamiltonian_isPolynomial` (words of length ≤ 3);
* ~4191–4197, the divergence constraint and its resolution:
  `nsDivergenceConstraint_resolution`, `nsBrst_nilpotent`;
* ~4199–4208, self-adjointness: `nsHamiltonian_hasZeroDeficiency`,
  `nsHamiltonian_hasZeroDeficiencyOn` (**truncation only**) and the conditional
  `ns_esa_of_farisLavine`, `ns_esa_of_farisLavine_dense`;
* ~4210–4216, existence and uniqueness of the solution: `nsFlow_group`,
  `nsFlow_groupOnEvolved`, `nsFlow_noBlowup` (**truncation only**); the
  differential form — the evolution equation `ψ̇ = i H_N ψ` and the unique
  solvability of its Cauchy problem — is in the companion module
  `BookProof.ChapterNavierStokesCauchy`.

## What is proved

Let `H_N` be the Navier–Stokes Hamiltonian **restricted to a finite truncation**
(finitely many field modes `u_k`, `u_{k,j}`, `u_{k,jj}`, each realized by a
Hermitian matrix on a finite-dimensional state space, the modes commuting with
one another as multiplication operators do).  Then

* `nsHamiltonian_hermitian` — `H_Nᴴ = H_N`;
* `nsHamiltonian_isPolynomial` — every term of `H_N` is a word of length at most
  three in the generators `u_k`, `π_i` (the "low degree in the fields"
  hypothesis of `book.tex` ~4199);
* `nsFlow_zero`, `nsFlow_group`, `nsFlow_unitary` — `U(t) = e^{i t H_N}` is a
  one-parameter **unitary group**, defined for *every* real time: the flow of the
  truncation is complete;
* `nsFlow_norm_preserving`, `nsFlow_noBlowup` — the flow preserves the `ℓ²` mass
  and every coefficient of the evolved state stays bounded by the initial mass,
  uniformly in `t`: **no finite-time singularity on the truncation**;
* `nsHamiltonian_hasZeroDeficiency` — the truncated Hamiltonian has vanishing
  deficiency: `H_N ψ = ± i ψ` forces `ψ = 0`.

Alongside the truncation the file records the algebraic core of the surrounding
construction: the derivatives-as-fields Taylor operator (`Part A`), the
Lagrangian change of variables and the volume-preservation constraint
(`Part B`), the BRST ghost charge (`Part E`), and the Faris–Lavine framing of
the continuum essential-self-adjointness question (`Part G`).

## What is *not* claimed

The essential self-adjointness of the **untruncated continuum** operator
`H = ∫ a†(πⁱ(u_j u_{i,j} − ν u_{i,jj}) + h.c.) a`, and with it global existence
and uniqueness for the Navier–Stokes equations, is **not** claimed anywhere in
this file.  The project's own ODE chapter is the standing warning: for `ẋ = x²`
the Hamiltonian `x²p̂ − i x̂` is a polynomial of degree 3 whose classical flow
`x₀/(1 − t x₀)` is incomplete, so a low-degree polynomial Hamiltonian need *not*
be essentially self-adjoint.  Accordingly:

* the degree bound `nsHamiltonian_isPolynomial` is recorded as a **symmetry**
  statement (a well-defined polynomial operator), never as self-adjointness;
* `HasZeroDeficiency` is the deficiency-index-`(0,0)` condition *for the operator
  itself*; on a finite-dimensional space (where the operator is bounded and
  everywhere defined) this is exactly essential self-adjointness, and it is
  proved for the truncation.  For an unbounded operator the deficiency spaces
  are those of the *adjoint*, so the finite statement does not transfer;
* `ns_esa_of_farisLavine` and its densely-defined form
  `ns_esa_of_farisLavine_dense` are **conditional**: the Faris–Lavine commutator
  criterion (Faris–Lavine 1974, Corollary 1.1; Reed–Simon Vol. II Theorem X.28)
  enters as a *named hypothesis*, never as an `axiom`, exactly as Crouzeix's
  inequality does in `BookProof.ChapterH4`.  Verifying its two analytic
  inequalities for the continuum operator is a research target, not a result of
  this file.  The hypothesis is carried in its honest form: symmetry of the
  operator is part of it, since without symmetry the criterion is contradictory
  and the conditional theorem would be vacuous
  (`farisLavine_without_symmetry_forces_trivial`), while with symmetry it is
  satisfiable (`farisLavine_holds_of_everywhereDefined`) — indeed automatic for
  everywhere-defined operators, which is precisely why the analytic content sits
  in the dense-domain predicate `HasZeroDeficiencyOn`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

namespace BookProof.NavierStokesFlow

/-! ## Part A — The field, its derivatives as fields, and the momentum constraint -/

section FieldWithDerivatives

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]

/-- **A.2** The operator-valued field of `book.tex` ~4151–4173,
`φ(X) = φ + φ_i · (X_i − x_i)`: a point value `φ` together with first-order
Taylor coefficients `φ_i`, which are the *derivative fields* `u_{k,j}` of the
truncation and are independent canonical degrees of freedom. -/
def fieldTaylor (phi : E →ₗ[ℂ] E) (phiD : ι → E →ₗ[ℂ] E) (X : ι → E →ₗ[ℂ] E)
    (x : ι → ℂ) : E →ₗ[ℂ] E :=
  phi + ∑ i, (phiD i) ∘ₗ (X i - x i • LinearMap.id)



end FieldWithDerivatives











/-! ## Part B — The Lagrangian change of variables and volume preservation -/







/-- The data of the **Lagrangian (parcel) form** of the transformed
Navier–Stokes operator: the parcel momenta `P` (whose squares are the advective
Laplacian `−½Δ_X`), the viscous gradients `Q`, the drift generators `D` with the
external force `f`, the viscosity `nu ≥ 0`, and the 0-order volume-preservation
constraint `C`. -/
structure LagrangianNS (n : ℕ) where
  /-- Parcel momenta: the advection term is `½ ∑ P_i²`. -/
  P : Fin 3 → Matrix (Fin n) (Fin n) ℂ
  /-- Viscous gradient operators: the viscosity term is `nu ∑ Q_i²`. -/
  Q : Fin 3 → Matrix (Fin n) (Fin n) ℂ
  /-- Drift generators of the external force (a first-order term). -/
  D : Fin 3 → Matrix (Fin n) (Fin n) ℂ
  /-- The external force. -/
  f : Fin 3 → ℝ
  /-- The kinematic viscosity. -/
  nu : ℝ
  /-- The 0-order volume-preservation (pressure/ghost) constraint. -/
  C : Matrix (Fin n) (Fin n) ℂ
  P_herm : ∀ i, (P i)ᴴ = P i
  Q_herm : ∀ i, (Q i)ᴴ = Q i
  D_herm : ∀ i, (D i)ᴴ = D i
  C_herm : Cᴴ = C
  nu_nonneg : 0 ≤ nu

namespace LagrangianNS

variable {n : ℕ} (L : LagrangianNS n)

/-- The advective (kinetic) term `−½Δ_X = ½ ∑ P_i²`: a **positive** second-order
operator after the Lagrangian change of variables. -/
noncomputable def kinetic : Matrix (Fin n) (Fin n) ℂ := ((1 : ℝ) / 2) • ∑ i, L.P i * L.P i

/-- The viscous term `nu ∑ Q_i²`, second order. -/
noncomputable def viscous : Matrix (Fin n) (Fin n) ℂ := L.nu • ∑ i, L.Q i * L.Q i

/-- The force drift `∑ f_i D_i`, first order. -/
noncomputable def drift : Matrix (Fin n) (Fin n) ℂ := ∑ i, L.f i • L.D i

/-- The full transformed operator `ĥ_full = −½Δ_X − νΔ_{ξ,X} − i f·∇_X + Ĥ_c`. -/
noncomputable def hFull : Matrix (Fin n) (Fin n) ℂ := L.kinetic + L.viscous + L.drift + L.C











end LagrangianNS

/-! ## Part C — The finite truncation is a finite Hermitian matrix -/

/-- The data of a **finite truncation** of the Navier–Stokes system: the fifteen
field modes `u_k` (`k = 0,1,2`), `u_{k,j}` (indices `3 … 11`) and `u_{k,jj}`
(indices `12, 13, 14`) of `book.tex` ~4151–4173, realized as Hermitian matrices
on a finite-dimensional state space, together with the three momenta `π_i` and
the viscosity `nu`.  The field modes commute with one another, as multiplication
operators of a common set of coordinates do. -/
structure NSTruncation (n : ℕ) where
  /-- The fifteen field modes. -/
  u : Fin 15 → Matrix (Fin n) (Fin n) ℂ
  /-- The three momenta `π_i`. -/
  mom : Fin 3 → Matrix (Fin n) (Fin n) ℂ
  /-- The kinematic viscosity. -/
  nu : ℝ
  u_herm : ∀ k, (u k)ᴴ = u k
  mom_herm : ∀ i, (mom i)ᴴ = mom i
  u_comm : ∀ k l, u k * u l = u l * u k

/-- **Non-vacuity of the truncation hypotheses.**  Diagonal (multiplication)
field modes with real entries — the finite shadow of the multiplication
operators `u_k(x)` — are Hermitian and commute with one another, so together
with any Hermitian momenta they form a truncation. -/
def nsTruncationOfDiagonal {n : ℕ} (a : Fin 15 → Fin n → ℝ)
    (p : Fin 3 → Matrix (Fin n) (Fin n) ℂ) (hp : ∀ i, (p i)ᴴ = p i) (nu : ℝ) :
    NSTruncation n where
  u k := Matrix.diagonal fun x => (a k x : ℂ)
  mom := p
  nu := nu
  u_herm k := by simp [Matrix.diagonal_conjTranspose]
  mom_herm := hp
  u_comm k l := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp [mul_comm]

/-- The index of the velocity mode `u_j`. -/
def nsVelIdx (j : Fin 3) : Fin 15 := ⟨j.val, by omega⟩

/-- The index of the first-derivative mode `u_{i,j}`. -/
def nsGradIdx (i j : Fin 3) : Fin 15 := ⟨3 + 3 * i.val + j.val, by omega⟩

/-- The index of the second-derivative mode `u_{i,jj}`. -/
def nsLapIdx (i : Fin 3) : Fin 15 := ⟨12 + i.val, by omega⟩

variable {n : ℕ} (d : NSTruncation n)

/-- The velocity mode `u_j`. -/
def nsVelocity (j : Fin 3) : Matrix (Fin n) (Fin n) ℂ := d.u (nsVelIdx j)

/-- The derivative mode `u_{i,j}`. -/
def nsGradVelocity (i j : Fin 3) : Matrix (Fin n) (Fin n) ℂ := d.u (nsGradIdx i j)

/-- The second-derivative mode `u_{i,jj}`. -/
def nsLapVelocity (i : Fin 3) : Matrix (Fin n) (Fin n) ℂ := d.u (nsLapIdx i)

/-- **C.2** The Navier–Stokes term `A_i = ∑_j u_j u_{i,j} − ν u_{i,jj}`
(`book.tex` ~4184–4189): advection minus viscosity. -/
noncomputable def nsAdvection (i : Fin 3) : Matrix (Fin n) (Fin n) ℂ :=
  (∑ j : Fin 3, nsVelocity d j * nsGradVelocity d i j) - (d.nu : ℂ) • nsLapVelocity d i

/-- **C.2** The truncated Navier–Stokes Hamiltonian
`H_N = ∑_i (π_i A_i + A_i π_i)`, the Weyl-symmetrized (anticommutator) form. -/
noncomputable def nsHamiltonian : Matrix (Fin n) (Fin n) ℂ :=
  ∑ i : Fin 3, (d.mom i * nsAdvection d i + nsAdvection d i * d.mom i)







/-- The generators of the truncated algebra: `inl k` is the field mode `u_k`,
`inr i` the momentum `π_i`. -/
def nsGen : Fin 15 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ := Sum.elim d.u d.mom

/-- The index set of the terms of `H_N`: an advection term `(i, j, b)` (with `b`
recording which side the momentum sits on) or a viscous term `(i, b)`. -/
abbrev NSWordIndex := (Fin 3 × Fin 3 × Bool) ⊕ (Fin 3 × Bool)

/-- The word (ordered list of generators) of each term of `H_N`. -/
def nsWord : NSWordIndex → List (Fin 15 ⊕ Fin 3)
  | .inl (i, j, false) => [.inr i, .inl (nsVelIdx j), .inl (nsGradIdx i j)]
  | .inl (i, j, true) => [.inl (nsVelIdx j), .inl (nsGradIdx i j), .inr i]
  | .inr (i, false) => [.inr i, .inl (nsLapIdx i)]
  | .inr (i, true) => [.inl (nsLapIdx i), .inr i]

/-- The scalar coefficient of each term of `H_N`. -/
def nsCoeff (nu : ℝ) : NSWordIndex → ℂ
  | .inl _ => 1
  | .inr _ => -(nu : ℂ)





/-! ## Part D — Complete flow on the truncation (no singularities) -/

/-- **D.1** The flow of the truncated Navier–Stokes Hamiltonian,
`U(t) = e^{i t H_N}`. -/
noncomputable def nsFlowUnitary (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (((t : ℂ) * Complex.I) • nsHamiltonian d)













/-! ## Part E — The divergence constraint and the BRST charge -/

/-- The divergence field `u_{j,j}` of the truncation. -/
noncomputable def nsDivergence : Matrix (Fin n) (Fin n) ℂ := ∑ j : Fin 3, nsGradVelocity d j j

/-- **E.1** The truncated **BRST charge** `Ω = u_{j,j} ⊗ ψ†` on the tensor
product of the bosonic state space with the two-dimensional ghost factor. -/
noncomputable def nsBrstCharge : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  nsDivergence d ⊗ₖ BookProof.GhostField.psiDag









/-! ## Part G — Deficiency, second quantization, and the Faris–Lavine criterion -/

section Deficiency

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Vanishing deficiency** for an operator on a complex inner-product space:
`H ψ = ± i ψ` forces `ψ = 0`, i.e. the deficiency indices are `(0, 0)`.

*Scope.* On a finite-dimensional space (a bounded, everywhere-defined operator)
this is exactly essential self-adjointness.  For an unbounded operator the
deficiency spaces are those of the **adjoint** on its own domain, so this
predicate is the finite/bounded shadow of the analytic notion. -/
def HasZeroDeficiency (H : F →ₗ[ℂ] F) : Prop :=
  (∀ v : F, H v = Complex.I • v → v = 0) ∧ (∀ v : F, H v = -(Complex.I • v) → v = 0)









/-! ### Deficiency of the adjoint on a dense domain

`HasZeroDeficiency` above is the deficiency condition *for the operator itself*,
which is the right notion exactly when the operator is everywhere defined.  The
analytic notion — the one Faris–Lavine is about — asks the deficiency spaces of
the **adjoint** of an operator given on a dense domain `D` to vanish: no `w` may
satisfy `⟪H v, w⟫ = ⟪v, ± i w⟫` for all `v ∈ D` unless `w = 0`.  For `D = ⊤` the
two notions agree (`hasZeroDeficiencyOn_top_of_symmetric`); for a proper dense
domain the second is strictly stronger, and it is *not* claimed here for the
continuum Navier–Stokes operator. -/

/-- Vanishing deficiency of the **adjoint** of an operator `H` defined on the
domain `D`: if `w` satisfies `⟪H v, w⟫ = ⟪v, ± i w⟫` for every `v ∈ D` — that
is, if `w` lies in a deficiency space of `H∗` — then `w = 0`. -/
def HasZeroDeficiencyOn (D : Submodule ℂ F) (H : D →ₗ[ℂ] D) : Prop :=
  (∀ w : F, (∀ v : D, (inner ℂ (H v : F) w : ℂ) = inner ℂ (v : F) (Complex.I • w)) → w = 0) ∧
    (∀ w : F, (∀ v : D, (inner ℂ (H v : F) w : ℂ) = inner ℂ (v : F) (-(Complex.I • w))) → w = 0)

/-- An everywhere-defined operator, viewed as an operator on the domain `⊤`. -/
noncomputable def restrictToTop (H : F →ₗ[ℂ] F) :
    (⊤ : Submodule ℂ F) →ₗ[ℂ] (⊤ : Submodule ℂ F) :=
  LinearMap.codRestrict ⊤ (H.comp (⊤ : Submodule ℂ F).subtype) fun _ => trivial







end Deficiency





/-- **G.1** *The Navier–Stokes Hilbert space is a Fock space over a Fock space.*
The algebraic content is the exponential law `Sym(M × N) ≅ Sym M ⊗ Sym N`
(`BookProof.ChapterU.prodEquiv`): the tensor product of two Fock spaces is again
a Fock space, so the outer (trajectory-indexed) quantization of `nsSecondQuant`
below stays inside the same category and no infinite-dimensional tensor product
is needed. -/
noncomputable def nsFockOfFock (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    SymmetricAlgebra R (M × N) ≃ₐ[R] (SymmetricAlgebra R M ⊗[R] SymmetricAlgebra R N) :=
  BookProof.ChapterU.prodEquiv R M N

/-- **G.1/G.2** The second-quantized ("Fock of a Fock") form of an operator: with
outer ladder operators `A_k` and single-particle kernel `h`,
`Ĥ = ∑_{k,l} h_{kl} A†_k A_l`. -/
noncomputable def nsSecondQuant {m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (h : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ k : Fin m, ∑ l : Fin m, h k l • ((A k)ᴴ * A l)

/-- The outer generators: `inl k` is the creation operator `A†_k`, `inr l` the
annihilation operator `A_l`. -/
def nsOuterGen {m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    Fin m ⊕ Fin m → Matrix (Fin n) (Fin n) ℂ :=
  Sum.elim (fun k => (A k)ᴴ) A



/-- **G.3** The **comparison operator** of the outer Fock layer: the number
operator `N = ∑_k A†_k A_k`, the second-quantized `∫ 𝒩X A†[X] A[X]`. -/
noncomputable def nsNumberOp {m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := ∑ k : Fin m, (A k)ᴴ * A k





end BookProof.NavierStokesFlow


