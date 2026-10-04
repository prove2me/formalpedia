-- Prove2me | Definitions.Def_ChapterQuantumGravityBrstCharge
-- name    : ChapterQuantumGravityBrstCharge
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T07:36:14.270974+00:00
-- url     : https://prove2.me/theorems/161223f6-a9f5-475b-b15e-3f400bb4eb3a
-- title:
--   Chapter QuantumGravityBrstCharge
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQuantumGravityBrstCharge.lean`): generated def bundle for ChapterQuantumGravityBrstCharge. See BookProof/ChapterQuantumGravityBrstCharge.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityBrstCharge.lean

import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterYangMillsHermite
import Mathlib


/-!
# The BRST charge of the 3D gauge-fixed gravity Hamiltonian: ghosts on `ℤ₂¹⁹` and nilpotency

`CONSOLIDATED_PLAN.md` §10.6.2 item 4 (and `PLAN_LEAN_SPECIALIST_QG_FLOW.md` **Part F**,
items F.6 and F.7) asks for the manuscript's BRST charge `G` — the diffeomorphism, local
Lorentz and translation constraints dressed with the `ℤ₂¹⁹` ghosts — and for its
nilpotency, on the field space of `BookProof/ChapterQuantumGravity3DGauge.lean`.

## What is proved

**The abstract theorem (the general non-abelian BRST charge).**  In any ring that is an
`ℝ`-algebra, for ghost operators satisfying the canonical anticommutation relations
(`BookProof.BRSTNilpotent.GhostCAR`) and constraints `G_a` that commute with the ghosts and
close into a Lie algebra with real structure constants `f`,

```
Ω = Σ_a G_a χ_a − ½ Σ_{a,b,e} f_{abe} χ_a χ_b β_e
```

satisfies **`brst_full_nilpotent`**: `Ω² = 0`.  This is the full charge, not only its cubic
ghost part: `BookProof.ChapterBRSTNilpotent.brst_charge_nilpotent` handles the cubic square
(where the Jacobi identity enters), `glin_sq` computes the square of the constraint part as
half the ghost-contracted constraint algebra, and `glin_mul_Q_add_Q_mul_glin` shows that the
cross terms produce exactly the opposite quantity — the classical cancellation that fixes
the coefficient `−½`.  Nilpotency of the *abelian* charge (`brst_abelian_nilpotent`) is the
special case `f = 0`, and needs no Jacobi identity.

**The ghost sector on `ℤ₂¹⁹` (F.7).**  The `19` diffeomorphism ghosts are realized on the
fermionic Fock space `ghostSpace = Λ(ℂ¹⁹)` (the exterior algebra — the `ℤ₂¹⁹` occupation
space), with `ghostCre a` the exterior multiplication by the `a`-th basis vector and
`ghostAnn a` the contraction against the `a`-th coordinate functional.  `ghost_car` is the
canonical anticommutation relations `{ψ_a, ψ†_b} = δ_{ab}`, `{ψ_a, ψ_b} = 0`,
`{ψ†_a, ψ†_b} = 0` in the `GhostCAR` form.

**The graded field-space (F.6).**  `QGState = ℂ[x₀,…,x₈₃] ⊗ Λ(ℂ¹⁹)` is the
Gauss–polynomial core of `L²(ℝ⁸⁴)` tensored with the ghost sector; `bosOp` and `ghostOp`
embed the operators of the two factors, `bosOp_ghostOp_comm` records that they commute, and
`qgGhostCar` transports the CAR to the graded space.

**The constraints.**  `elemGen j k` is the first-order operator `x_j ∂_k` on the
Gauss-weighted polynomial core and `linGen M = Σ_{j,k} M_{jk} x_j ∂_k` the generator of the
linear change `M` of the field coordinates — the form the diffeomorphism, Lorentz and
translation constraints take on the field space.  `elemGen_bracket` and `linGen_bracket`
prove that these generators **close into the matrix Lie algebra**:
`[linGen M, linGen N] = linGen (MN − NM)`.

**Non-ADM reduction (book.tex ~8226–8244) — the doctrine of this charge.**  When the
globally defined time-like vector is the constant `v^μ = δ^μ_0`, the four-dimensional
Hamiltonian formalism collapses to a three-dimensional one that is **not** the ADM
formalism: the constraint algebra differs (no `H_c = 0` solved for a conformal-mode
curvature `R_c`), ADM is only weakly hyperbolic / not well posed, and the
diffeomorphisms must conserve `v^μ = δ^μ_0`, so the **ghosts of the resulting BRST
charge are constant in the timepiece**, while the charge itself keeps the **same
functional form as the four-dimensional formalism** — explicitly different from the ADM
BRST charge.  The frame time component is fixed by the gravity analogue of the
Yang–Mills Weyl gauge, the gauge-fixing fermion `{G, i b_j A_0^j}`
(`Book/Starobinsky.lean`; plan §QG).  The nilpotency theorem below is proved for that
*functional form*; no ADM truncation of the fields or ghosts is performed, and the
`bookGfTerm_eq_zero_of_Afield0` accounting identity of the Yang–Mills/SM modules is
**not** asserted here (the frame fermion `b_j A_0^j` is not the SM `ψ_a A_{0a}` slice).

**The BRST charge and its nilpotency (F.6).**  `qgBRST M f` is the charge built from a
family `M : Fin 19 → Matrix (Fin 84) (Fin 84) ℝ` of constraint generators, and
**`qgBRST_nilpotent`** proves `Ω² = 0` whenever the family closes with real structure
constants satisfying the Jacobi identity.  `qgBRST_abelian_nilpotent` is the
commuting-family instance, and `affMat`/`affF`/`affMat_close`/`affF_jacobi`/
`affBRST_nilpotent` a concrete **non-abelian** instance — the affine algebra `aff(1)`,
`[H, E] = E`, acting on the first two field coordinates, with `affMat_non_abelian`
recording that the two generators really fail to commute — so the construction is not
vacuous.

## Honest boundary

The charge is built on the *algebraic* graded core `ℂ[x] ⊗ Λ(ℂ¹⁹)` (polynomials times the
Gaussian, tensored with the finite ghost sector), which is the dense domain on which the
field-space Hamiltonian of `ChapterQuantumGravity3DGauge` is defined; no bounded extension
to the completed Hilbert space is claimed, and the reduction of the *dynamics* to BRST
cohomology is the separate `BookProof/ChapterBrstReducedTransfer.lean` (which assumes a
bounded charge).  The constraint family is data: the theorem says that *whenever* the
generators close with real structure constants obeying Jacobi, the charge is nilpotent, and
the `so(3)` instance exhibits a genuinely non-abelian family.  No mass gap and no global
existence statement is made.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QuantumGravityBrstCharge

open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

/-! ## The abstract non-abelian BRST charge -/

section Abstract

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}

/-- The **constraint part** of the BRST charge, `Σ_a G_a χ_a`. -/
def glin (G χ : Fin n → R) : R := ∑ a, G a * χ a

/-- **The BRST charge** `Ω = Σ_a G_a χ_a − ½ Σ_{a,b,e} f_{abe} χ_a χ_b β_e`. -/
def brstCharge (f : Fin n → Fin n → Fin n → ℝ) (G χ β : Fin n → R) : R :=
  glin G χ - (1 / 2 : ℝ) • Q f χ β

/-- The **constraint algebra**: the constraints commute with the ghosts and close with real
structure constants `f`. -/
structure ConstraintAlgebra (f : Fin n → Fin n → Fin n → ℝ) (G χ β : Fin n → R) : Prop where
  /-- the constraints commute with the ghost creation operators -/
  comm_chi : ∀ a b, G a * χ b = χ b * G a
  /-- the constraints commute with the ghost annihilation operators -/
  comm_beta : ∀ a b, G a * β b = β b * G a
  /-- the constraints close: `[G_a, G_b] = Σ_e f_{abe} G_e` -/
  bracket : ∀ a b, G a * G b - G b * G a = ∑ e, f a b e • G e

variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}













end Abstract

/-! ## The constraint generators on the field space

The diffeomorphism, local Lorentz and translation constraints act on the field space by
infinitesimal *linear* changes of the field coordinates, i.e. by the first-order operators
`x_j ∂_k` (here `∂_k` is the covariant derivative `derOp k` of the Gauss-weighted core).
These span a copy of `gl(d)` and are the generators the BRST charge is built from. -/

section Generators

variable {d : ℕ}

/-- The **elementary generator** `E_{jk} = x_j ∂_k` on the Gauss-weighted polynomial core. -/
def elemGen (j k : Fin d) : Module.End ℂ (MvPolynomial (Fin d) ℂ) :=
  (mulOp (X j)).comp (derOp k)







/-- The generator `∑_{j,k} M_{jk} x_j ∂_k` of the linear field-coordinate change `M`, as an
infinitesimally `ℝ`-linear function of `M`. -/
def linGenLM : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] Module.End ℂ (MvPolynomial (Fin d) ℂ) where
  toFun M := ∑ j, ∑ k, (M j k) • elemGen j k
  map_add' A B := by
    simp only [Matrix.add_apply, add_smul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
  map_smul' r A := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

/-- **The constraint generator** attached to a real matrix `M`: `∑_{j,k} M_{jk} x_j ∂_k`. -/
def linGen (M : Matrix (Fin d) (Fin d) ℝ) : Module.End ℂ (MvPolynomial (Fin d) ℂ) := linGenLM M











section SumHelpers

variable {α : Type*}





end SumHelpers







end Generators

/-! ## The ghost sector on `ℤ₂¹⁹` (F.7)

The `19` ghosts live on the fermionic occupation space `ℤ₂¹⁹`, realized as the exterior
algebra `Λ(ℂ¹⁹)`.  Creation is exterior multiplication, annihilation is contraction. -/

/-- The ghost Fock space: the `ℤ₂¹⁹` occupation space `Λ(ℂ¹⁹)`. -/
abbrev ghostSpace : Type := ExteriorAlgebra ℂ (Fin 19 → ℂ)

/-- The ghost **creation** operator `ψ†_a`: exterior multiplication by the `a`-th basis vector. -/
def ghostCre (a : Fin 19) : Module.End ℂ ghostSpace :=
  LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ (Pi.single a 1))

/-- The ghost **annihilation** operator `ψ_a`: contraction against the `a`-th coordinate. -/
def ghostAnn (a : Fin 19) : Module.End ℂ ghostSpace :=
  CliffordAlgebra.contractLeft (LinearMap.proj a)



/-! ## The graded field space (F.6)

The total state space is the Gauss–polynomial core of `L²(ℝ⁸⁴)` tensored with the ghost
sector.  Bosonic and ghost operators embed as `T ⊗ 1` and `1 ⊗ T`, and therefore commute. -/

/-- The bosonic factor: the polynomial core of the `84`-dimensional field space. -/
abbrev qgPoly : Type := MvPolynomial (Fin 84) ℂ

/-- The **graded field space** `ℂ[x₀,…,x₈₃] ⊗ Λ(ℂ¹⁹)`. -/
abbrev QGState : Type := TensorProduct ℂ qgPoly ghostSpace

/-- A bosonic operator, acting as `T ⊗ 1` on the graded space. -/
def bosOp (T : Module.End ℂ qgPoly) : Module.End ℂ QGState := LinearMap.rTensor ghostSpace T

/-- A ghost operator, acting as `1 ⊗ T` on the graded space. -/
def ghostOp (T : Module.End ℂ ghostSpace) : Module.End ℂ QGState := LinearMap.lTensor qgPoly T



















/-- The ghost creation operators on the graded field space. -/
def qgChi (a : Fin 19) : Module.End ℂ QGState := ghostOp (ghostCre a)

/-- The ghost annihilation operators on the graded field space. -/
def qgBeta (a : Fin 19) : Module.End ℂ QGState := ghostOp (ghostAnn a)



/-- The **constraints** attached to a family of linear field-coordinate generators. -/
def qgConstraint (M : Fin 19 → Matrix (Fin 84) (Fin 84) ℝ) (a : Fin 19) : Module.End ℂ QGState :=
  bosOp (linGen (M a))

/-- **The BRST charge of the 3D gauge-fixed gravity field space** (F.6). -/
def qgBRST (M : Fin 19 → Matrix (Fin 84) (Fin 84) ℝ) (f : Fin 19 → Fin 19 → Fin 19 → ℝ) :
    Module.End ℂ QGState :=
  brstCharge f (qgConstraint M) qgChi qgBeta







/-! ## A concrete non-abelian instance

The construction is not vacuous: the two-dimensional non-abelian Lie algebra `[H, E] = E`
(the affine algebra `aff(1)`, realized by the matrix units `E₀₀` and `E₀₁` acting on the first
two field coordinates) closes with real structure constants that are antisymmetric and
satisfy the Jacobi identity, so its BRST charge is nilpotent. -/

/-- Structure-constant kernel of `aff(1)`: `ε_{01} = 1`, `ε_{10} = −1`, all else `0`. -/
def affEps (a b : Fin 19) : ℝ :=
  (if a = 0 ∧ b = 1 then (1 : ℝ) else 0) - (if a = 1 ∧ b = 0 then 1 else 0)

/-- The structure constants of `aff(1)`: `f_{ab}{}^e = ε_{ab} δ^e_1`. -/
def affF (a b e : Fin 19) : ℝ := if e = 1 then affEps a b else 0

/-- The generators of `aff(1)`: `H = E₀₀`, `E = E₀₁`, and `0` for the remaining ghosts. -/
def affMat (a : Fin 19) : Matrix (Fin 84) (Fin 84) ℝ :=
  if a = 0 then Matrix.single 0 0 1 else if a = 1 then Matrix.single 0 1 1 else 0













end

end BookProof.QuantumGravityBrstCharge


