-- Prove2me | Definitions.Def_ChapterNavierStokesCanonicalVector
-- name    : ChapterNavierStokesCanonicalVector
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T00:05:06.243521+00:00
-- url     : https://prove2.me/theorems/2c26314e-2952-435e-a73d-7f30574a35b5
-- title:
--   `BookProof.ChapterNavierStokesThreeComponent` proves that the coupled three-component fiber Hamiltonian
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesCanonicalVector`, source chapter `BookProof/ChapterNavierStokesCanonicalVector.lean`).
--
--   `BookProof.ChapterNavierStokesThreeComponent` proves that the coupled three-component fiber Hamiltonian
--
--   `H = ∑_i ½(π_i V_i + V_i π_i)`, `V_i(u) = ∑_k A_{ik} u_k + c_i`,
--
--   is essentially self-adjoint on the finite-mode core of `ℓ²(Vel)`, `Vel = Fin 3 → ℕ`, for an arbitrary real matrix `A` and an arbitrary real vector `c` — but it does so by *writing down the Hermite matrix* of that operator, and the module records as an honest boundary that "the differential realization on `L²(du₁du₂du₃)` is not built here".
--
--   This module removes that boundary, in the same way that `BookProof.ChapterNavierStokesHermiteCanonical` removed it for the single linear fiber: it builds the three canonical pairs `(u_i, π_i)` out of the Hermite ladder operators and proves that the matrix `velH` **is** the canonically written operator.
--
--   In the Eulerian derivatives-as-fields picture the quadratic symbol of the Navier–Stokes generator at one fiber is
--
--   `A_i(u) = u_j u_{i,j} − ν u_{i,jj}`,
--
--   which is an **affine** function of the velocity `u = (u₁,u₂,u₃)`: its linear part is the velocity-gradient matrix `G_{ij} = u_{i,j}` and its constant part is `−ν u_{i,jj}` (the derivative fields `u_{i,j}`, `u_{i,jj}` are independent canonical coordinates, constants of the motion at the fiber). So the full quadratic symbol is exactly the affine field `V_i` above with `A = G` and `c_i = −ν u_{i,jj}`, and the canonical quantization of the symbol is the Weyl-ordered `∑_i ½(π_i A_i + A_i π_i)`.
--
--   * `ann i`, `cre i` — the annihilation and creation operators of the `i`-th mode on the finite-mode core of `ℓ²(Vel)`, with the full canonical commutation relations `comm_ann_cre` (`[a_i, a_i†] = 1`), `comm_ann_cre_of_ne` (`[a_i, a_k†] = 0`, `i ≠ k`), `ann_comm`, `cre_comm`; * `pos i = (a_i + a_i†)/√2`, `mom i = i(a_i† − a_i)/√2` — the three canonical pairs, with `comm_mom_pos` (`[π_i, u_i] = −i`) and `comm_mom_pos_of_ne` (`[π_i, u_k] = 0`); * `fieldV A c i = ∑_k A_{ik} u_k + c_i` — the affine fiber field, and `canH A c = ∑_i ½(π_i V_i + V_i π_i)` — the Weyl-ordered canonical Hamiltonian; * `canH_eq_velH` — **the identification**: `canH A c` is exactly the Hermite matrix `velH A c` of `ChapterNavierStokesThreeComponent`; * `canH_essentiallySelfAdjointOn_core` — hence the canonically written full quadratic-symbol Hamiltonian is essentially self-adjoint on the finite-mode core; * `nsQuadraticH`, `nsQuadraticH_essentiallySelfAdjointOn_core` — the same statement with the coefficients spelled out as the Navier–Stokes data `(ν, u_{i,j}, u_{i,jj})`.
--
--   The Hilbert space is the Hermite (occupation-number) realization `ℓ²(Fin 3 → ℕ)` of `L²(du₁du₂du₃)` for the three velocity components at one fiber; `pos i` and `mom i` are the canonical pair in that realization, and the operator is the Weyl quantization of the affine symbol. Nothing here claims global regularity of the classical Navier–Stokes equation (Contention D5, the deliberate scope cut).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesCanonicalVector.lean

import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFreeFieldConstraint
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesSignedShift
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterU

import Mathlib

import Mathlib

/-!
# The canonical (differential) form of the full quadratic Navier–Stokes symbol

`BookProof.ChapterNavierStokesThreeComponent` proves that the coupled
three-component fiber Hamiltonian

`H = ∑_i ½(π_i V_i + V_i π_i)`,  `V_i(u) = ∑_k A_{ik} u_k + c_i`,

is essentially self-adjoint on the finite-mode core of `ℓ²(Vel)`, `Vel = Fin 3 → ℕ`,
for an arbitrary real matrix `A` and an arbitrary real vector `c` — but it does so by
*writing down the Hermite matrix* of that operator, and the module records as an honest
boundary that "the differential realization on `L²(du₁du₂du₃)` is not built here".

This module removes that boundary, in the same way that
`BookProof.ChapterNavierStokesHermiteCanonical` removed it for the single linear fiber:
it builds the three canonical pairs `(u_i, π_i)` out of the Hermite ladder operators and
proves that the matrix `velH` **is** the canonically written operator.

## The Navier–Stokes symbol

In the Eulerian derivatives-as-fields picture the quadratic symbol of the Navier–Stokes
generator at one fiber is

`A_i(u) = u_j u_{i,j} − ν u_{i,jj}`,

which is an **affine** function of the velocity `u = (u₁,u₂,u₃)`: its linear part is the
velocity-gradient matrix `G_{ij} = u_{i,j}` and its constant part is `−ν u_{i,jj}` (the
derivative fields `u_{i,j}`, `u_{i,jj}` are independent canonical coordinates, constants
of the motion at the fiber).  So the full quadratic symbol is exactly the affine field
`V_i` above with `A = G` and `c_i = −ν u_{i,jj}`, and the canonical quantization of the
symbol is the Weyl-ordered `∑_i ½(π_i A_i + A_i π_i)`.

## Contents

* `ann i`, `cre i` — the annihilation and creation operators of the `i`-th mode on the
  finite-mode core of `ℓ²(Vel)`, with the full canonical commutation relations
  `comm_ann_cre` (`[a_i, a_i†] = 1`), `comm_ann_cre_of_ne` (`[a_i, a_k†] = 0`, `i ≠ k`),
  `ann_comm`, `cre_comm`;
* `pos i = (a_i + a_i†)/√2`, `mom i = i(a_i† − a_i)/√2` — the three canonical pairs, with
  `comm_mom_pos` (`[π_i, u_i] = −i`) and `comm_mom_pos_of_ne` (`[π_i, u_k] = 0`);
* `fieldV A c i = ∑_k A_{ik} u_k + c_i` — the affine fiber field, and
  `canH A c = ∑_i ½(π_i V_i + V_i π_i)` — the Weyl-ordered canonical Hamiltonian;
* `canH_eq_velH` — **the identification**: `canH A c` is exactly the Hermite matrix
  `velH A c` of `ChapterNavierStokesThreeComponent`;
* `canH_essentiallySelfAdjointOn_core` — hence the canonically written full
  quadratic-symbol Hamiltonian is essentially self-adjoint on the finite-mode core;
* `nsQuadraticH`, `nsQuadraticH_essentiallySelfAdjointOn_core` — the same statement with
  the coefficients spelled out as the Navier–Stokes data `(ν, u_{i,j}, u_{i,jj})`.

## Honest boundary

The Hilbert space is the Hermite (occupation-number) realization `ℓ²(Fin 3 → ℕ)` of
`L²(du₁du₂du₃)` for the three velocity components at one fiber; `pos i` and `mom i` are
the canonical pair in that realization, and the operator is the Weyl quantization of the
affine symbol.  Nothing here claims global regularity of the classical Navier–Stokes
equation (Contention D5, the deliberate scope cut).
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace CanonicalVector

open LpNat FarisLavine IkebeKato ThreeComponent ShiftHamiltonian SignedShift

/-! ## Bookkeeping for the multi-index shifts -/







theorem raise_lower (i : Fin 3) {β : Vel} (h : 1 ≤ β i) : raise i (lower i β) = β := by
  funext j
  by_cases hji : j = i
  · subst hji; rw [raise_self, lower_self]; omega
  · rw [raise_of_ne hji, lower_of_ne hji]



/-! ## The ladder operators of the three modes -/

/-- The coordinates of `a_i x`: `√(β_i + 1) x_{β + e_i}`. -/
noncomputable def aFun (i : Fin 3) (X : Vel → ℂ) : Vel → ℂ :=
  fun β => (Real.sqrt ((β i : ℝ) + 1) : ℂ) * X (raise i β)

/-- The coordinates of `a_i† x`: `√(β_i) x_{β − e_i}`. -/
noncomputable def cFun (i : Fin 3) (X : Vel → ℂ) : Vel → ℂ :=
  fun β => (Real.sqrt (β i : ℝ) : ℂ) * X (lower i β)

theorem support_aFun {i : Fin 3} {X : Vel → ℂ} (h : (Function.support X).Finite) :
    (Function.support (aFun i X)).Finite := by
  refine Set.Finite.subset (h.preimage (f := raise i)
    (Set.injOn_of_injective (raise_injective i))) ?_
  intro β hβ
  simp only [Function.mem_support, aFun] at hβ
  simp only [Set.mem_preimage, Function.mem_support]
  intro h0
  exact hβ (by rw [h0, mul_zero])

theorem support_cFun {i : Fin 3} {X : Vel → ℂ} (h : (Function.support X).Finite) :
    (Function.support (cFun i X)).Finite := by
  refine Set.Finite.subset (h.image (raise i)) ?_
  intro β hβ
  simp only [Function.mem_support, cFun] at hβ
  have hne : X (lower i β) ≠ 0 := fun h0 => hβ (by rw [h0, mul_zero])
  have hpos : 1 ≤ β i := by
    by_contra hcon
    have : β i = 0 := by omega
    apply hβ
    rw [this]
    simp
  exact ⟨lower i β, hne, raise_lower i hpos⟩

/-- A finitely supported coordinate sequence as a state of the finite-mode core. -/
noncomputable def mkCore {X : Vel → ℂ} (h : (Function.support X).Finite) : lpFiniteModes Vel :=
  ⟨⟨X, memLpTwo_of_finite_support h⟩, h⟩

@[simp] theorem mkCore_coe {X : Vel → ℂ} (h : (Function.support X).Finite) (β : Vel) :
    (((mkCore h : lpFiniteModes Vel) : L2I Vel) : Vel → ℂ) β = X β := rfl



theorem support_finite (x : lpFiniteModes Vel) :
    (Function.support (((x : L2I Vel) : Vel → ℂ))).Finite := x.2

/-- **The annihilation operator of the mode `i`.** -/
noncomputable def ann (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel where
  toFun x := mkCore (support_aFun (i := i) (support_finite x))
  map_add' x y := by
    refine Subtype.ext (lp.ext (funext fun β => ?_))
    simp only [mkCore_coe, aFun, Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' a x := by
    refine Subtype.ext (lp.ext (funext fun β => ?_))
    simp only [mkCore_coe, aFun, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

/-- **The creation operator of the mode `i`.** -/
noncomputable def cre (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel where
  toFun x := mkCore (support_cFun (i := i) (support_finite x))
  map_add' x y := by
    refine Subtype.ext (lp.ext (funext fun β => ?_))
    simp only [mkCore_coe, cFun, Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' a x := by
    refine Subtype.ext (lp.ext (funext fun β => ?_))
    simp only [mkCore_coe, cFun, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

/-- The coordinate function of a state. -/
noncomputable def crd (x : lpFiniteModes Vel) : Vel → ℂ := ((x : L2I Vel) : Vel → ℂ)













/-! ## The canonical commutation relations, at the level of coordinates -/























/-! ## The canonical commutation relations, as operator identities -/









/-! ## The three canonical pairs -/



/-- **The fiber coordinate of the mode `i`**, `u_i = (a_i + a_i†)/√2`. -/
noncomputable def pos (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (cre i + ann i)

/-- **The momentum of the mode `i`**, `π_i = i(a_i† − a_i)/√2 = −i ∂/∂u_i`. -/
noncomputable def mom (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  (Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ)) • (cre i - ann i)





/-! ## The coordinates of a signed hop, read off from an incoming term

For each of the four hopping families of `ChapterNavierStokesThreeComponent` the
"incoming" half of the hopping — the value of the Hamiltonian at `γ` coming from the
unique index that hops to `γ` — is a ladder expression, and the following lemma is the
bookkeeping that identifies it as such. -/



variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

/-! ### The diagonal (self-advection) hop -/



/-! ### The strain (symmetric cross) hop -/



/-! ### The vorticity (antisymmetric cross) hop -/



/-! ### The `±1`-hop of the constant part -/



/-! ## The ladder normal form

Both the Hermite matrix `velH` and the canonically written operator reduce to the same
explicit combination of ladder expressions; `ladFun` is that combination. -/

/-- The ladder normal form of the coupled three-component fiber Hamiltonian. -/
noncomputable def ladFun (X : Vel → ℂ) (γ : Vel) : ℂ :=
  Complex.I * ((∑ i, ((A i i / 2 : ℝ) : ℂ) * (cFun i (cFun i X) γ - aFun i (aFun i X) γ))
    + (∑ i, ((c i / Real.sqrt 2 : ℝ) : ℂ) * (cFun i X γ - aFun i X γ))
    + (∑ i, ∑ k, ((coefPair A i k : ℝ) : ℂ) * (cFun i (cFun k X) γ - aFun i (aFun k X) γ))
    + (∑ i, ∑ k, ((coefRot A i k : ℝ) : ℂ) * (cFun i (aFun k X) γ - aFun i (cFun k X) γ)))





/-! ## The canonically written Hamiltonian -/

/-- The coordinates of `u_i x`. -/
noncomputable def pFun (i : Fin 3) (X : Vel → ℂ) : Vel → ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (cFun i X + aFun i X)

/-- The coordinates of `π_i x`. -/
noncomputable def mFun (i : Fin 3) (X : Vel → ℂ) : Vel → ℂ :=
  (Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ)) • (cFun i X - aFun i X)









/-- **The affine fiber field** `V_i(u) = ∑_k A_{ik} u_k + c_i`. -/
noncomputable def fieldV (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  (∑ k, ((A i k : ℝ) : ℂ) • pos k) + (((c i : ℝ) : ℂ) • LinearMap.id)

/-- **The Weyl-ordered canonical Hamiltonian** `∑_i ½(π_i V_i + V_i π_i)`. -/
noncomputable def canH : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  ∑ i, ((1 : ℂ) / 2) • ((mom i).comp (fieldV A c i) + (fieldV A c i).comp (mom i))

/-- The coordinates of the affine fiber field. -/
noncomputable def vFun (i : Fin 3) (X : Vel → ℂ) : Vel → ℂ :=
  (∑ k, ((A i k : ℝ) : ℂ) • pFun k X) + (((c i : ℝ) : ℂ) • X)

/-- The coordinates of the canonical Hamiltonian. -/
noncomputable def canFun (X : Vel → ℂ) (γ : Vel) : ℂ :=
  ∑ i, ((1 : ℂ) / 2) * (mFun i (vFun A c i X) γ + vFun A c i (mFun i X) γ)





/-! ### The Weyl-ordered product of one momentum and one coordinate -/





/-- The Weyl-ordered product `½(π_i u_k + u_k π_i)`, in coordinates. -/
noncomputable def symProdFun (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) : ℂ :=
  ((1 : ℂ) / 2) * (mFun i (pFun k X) γ + pFun k (mFun i X) γ)







/-! ## The identification, and essential self-adjointness of the canonical operator -/





/-- A Hermite basis state of the three-mode core. -/
noncomputable def coreState (β : Vel) : lpFiniteModes Vel :=
  ⟨lp.single 2 β 1, lpSingle_mem_lpFiniteModes β 1⟩



/-! ## The Navier–Stokes reading of the coefficients

At one Eulerian fiber the quadratic symbol of the Navier–Stokes generator is
`A_i(u) = u_j u_{i,j} − ν u_{i,jj}`, an affine function of the velocity whose linear part
is the velocity gradient `u_{i,j}` and whose constant part is `−ν u_{i,jj}` (the derivative
fields are independent canonical coordinates at the fiber).  The following is the theorem
above with the coefficients spelled out that way. -/

/-- **The quantized Navier–Stokes quadratic symbol** `∑_i ½(π_i A_i + A_i π_i)` with
`A_i(u) = ∑_j (grad i j) u_j − ν (lap i)`, on the three-mode Hermite core. -/
noncomputable def nsQuadraticH (nu : ℝ) (grad : Matrix (Fin 3) (Fin 3) ℝ) (lap : Fin 3 → ℝ) :
    lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  canH grad (fun i => -(nu * lap i))





end CanonicalVector

end BookProof.NavierStokesFlow


