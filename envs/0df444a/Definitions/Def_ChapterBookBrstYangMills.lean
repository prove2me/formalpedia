-- Prove2me | Definitions.Def_ChapterBookBrstYangMills
-- name    : ChapterBookBrstYangMills
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T14:39:11.997977+00:00
-- url     : https://prove2.me/theorems/2dadb410-4a26-4292-9bf0-a8602ab356d0
-- title:
--   Chapter BookBrstYangMills
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterBookBrstYangMills.lean`): generated def bundle for ChapterBookBrstYangMills. See BookProof/ChapterBookBrstYangMills.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBookBrstYangMills.lean

import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterA4
import Mathlib


/-!
# The BRST charge **exactly as defined in `book.tex`**

`book.tex`, chapter *"Quantization due to time-evolution: Yang–Mills and Classical Statistical
Field Theory"*, §*"Pure SU(3) Yang-Mills theory"* (lines ~7060 and ~7343) defines the BRST
charge of a gauge theory with structure constants `f_{abc}` by the **density**

```
Ω(x) = π^μ_a ∂_μ ψ†_a − π^μ_a f_{abc} A_{μb} ψ†_c − (i/2) f_{abc} ψ†_a ψ†_b ψ_c
```

together with the canonical relations of the same section,

```
[A_{μa}, π^ν_b] = i δ^ν_μ δ_{ab},   {ψ_a, ψ†_b} = δ_{ab},   {ψ_a,ψ_b} = {ψ†_a,ψ†_b} = 0 .
```

This module builds that charge: the three terms above, with the momenta, gauge-field
multiplication operators and ghosts realized as operators on a concrete graded state space,
and it *derives* the constraint algebra — the Gauss law — from the canonical relations
instead of assuming it.

## The gauge algebra and the derivative term

The book's gauge field takes values in the Lie algebra of the gauge group at every point of
space.  Here the local gauge algebra is modelled by a finite-dimensional Lie algebra `𝔤`
(basis `T_a`, `a : Fin N`, structure constants `f_{abc}` totally antisymmetric, as for the
book's `SU(N)` generators normalized by `tr(T_aT_b) = ½δ_{ab}`) carrying, for each spacetime
direction `μ`, a **derivation** `∂_μ` (matrix `D μ`).  The derivation property
`∂_μ[X,Y] = [∂_μX,Y] + [X,∂_μY]` is exactly what makes the first term `π^μ_a ∂_μψ†_a` of the
book's charge enter the Gauss-law algebra correctly.  `∂_μ = 0` is the constant
(single-multiplet) case; `∂_μ = ad_{X_μ}` is a non-trivial instance, exhibited below.

## What is proved

* `bookCCR`, `bookGhostCar` — the canonical (anti)commutation relations of the book's section
  hold in the realization: `[A_{μa}, π^ν_b] = i δ^ν_μ δ_{ab}`, `{ψ_a, ψ†_b} = δ_{ab}`, and the
  bosonic and ghost operators commute.
* `gaussGen_bracket` — **the Gauss-law constraint algebra**: the operators `𝒢_c` appearing as
  the coefficient of the ghost `ψ†_c` in the book's charge close into the gauge algebra,
  `[𝒢_c, 𝒢_e] = Σ_h f_{ceh} 𝒢_h`.  This is *derived* from the canonical relations, the
  derivation property of `∂_μ` and the Jacobi identity.
* `bookOmega_eq_brstCharge` — the book's charge is `i` times the abstract BRST charge of
  `BookProof.QuantumGravityBrstCharge` with these constraints; in particular the coefficient
  `−i/2` of the cubic ghost term of `book.tex` is exactly the one nilpotency requires.
* **`bookOmega_nilpotent`** — `Ω² = 0` for the book's charge.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.BookBrstYangMills

open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

/-! ## 1. The gauge algebra with its spacetime derivations -/

/-- The data of the book's gauge algebra: totally antisymmetric structure constants obeying
the Jacobi identity (the `SU(N)` structure constants of the book's §"Pure SU(3) Yang-Mills
theory"), together with the four spacetime derivations `∂_μ` in the same basis,
`∂_μ T_a = Σ_b (D μ)_{ab} T_b`. -/
structure GaugeAlgebra (N : ℕ) where
  /-- structure constants, `[T_a, T_b] = Σ_c f_{abc} T_c` -/
  f : Fin N → Fin N → Fin N → ℝ
  /-- antisymmetry in the first two indices -/
  antisymm : ∀ a b c, f a b c = -f b a c
  /-- cyclic invariance; together with `antisymm` this is total antisymmetry, which is what
  the book's normalization `tr(T_aT_b) = ½δ_{ab}` provides -/
  cyclic : ∀ a b c, f a b c = f b c a
  /-- the Jacobi identity -/
  jacobi : ∀ a b c d, ∑ e, (f a b e * f e c d + f b c e * f e a d + f c a e * f e b d) = 0
  /-- the spacetime derivatives in the basis: `∂_μ T_a = Σ_b (D μ)_{ab} T_b` -/
  D : Fin 4 → Fin N → Fin N → ℝ
  /-- `∂_μ` is a derivation: `∂_μ[T_a,T_b] = [∂_μT_a, T_b] + [T_a, ∂_μT_b]` -/
  leibniz : ∀ μ a b c, ∑ h, f a b h * D μ h c
    = ∑ h, D μ a h * f h b c + ∑ h, D μ b h * f a h c

variable {N : ℕ} (G : GaugeAlgebra N)

/-! ## 2. Two index identities of the gauge algebra -/

/-- The contracted product of two structure constants. -/
def strProd (p q r s : Fin N) : ℝ := ∑ m, G.f p q m * G.f r s m













/-! ## 3. The state space: fields and ghosts -/

/-- The bosonic field coordinates: one polynomial variable per gauge-field component
`A_{μa}`. -/
abbrev FieldPoly (N : ℕ) : Type := MvPolynomial (Fin 4 × Fin N) ℂ

/-- The ghost sector: the `ℤ₂^N` occupation space `Λ(ℂ^N)`, one ghost per gauge generator. -/
abbrev GhostSpace (N : ℕ) : Type := ExteriorAlgebra ℂ (Fin N → ℂ)

/-- The graded state space of the book's section: bosonic fields tensored with ghosts. -/
abbrev BookState (N : ℕ) : Type := TensorProduct ℂ (FieldPoly N) (GhostSpace N)

/-- The ghost creation operator `ψ†_a`. -/
def ghostCreN (a : Fin N) : Module.End ℂ (GhostSpace N) :=
  LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ (Pi.single a 1))

/-- The ghost annihilation operator `ψ_a`. -/
def ghostAnnN (a : Fin N) : Module.End ℂ (GhostSpace N) :=
  CliffordAlgebra.contractLeft (LinearMap.proj a)



/-- A bosonic operator on the graded space. -/
def bosOpN (T : Module.End ℂ (FieldPoly N)) : Module.End ℂ (BookState N) :=
  LinearMap.rTensor (GhostSpace N) T

/-- A ghost operator on the graded space. -/
def ghostOpN (T : Module.End ℂ (GhostSpace N)) : Module.End ℂ (BookState N) :=
  LinearMap.lTensor (FieldPoly N) T

























/-- The ghost creation operator `ψ†_a` on the graded space. -/
def chiOp (a : Fin N) : Module.End ℂ (BookState N) := ghostOpN (ghostCreN a)

/-- The ghost annihilation operator `ψ_a` on the graded space. -/
def betaOp (a : Fin N) : Module.End ℂ (BookState N) := ghostOpN (ghostAnnN a)



/-! ## 4. The gauge field and its conjugate momentum -/

/-- The gauge-field operator `A_{μa}` on the polynomial core: multiplication by the
coordinate. -/
def AfieldPoly (μ : Fin 4) (a : Fin N) : Module.End ℂ (FieldPoly N) :=
  LinearMap.mulLeft ℂ (X (μ, a))

/-- The conjugate momentum `π^μ_a = −i ∂/∂A_{μa}` on the polynomial core. -/
def momPoly (μ : Fin 4) (a : Fin N) : Module.End ℂ (FieldPoly N) :=
  (-Complex.I) • (pderiv (μ, a) : Derivation ℂ (FieldPoly N) (FieldPoly N)).toLinearMap

/-- The gauge-field operator on the graded space. -/
def Afield (μ : Fin 4) (a : Fin N) : Module.End ℂ (BookState N) := bosOpN (AfieldPoly μ a)

/-- The conjugate momentum on the graded space. -/
def mom (μ : Fin 4) (a : Fin N) : Module.End ℂ (BookState N) := bosOpN (momPoly μ a)













/-! ## 5. The Gauss-law constraints -/

/-- An affine combination `α·1 + Σ_g β_g A_{μg}` of the field coordinates in one spacetime
direction: the shape of an infinitesimal gauge transformation of `A_{μa}`. -/
def vecComb (α : ℝ) (β : Fin N → ℝ) (μ : Fin 4) : FieldPoly N :=
  ((α : ℝ) : ℂ) • (1 : FieldPoly N) + ∑ g, ((β g : ℝ) : ℂ) • X (μ, g)





/-- The coefficient polynomials of the Gauss-law vector field: (minus) the infinitesimal gauge
transformation of the coordinate `A_{μa}` generated by `T_c`. -/
def gaussVec (c : Fin N) : (Fin 4 × Fin N) → FieldPoly N := fun i =>
  vecComb (-(G.D i.1 c i.2)) (fun g => G.f i.2 g c) i.1

/-- The Gauss-law generator as a derivation of the field algebra. -/
def gaussDer (c : Fin N) : Derivation ℂ (FieldPoly N) (FieldPoly N) :=
  mkDerivation ℂ (gaussVec G c)

@[simp] theorem gaussDer_X (c : Fin N) (i : Fin 4 × Fin N) :
    gaussDer G c (X i) = gaussVec G c i := mkDerivation_X ℂ _ i







/-- **The Gauss-law constraint** `𝒢_c` on the polynomial core. -/
def gaussGenPoly (c : Fin N) : Module.End ℂ (FieldPoly N) := (gaussDer G c).toLinearMap



/-- **The Gauss-law constraint** `𝒢_c` on the graded state space. -/
def gaussGen (c : Fin N) : Module.End ℂ (BookState N) := bosOpN (gaussGenPoly G c)









/-! ## 6. The book's BRST charge -/

/-- `∂_μψ†_a`, the `a`-component of the spacetime derivative of the ghost field. -/
def dChi (μ : Fin 4) (a : Fin N) : Module.End ℂ (BookState N) :=
  ∑ b, (G.D μ b a) • chiOp b

/-- **The BRST charge of `book.tex`**,
`Ω = π^μ_a ∂_μψ†_a − π^μ_a f_{abc} A_{μb} ψ†_c − (i/2) f_{abc} ψ†_a ψ†_b ψ_c`. -/
def bookOmega : Module.End ℂ (BookState N) :=
  (∑ μ, ∑ a, mom μ a * dChi G μ a)
    - (∑ μ, ∑ a, ∑ b, ∑ c, (G.f a b c) • (mom μ a * Afield μ b * chiOp c))
    - (Complex.I / 2) • (∑ a, ∑ b, ∑ c, (G.f a b c) • (chiOp a * chiOp b * betaOp c))
















end

end BookProof.BookBrstYangMills


