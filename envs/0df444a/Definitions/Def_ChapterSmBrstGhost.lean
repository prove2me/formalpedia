-- Prove2me | Definitions.Def_ChapterSmBrstGhost
-- name    : ChapterSmBrstGhost
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T07:05:58.845428+00:00
-- url     : https://prove2.me/theorems/a0bb8be9-7a4a-4aea-9198-7f5a494e47db
-- title:
--   Chapter SmBrstGhost
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSmBrstGhost.lean`): generated def bundle for ChapterSmBrstGhost. See BookProof/ChapterSmBrstGhost.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSmBrstGhost.lean

import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterSmCarAlgebra
import Mathlib


/-!
# The ghost / BRST sector of the Standard-Model gauge algebra

This module closes the third honest boundary of the Standard-Model wave of
`CONSOLIDATED_PLAN.md` §D6b-SM: *“the ghost/BRST sector is not built”*.  The Grassmann
coordinates `ζ_F` of §D6b-SM.1 carry, besides the matter fermions, **one ghost per gauge
generator**; the Standard-Model gauge algebra `su(3) ⊕ su(2) ⊕ u(1)` has `8 + 3 + 1 = 12`
generators, so the ghost sector is a twelve-mode CAR algebra, and the BRST charge is

```
Ω = Σ_a c^a G_a − ½ Σ_{a,b,c} f_{abc} c^a c^b b_c .
```

## What is proved

* **The structure constants of the Standard-Model gauge algebra.**  `sumStruct` is the
  direct sum of two structure-constant families, `sumStruct_antisymm` and
  `sumStruct_jacobi` show that antisymmetry and the Jacobi identity are inherited;
  `su2Struct` is the concrete `su(2)` Levi-Civita family (antisymmetry and Jacobi by finite
  check), `u1Struct` the abelian one, and `smStruct f₃` assembles them with an `su(3)`
  family `f₃` into the twelve-generator family, with **`smStruct_antisymm`** and
  **`smStruct_jacobi`**: the Standard-Model gauge algebra has totally antisymmetric
  structure constants obeying Jacobi, which is exactly what BRST needs.
* **The ghost sector on the CAR algebra.**  The ghosts are the last twelve modes of the
  fermionic Fock space of `BookProof.ChapterSmCarAlgebra`; `smGhostCAR` is their canonical
  anticommutation relations, `ghostNumber` the ghost-number operator with
  `ghostNumber_occ` (its spectrum is the ghost occupation number) and the commutators
  `ghostNumber_comm_ghostCre`, `ghostNumber_comm_ghostAnn`.
* **The cubic ghost charge is nilpotent** — `smGhostCharge_nilpotent`, through the project's
  `BookProof.BRSTNilpotent.brst_charge_nilpotent` with the Standard-Model structure
  constants.
* **The full BRST charge is nilpotent** — `brstCharge_nilpotent`, an algebraic theorem in
  any ring carrying ghosts with the CAR and constraint operators `G_a` that commute with
  the ghosts and close with the structure constants: `Ω² = 0`.
* **Second quantization is a Lie-algebra homomorphism** — `fermiBilin_lie`,
  `creat_annih_commutator`: `[dΓ(A), dΓ(B)] = dΓ([A,B])`, so the Gauss-law generators
  `G_a = −i dΓ(T_a)` of the matter sector close with the *real* structure constants
  (`matterGen_lie`), and they commute with the ghosts (`matterGen_comm_ghostCre`,
  `matterGen_comm_ghostAnn`) because they are even.
* **The Standard-Model BRST charge** `smBrstCharge` on the joint matter ⊗ ghost Fock space,
  with **`smBrstCharge_nilpotent`**: `Ω² = 0`, which is what makes the BRST cohomology —
  the physical sector — well defined.

## Honest boundary

The mode set here is finite: one plane-wave matter multiplet and the twelve ghosts, i.e. the
gauge algebra of the collective-coordinate presentation of §D6b-SM.1.  The charge used in
this module is the abstract one, with the constraints `G_a` given as data.  The BRST charge
**as `book.tex` itself defines it** — the density
`Ω = π^μ_a ∂_μψ†_a − π^μ_a f_{abc}A_{μb}ψ†_c − (i/2) f_{abc}ψ†_aψ†_bψ_c` with the book's
canonical relations, the Gauss law *derived* from them, and the gauge-fixing fermion
`Ψ = i ψ_a A_{0a}` — is built in `BookProof.ChapterBookBrstYangMills`,
`BookProof.ChapterBookBrstGaugeFixing` and `BookProof.ChapterBookBrstInstances`, the last of
which instantiates it with the Standard-Model structure constants `smStruct f₃`.  The
`su(3)` structure constants enter as a family satisfying antisymmetry and Jacobi (which
`BookProof.ChapterYangMillsSU3` derives for trace-orthonormal generators); the book's
formalism uses no Faddeev–Popov determinant and none is constructed, and no statement about
the *size* of the BRST cohomology is made.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmBrstGhost

open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

/-! ## 1. The structure constants of `su(3) ⊕ su(2) ⊕ u(1)` -/

/-- The direct sum of two families of structure constants: a bracket never leaves its
summand. -/
def sumStruct {ι κ : Type*} (f1 : ι → ι → ι → ℝ) (f2 : κ → κ → κ → ℝ) :
    (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ
  | Sum.inl a, Sum.inl b, Sum.inl c => f1 a b c
  | Sum.inr a, Sum.inr b, Sum.inr c => f2 a b c
  | _, _, _ => 0





/-- The Levi-Civita symbol on three indices, as an integer. -/
def epsZ (a b c : Fin 3) : ℤ :=
  if a = b ∨ b = c ∨ a = c then 0
  else if (a, b) = ((0 : Fin 3), (1 : Fin 3)) ∨ (a, b) = ((1 : Fin 3), (2 : Fin 3))
        ∨ (a, b) = ((2 : Fin 3), (0 : Fin 3)) then 1 else -1

/-- **The `su(2)` structure constants** `ε_{jkl}`. -/
def su2Struct (a b c : Fin 3) : ℝ := (epsZ a b c : ℝ)

/-- **The `u(1)` structure constants**: an abelian factor has none. -/
def u1Struct (_ _ _ : Fin 1) : ℝ := 0













/-- The twelve generator labels of the Standard-Model gauge algebra, split into the eight
gluon, three weak and one hypercharge directions. -/
def smIdxEquiv : Fin 12 ≃ (Fin 8 ⊕ (Fin 3 ⊕ Fin 1)) :=
  (finCongr (by norm_num : (12 : ℕ) = 8 + (3 + 1))).trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin 8)) finSumFinEquiv.symm))

/-- **The structure constants of the Standard-Model gauge algebra** `su(3) ⊕ su(2) ⊕ u(1)`,
given those of `su(3)`. -/
def smStruct (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ) (a b c : Fin 12) : ℝ :=
  sumStruct f3 (sumStruct su2Struct u1Struct) (smIdxEquiv a) (smIdxEquiv b) (smIdxEquiv c)





/-! ## 2. The ghost sector inside the CAR algebra -/

variable {m : ℕ}

/-- The mode carrying the `a`-th ghost: the ghosts are the last twelve modes of the
fermionic Fock space, the matter modes being the first `m`. -/
def ghostMode (m : ℕ) (a : Fin 12) : Fin (m + 12) := Fin.natAdd m a

/-- The **ghost creation** operator `c^a`. -/
def ghostCre (m : ℕ) (a : Fin 12) : Module.End ℂ (FermiFock (m + 12)) :=
  creat (ghostMode m a)

/-- The **ghost annihilation** (antighost) operator `b_a`. -/
def ghostAnn (m : ℕ) (a : Fin 12) : Module.End ℂ (FermiFock (m + 12)) :=
  annih (ghostMode m a)





/-- **The ghost-number operator** `Σ_a c^a b_a`. -/
def ghostNumber (m : ℕ) : Module.End ℂ (FermiFock (m + 12)) :=
  ∑ a : Fin 12, ghostCre m a * ghostAnn m a



















/-- **The cubic ghost part of the Standard-Model BRST charge.** -/
def smGhostCharge (m : ℕ) (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    Module.End ℂ (FermiFock (m + 12)) :=
  Q (smStruct f3) (ghostCre m) (ghostAnn m)



/-! ## 3. The full BRST charge, in the abstract -/

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}





/-- **The BRST charge** `Ω = Σ_a c^a G_a − ½ f_{abc} c^a c^b b_c` of a family of first-class
constraints `G_a`. -/
def brstCharge (f : Fin n → Fin n → Fin n → ℝ) (χ β : Fin n → R) (G : Fin n → R) : R :=
  (∑ a, χ a * G a) - (1 / 2 : ℝ) • Q f χ β



/-! ## 4. The Gauss-law constraints: second quantization as a Lie homomorphism -/

variable {N : ℕ}



























/-! ## 5. The Standard-Model BRST charge -/

/-- The matter block of a one-particle operator, embedded in the joint matter ⊗ ghost mode
set: the operator acts on the first `m` modes and annihilates the ghosts. -/
def embedMatter (m : ℕ) (M : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin (m + 12)) (Fin (m + 12)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 0)

/-- **The Gauss-law generator** of the `a`-th gauge direction: the second quantization
`−i dΓ(T_a)` of the one-particle generator on the matter modes. -/
def matterGen (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ) (a : Fin 12) :
    Module.End ℂ (FermiFock (m + 12)) :=
  (-Complex.I) • fermiBilin (embedMatter m (T a))



















/-- **The Standard-Model BRST charge** on the joint matter ⊗ ghost Fock space. -/
def smBrstCharge (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ)
    (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ) : Module.End ℂ (FermiFock (m + 12)) :=
  brstCharge (smStruct f3) (ghostCre m) (ghostAnn m) (matterGen m T)



end

end BookProof.SmBrstGhost


