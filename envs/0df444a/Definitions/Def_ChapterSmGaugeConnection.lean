-- Prove2me | Definitions.Def_ChapterSmGaugeConnection
-- name    : ChapterSmGaugeConnection
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:27:19.669857+00:00
-- url     : https://prove2.me/theorems/537e26c6-2dda-4f81-bef4-7d92c16cf9d8
-- title:
--   Chapter SmGaugeConnection
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSmGaugeConnection.lean`): generated def bundle for ChapterSmGaugeConnection. See BookProof/ChapterSmGaugeConnection.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSmGaugeConnection.lean

import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmDiracSpinor
import Mathlib


/-!
# The gauge connection inside the covariant derivative `D`

This module closes the second of the honest boundaries left open by the Standard-Model wave
of `CONSOLIDATED_PLAN.md` §D6b-SM: *“the gauge connection inside `D` is not formalized”*.
`BookProof.ChapterSmDiracSpinor` built the spinor Dirac matrix of a plane-wave mode with
`∂_j ↦ i k_j`; what was missing is the **minimal coupling**

```
D_j = ∂_j + i g_s G^a_j T_a + i g W^k_j (τ_k/2) + i g' B_j Y      (book.tex, §“Majorana
                                                                   spinors in the SM”)
```

i.e. the replacement of `i k_j` by `i (k_j + A_j)` with the Lie-algebra-valued connection
`A_j`.  In the collective-coordinate presentation of §D6b-SM.1 the gauge fields *are*
finitely many real numbers `G^a_j, W^k_j, B_j`, so this module works with a constant
background: one plane-wave matter mode, an arbitrary family of Hermitian generators
`T_a` closing with real structure constants, and arbitrary real field components.

## What is proved

* `conn`, `conn_conjTranspose` — the connection `A_j = g Σ_a A^a_j T_a` is Hermitian when the
  generators are.
* `covD`, `covD_conjTranspose` — the covariant derivative `D_j = i (k_j + A_j)` is
  **anti-Hermitian**, which is what makes `−i γ⁰γ·D` symmetric.
* `covD_zero_coupling` — at zero coupling `D_j` is the free `i k_j`: the connection enters
  `D` only through minimal coupling.
* **`covD_commutator`** — the commutator of two covariant derivatives is the **non-abelian
  field strength**:
  `[D_j, D_l] = −i g² Σ_c (Σ_{a,b} f_{abc} A^a_j A^b_l) T_c`,
  the operator form of `W^j_{μν} = −(i/g) tr([D_μ,D_ν] τ^j)` of `book.tex` and of the
  `g_s f^{abc} G^b_j G^c_k` term of the magnetic energy `B^G` of §D6b-SM.1;
  `covD_commutator_abelian` is its abelian case (a constant abelian background is pure
  gauge: the commutator vanishes).
* **Gauge covariance** — `covD_conj` (conjugating `D` by a unitary conjugates the
  connection) and `conn_gauge_transform` (if the adjoint action of `U` rotates the
  generators by a real matrix `R`, the conjugated connection is again a connection, with
  rotated field components): the space of connections is stable under gauge
  transformations, and `D` transforms covariantly.
* **The gauged Dirac matrix** `diracGaugeMat` — the Hermitian one-particle Dirac matrix on
  `spinor ⊗ internal` with the connection inside `D`
  (`diracGaugeMat_conjTranspose`), which reduces to the free matrix of
  `BookProof.ChapterSmDiracSpinor` at zero field (`diracGaugeMat_free`) and splits as
  free + gauge interaction (`diracGaugeMat_split`).
* **Second quantization** — `diracGaugeField` puts the gauged Dirac matrix on the CAR
  algebra of `BookProof.ChapterSmCarAlgebra` (`4 × 3 = 12` colour–spinor modes),
  `diracGaugeField_symmetric`, and `dirac_gauge_field_esa`: essential self-adjointness
  through the Faris–Lavine hypotheses of `BookProof.ChapterSmDiracYukawa`.

## Honest boundary

The background is constant (one plane-wave matter mode, collective gauge coordinates), so
`D_j` carries `i k_j` rather than an unbounded derivative, and this module’s commutator
`[D_j, D_l]` sees only the non-abelian part of `F` — the `∂_j A_l − ∂_l A_j` term vanishes
because the field is constant by construction (the full `F = ∂A − ∂A + [A,A]` is the
magnetic energy `B^G`/`B^W`/`B^B` of `ChapterSmHamiltonian`).  No dynamics of the gauge
field and no continuum limit of `D` is claimed here.  (The curl/continuum half is reachable
by the momentum-space convolution already used for NS and QG — `fourier_mul_eq_convolution`
/ `fourier_advection_convolution` — not a QYM device, only for proofs of this type.)

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmGaugeConnection

open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.ChapterCPTHamiltonian BookProof.SmCar
open BookProof.SmDiracYukawa BookProof.SmDiracSpinor BookProof.FarisLavine

noncomputable section

variable {N d : ℕ}

/-! ## 1. The connection -/

/-- **The gauge connection** `A_j = g Σ_a A^a_j T_a`: the Lie-algebra-valued one-form built
from the real collective coordinates `A^a_j` of §D6b-SM.1 and the generators `T_a`. -/
def conn (g : ℝ) (T : Fin d → Matrix (Fin N) (Fin N) ℂ) (A : Fin d → Fin 3 → ℝ)
    (j : Fin 3) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ a : Fin d, ((g * A a j : ℝ) : ℂ) • T a







/-! ## 2. The covariant derivative -/

/-- **The covariant derivative of a plane-wave mode**, `D_j = i (k_j + A_j)`: the free
`∂_j ↦ i k_j` with the connection inside it (minimal coupling). -/
def covD (k : Fin 3 → ℝ) (g : ℝ) (T : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (A : Fin d → Fin 3 → ℝ) (j : Fin 3) : Matrix (Fin N) (Fin N) ℂ :=
  Complex.I • (((k j : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) + conn g T A j)













/-! ## 3. Gauge covariance -/





/-! ## 4. The gauged Dirac matrix -/



/-- **The Dirac one-particle matrix with the gauge connection inside `D`**: the Hermitian
matrix `γ⁰γ·(−iD) + masses` on `spinor ⊗ internal`, with `−i D_j = k_j + A_j`. -/
def diracGaugeMat (k : Fin 3 → ℝ) (m1 m2 : ℝ) (g : ℝ) (T : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (A : Fin d → Fin 3 → ℝ) : Matrix (Fin 4 × Fin N) (Fin 4 × Fin N) ℂ :=
  (∑ j : Fin 3, Kin j ⊗ₖ (((k j : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) + conn g T A j))
    + (((-Complex.I) * (m1 : ℂ)) • MassA + ((-Complex.I) * (m2 : ℂ)) • MassB)
        ⊗ₖ (1 : Matrix (Fin N) (Fin N) ℂ)







/-! ## 5. Second quantization on the CAR algebra -/

/-- The colour–spinor mode labelling: the `4 × 3 = 12` modes of one quark flavour at one
plane-wave momentum. -/
def modeEquiv : Fin 4 × Fin 3 ≃ Fin 12 := finProdFinEquiv

/-- **The gauged Dirac field operator**: the second quantization `Σ_{AB} H_{AB} a†_A a_B` of
the gauged Dirac matrix on the CAR algebra of the twelve colour–spinor modes. -/
def diracGaugeField (k : Fin 3 → ℝ) (m1 m2 : ℝ) (g : ℝ) (T : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ)
    (A : Fin 8 → Fin 3 → ℝ) : FermiFock 12 →ₗ[ℂ] FermiFock 12 :=
  fermiBilin (Matrix.reindex modeEquiv modeEquiv (diracGaugeMat k m1 m2 g T A))





end

end BookProof.SmGaugeConnection


