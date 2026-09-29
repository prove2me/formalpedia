-- Prove2me | Definitions.Def_ChapterYangMillsGhostSector
-- name    : ChapterYangMillsGhostSector
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-15T20:00:16.435206+00:00
-- url     : https://prove2.me/theorems/77e31679-7b35-4845-95fd-22cce61d825a
-- title:
--   The Faddeev–Popov ghost sector of the 3D gauge-fixed Yang–Mills Hamiltonian The model What is proved Honest boundary
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.YangMillsGhostSector`, source chapter `BookProof/ChapterYangMillsGhostSector.lean`): The Faddeev–Popov ghost sector of the 3D gauge-fixed Yang–Mills Hamiltonian The model What is proved Honest boundary
--
--   The gauge-fixing machinery of the development is algebraic (`BookProof.ChapterGaugeFixing`: the BRST doublets and the gauge-fixing fermion, `BookProof.ChapterGhostField`: the ghost CAR pair and the ghost number operator) and the BRST-gauge-fixed *Hamiltonians* that exist are the gravity ones (`BookProof.ChapterQgBrstDerivativeGauge`). On the Yang–Mills side the Hamiltonian carried no ghost sector at all. This chapter supplies it.
--
--   `K` ghost mode pairs `(c_p, c̄_p)` give a finite-dimensional ghost Fock space with basis the ghost configurations `S ⊆ {0,…,K−1}`, so the total space is the orthogonal direct sum
--
--   `𝔉 = ⨁_{S ⊆ Fin K} L²(ℝ⁹⁹)` (`GhostSpace K`),
--
--   the gauge sector tensored with the ghost Fock space. For a **free** ghost sector — the Faddeev–Popov operator of the abelian gauge fixing is field independent, which is the formal content of `L_gf_evaluation`'s "the ghosts drop out of the physics" — the ghost Hamiltonian is diagonal in that basis, with eigenvalue the ghost energy `E(S) = Σ_{p ∈ S} ω_p`, so the total Hamiltonian is
--
--   `H_tot = H₁ ⊗ 1 + 1 ⊗ H_gh = ⨁_S (H₁ + E(S))` (`ymGhostHam`).
--
--   * `ghostNum`, `ghostEnergy`, `ghostEnergy_empty`, `ghostEnergy_nonneg` — the ghost number and the ghost energy. * `ghostCore`, `ghostCore_dense`, `fibreHam`, `ymGhostHam` — the glued core and the total Hamiltonian, for **every** family of structure constants and every ghost dispersion. * `fibreHam_symmetricOn`, **`ymGhostHam_symmetricOn`** — symmetry, unconditional. * **`ymGhostHam_preserves_ghostNumber`** — ghost number is conserved: the Hamiltonian preserves every ghost-number sector. `ymGhostHam_fibre` and **`ymGhostHam_vacuum_fibre`** — on the ghost vacuum `S = ∅` the total Hamiltonian *is* the gauge-sector Hamiltonian `H₁`: the ghosts decouple. * **`ymGhostHam_essentiallySelfAdjointOn_core`** — for the abelian (QED) gauge fixing `f_abc = 0` the total gauge+ghost Hamiltonian is essentially self-adjoint on the glued Gauss–polynomial core, hence has a unique self-adjoint realization (`ymGhostHam_stone_flow` is the unitary group it generates). * **`ymGhostHam_add_bounded_coupling_esa`** — the same after adding an arbitrary *bounded* symmetric gauge–ghost coupling, by Kato–Rellich: any regulated Faddeev–Popov coupling is covered.
--
--   For `f_abc ≠ 0` the Faddeev–Popov operator depends on the gauge field, so the ghost coupling is an unbounded multiplication operator; neither the free statement nor the bounded-coupling statement applies to it, and the gauge sector itself is then the open quartic problem of `BookProof.ChapterYangMillsBandBounds`. Symmetry, ghost-number conservation and the decoupling of the ghost vacuum hold for every `f_abc`; only the self-adjointness statements are restricted to the abelian case. No mass gap and no spectral claim is made.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsGhostSector.lean

import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterYangMillsAbelianEsa
import Mathlib
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterYangMillsHermite


/-!
# The Faddeev–Popov ghost sector of the 3D gauge-fixed Yang–Mills Hamiltonian

The gauge-fixing machinery of the development is algebraic
(`BookProof.ChapterGaugeFixing`: the BRST doublets and the gauge-fixing fermion,
`BookProof.ChapterGhostField`: the ghost CAR pair and the ghost number operator) and the
BRST-gauge-fixed *Hamiltonians* that exist are the gravity ones
(`BookProof.ChapterQgBrstDerivativeGauge`).  On the Yang–Mills side the Hamiltonian carried
no ghost sector at all.  This chapter supplies it.

## The model

`K` ghost mode pairs `(c_p, c̄_p)` give a finite-dimensional ghost Fock space with basis the
ghost configurations `S ⊆ {0,…,K−1}`, so the total space is the orthogonal direct sum

`𝔉 = ⨁_{S ⊆ Fin K} L²(ℝ⁹⁹)`  (`GhostSpace K`),

the gauge sector tensored with the ghost Fock space.  For a **free** ghost sector — the
Faddeev–Popov operator of the abelian gauge fixing is field independent, which is the formal
content of `L_gf_evaluation`'s "the ghosts drop out of the physics" — the ghost Hamiltonian
is diagonal in that basis, with eigenvalue the ghost energy `E(S) = Σ_{p ∈ S} ω_p`, so the
total Hamiltonian is

`H_tot = H₁ ⊗ 1 + 1 ⊗ H_gh = ⨁_S (H₁ + E(S))`  (`ymGhostHam`).

## What is proved

* `ghostNum`, `ghostEnergy`, `ghostEnergy_empty`, `ghostEnergy_nonneg` — the ghost number and
  the ghost energy.
* `ghostCore`, `ghostCore_dense`, `fibreHam`, `ymGhostHam` — the glued core and the total
  Hamiltonian, for **every** family of structure constants and every ghost dispersion.
* `fibreHam_symmetricOn`, **`ymGhostHam_symmetricOn`** — symmetry, unconditional.
* **`ymGhostHam_preserves_ghostNumber`** — ghost number is conserved: the Hamiltonian
  preserves every ghost-number sector.  `ymGhostHam_fibre` and
  **`ymGhostHam_vacuum_fibre`** — on the ghost vacuum `S = ∅` the total Hamiltonian *is* the
  gauge-sector Hamiltonian `H₁`: the ghosts decouple.
* **`ymGhostHam_essentiallySelfAdjointOn_core`** — for the abelian (QED) gauge fixing
  `f_abc = 0` the total gauge+ghost Hamiltonian is essentially self-adjoint on the glued
  Gauss–polynomial core, hence has a unique self-adjoint realization
  (`ymGhostHam_stone_flow` is the unitary group it generates).
* **`ymGhostHam_add_bounded_coupling_esa`** — the same after adding an arbitrary *bounded*
  symmetric gauge–ghost coupling, by Kato–Rellich: any regulated Faddeev–Popov coupling is
  covered.

## Honest boundary

For `f_abc ≠ 0` the Faddeev–Popov operator depends on the gauge field, so the ghost coupling
is an unbounded multiplication operator; neither the free statement nor the bounded-coupling
statement applies to it, and the gauge sector itself is then the open quartic problem of
`BookProof.ChapterYangMillsBandBounds`.  Symmetry, ghost-number conservation and the
decoupling of the ghost vacuum hold for every `f_abc`; only the self-adjointness statements
are restricted to the abelian case.  No mass gap and no spectral claim is made.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.YangMillsGhost

noncomputable section

open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.YangMillsHermite BookProof.YangMillsAbelianEsa
open BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent

variable {K : ℕ}

/-! ## The ghost configurations -/

/-- A ghost configuration: the set of occupied ghost modes. -/
abbrev GConf (K : ℕ) := Finset (Fin K)

/-- The ghost number of a configuration. -/
def ghostNum (S : GConf K) : ℕ := S.card

/-- The ghost energy of a configuration, for the ghost dispersion `ω`. -/
def ghostEnergy (ω : Fin K → ℝ) (S : GConf K) : ℝ := ∑ p ∈ S, ω p





/-! ## The total space and the glued core -/

/-- The gauge sector tensored with the ghost Fock space: one copy of `L²(ℝ⁹⁹)` for every
ghost configuration. -/
abbrev GhostSpace (K : ℕ) := lp (fun _ : GConf K => L2d 99) 2

/-- The glued Gauss–polynomial core. -/
def ghostCore (K : ℕ) : Submodule ℂ (GhostSpace K) :=
  dsCore (fun _ : GConf K => polyGaussCore (d := 99))



/-! ## The Hamiltonian -/

/-- The fibre Hamiltonian on the ghost configuration `S`: the gauge-fixed Yang–Mills
Hamiltonian shifted by the ghost energy of `S`. -/
def fibreHam (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (ω : Fin K → ℝ) (S : GConf K) :
    polyGaussCore (d := 99) →ₗ[ℂ] L2d 99 :=
  ymHamiltonian (coreRepPoly 99) fabc
    + ((((ghostEnergy ω S : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (L2d 99)).toLinearMap
        ∘ₗ (polyGaussCore (d := 99)).subtype)



/-- **The total gauge + ghost Hamiltonian** `H_tot = ⨁_S (H₁ + E(S))`. -/
def ymGhostHam (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (ω : Fin K → ℝ) :
    ghostCore K →ₗ[ℂ] GhostSpace K :=
  dsOp (fibreHam fabc ω)





/-! ## Symmetry -/





/-! ## Ghost number is conserved -/



/-! ## Essential self-adjointness in the abelian (QED) case -/









end

end BookProof.YangMillsGhost


