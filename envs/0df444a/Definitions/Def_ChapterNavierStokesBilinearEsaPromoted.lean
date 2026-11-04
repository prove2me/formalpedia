-- Prove2me | Definitions.Def_ChapterNavierStokesBilinearEsaPromoted
-- name    : ChapterNavierStokesBilinearEsaPromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-03T12:30:53.412587+00:00
-- url     : https://prove2.me/theorems/4bb121c1-947e-4081-9243-03a6fab4484d
-- title:
--   Bilinear Navier–Stokes generator: block membership
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesBilinearEsa.lean`): `BilinearEsa.blockVec_mem_maxDom` (each block of a finite-mode state lies in the maximal domain of the fiber comparison operator), carved out of ChapterNavierStokesBilinearEsa under the §2.13 new-name route: the served copy predates it, so the `blockVec_bilH` statement, which carries it as a term proof, dies server-side with `Unknown identifier`. Consumers add a single `import Definitions.Def_ChapterNavierStokesBilinearEsaPromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesBilinearEsa.lean

-- Generated from ChapterNavierStokesBilinearEsa.lean — the block membership fact the
-- `blockVec_bilH` statement carries as a term proof, which the platform's served
-- ChapterNavierStokesBilinearEsa copy predates (§2.13 new-name route:
-- submit-definition rejects an existing name, so the decl lives here instead).
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Mathlib

namespace BookProof.NavierStokesFlow

namespace BilinearEsa

open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

/-- Each block of a finite-mode state lies in the maximal domain of the fiber
comparison operator. -/
theorem blockVec_mem_maxDom (κ : J → ℝ) (v : lpFiniteModes (ℕ × J)) (j : J) :
    (blockVec ((v : L2I (ℕ × J))) j) ∈ maxDom (oscSymbol (κ j)) := by
  refine finiteModes_le_maxDom _ (mem_lpFiniteModes.mpr ?_)
  have hv := mem_lpFiniteModes.mp v.2
  have hinj : Function.Injective fun n : ℕ => (n, j) := by
    intro a b hab
    simpa using hab
  have hsub : Function.support
        (fun n : ℕ => (((blockVec ((v : L2I (ℕ × J))) j) : L2I ℕ) : ℕ → ℂ) n)
      ⊆ (fun n : ℕ => (n, j)) ⁻¹' Function.support (((v : L2I (ℕ × J))) : ℕ × J → ℂ) :=
    fun n hn => hn
  exact Set.Finite.subset (Set.Finite.preimage hinj.injOn hv) hsub

end BilinearEsa

end BookProof.NavierStokesFlow


