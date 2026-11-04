-- Prove2me | Definitions.Def_ChapterNavierStokesAffineBlockEsaPromoted
-- name    : ChapterNavierStokesAffineBlockEsaPromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-03T12:31:04.984369+00:00
-- url     : https://prove2.me/theorems/45609940-648c-4b0a-8668-82dcee80cbf2
-- title:
--   Affine-block Navier–Stokes generator: block membership
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesAffineBlockEsa.lean`): `AffineBlock.blockVec_mem_maxDom'` (each block of a finite-mode state lies in the maximal domain of any fiber comparison operator), carved out of ChapterNavierStokesAffineBlockEsa under the §2.13 new-name route: the served copy predates it, so the `blockVec_affBlockH` statement, which carries it as a term proof, dies server-side with `Unknown identifier`. Consumers add a single `import Definitions.Def_ChapterNavierStokesAffineBlockEsaPromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesAffineBlockEsa.lean

-- Generated from ChapterNavierStokesAffineBlockEsa.lean — the block membership fact
-- the `blockVec_affBlockH` statement carries as a term proof, which the platform's
-- served ChapterNavierStokesAffineBlockEsa copy predates (§2.13 new-name route:
-- submit-definition rejects an existing name, so the decl lives here instead).
import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Mathlib

namespace BookProof.NavierStokesFlow

namespace AffineBlock

open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa

variable {J : Type*}

/-- Each block of a finite-mode state lies in the maximal domain of any fiber
comparison operator. -/
theorem blockVec_mem_maxDom' (s : ℕ → ℝ) (v : lpFiniteModes (ℕ × J)) (j : J) :
    (blockVec ((v : L2I (ℕ × J))) j) ∈ maxDom s := by
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

end AffineBlock

end BookProof.NavierStokesFlow


