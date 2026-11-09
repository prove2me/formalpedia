-- Prove2me | Definitions.Def_AbelianCayleyHDX_colGraph
-- name    : AbelianCayleyHDX_colGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:37:41.973463+00:00
-- url     : https://prove2.me/theorems/270b4fdf-624a-4268-9e46-4584781ee5db
-- title:
--   The column graph of $H_D$
-- statement:
--   The graph on the columns $\Omega$ of $H_D$ in which two distinct columns are adjacent when some row of $H_D$ contains both. Lemma 3.5 shows its adjacency matrix is $\tilde H_D^{\mathsf T}\tilde H_D - \rho I$, and Lemma 3.7 that it is connected.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.5, p.12

import Mathlib
import Definitions.Def_AbelianCayleyHDX_HD

namespace AbelianCayleyHDX

/-- **The graph of Lemma 3.5** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.5, p.12): the graph on the columns `Ω` of `H_D` in
which two distinct columns are adjacent when they occur together in a row. Lemma 3.5 shows that its
adjacency matrix is `H̃_Dᵀ H̃_D − ρ I`. -/
def colGraph {t : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F] (D : Finset (PG t F)) :
    SimpleGraph (Omega F t) where
  Adj c c' := c ≠ c' ∧ ∃ r, HD D r c = 1 ∧ HD D r c' = 1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp fun _ hr => ⟨hr.2, hr.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end AbelianCayleyHDX


