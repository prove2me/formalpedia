-- Prove2me | Definitions.Def_PCNonBool_parityAxioms
-- name    : PCNonBool_parityAxioms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:50.421031+00:00
-- url     : https://prove2.me/theorems/00895f0f-a1cb-462f-b316-90aadf36698a
-- title:
--   Parity axioms $\mathrm{PA}(G)$
-- statement:
--   The **parity axioms** of FPHP$(G)$ are
--   $$\mathrm{PA}(G)=\Bigl\{\prod_{j\in N(i)}x_{i,j}+1 \ :\ i\in U\Bigr\}.$$
--   Over $\pm1$ assignments, the parity axiom of pigeon $i$ says that an odd number of the variables of $i$ equal $-1$; it is implied by the axioms of pigeon $i$ in FPHP$(G)$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5.1 (parity axioms), p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_xv

namespace PCNonBool

/-- The parity axioms of FPHP(G), `PA(G) = {∏_{j ∈ N(i)} x_{i,j} + 1 | i ∈ U}`
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5.1, p.27 (PDF p.30)). -/
def parityAxioms {F : Type*} [Field F] {U V : Type*} [Fintype V] (G : BipGraph U V) :
    Set (MvPolynomial (Var G) F) :=
  {p | ∃ i : U, p = (∏ j ∈ nbrOn G Finset.univ i, xv G i j) + 1}

end PCNonBool


