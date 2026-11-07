-- Prove2me | Definitions.Def_PCNonBool_ppdegSeq
-- name    : PCNonBool_ppdegSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:32:28.199959+00:00
-- url     : https://prove2.me/theorems/ba1d3d58-e053-4977-8d6b-3e1f65d11b58
-- title:
--   Pairwise pigeon degree of a refutation
-- statement:
--   The **pairwise pigeon degree** of a polynomial $p$ is $\max_{m_0,m_1\in p}\mathrm{ppdeg}(m_0,m_1)$, and that of a sequence of polynomials is the maximum over its lines. A refutation "has pairwise pigeon degree $D$" if this maximum is at most $D$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.5, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_ppdegOn
import Definitions.Def_PCNonBool_qset

namespace PCNonBool

/-- The pairwise pigeon degree of a sequence of polynomials in FPHP(G)'s variables: the largest
`ppdeg` of a pair in the Qset of a line (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.5, p.27 (PDF p.30):
"ppdeg(p) = max_{m₀,m₁ ∈ p} ppdeg(m₀, m₁)", "ppdeg(P) = max_{p ∈ P} ppdeg(p)"). -/
noncomputable def ppdegSeq {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (G : BipGraph U V) (π : List (MvPolynomial (Var G) F)) : ℕ :=
  (π.map fun p => (qset p).sup (ppdegOn G Finset.univ Finset.univ)).foldr max 0

end PCNonBool


