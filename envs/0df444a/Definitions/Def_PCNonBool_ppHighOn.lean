-- Prove2me | Definitions.Def_PCNonBool_ppHighOn
-- name    : PCNonBool_ppHighOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:32:47.966938+00:00
-- url     : https://prove2.me/theorems/18e8d888-ae36-4cdf-aad2-4a45fe29a24f
-- title:
--   The pair set $\mathrm{PPHigh}_D(\pi)$
-- statement:
--   For a real threshold $D$ and a sequence of polynomials $\pi$,
--   $$\mathrm{PPHigh}_D(\pi)=\bigcup_{p\in\pi}\{\,(m_0,m_1)\in\mathrm{Qset}(p) : \mathrm{ppdeg}(m_0,m_1)\ge D\,\},$$
--   the set of unordered monomial pairs of high pairwise pigeon degree. Pairwise pigeon degree is taken in an induced subgraph $G[U_a\sqcup V_a]$. The union is a union of sets.
--
--   The proof of the main theorem shows that each round of Algorithm 1 shrinks $|\mathrm{PPHigh}_D|$ by a factor $1-D/(\Delta N)$, while $|\mathrm{PPHigh}_D(\pi)|\le|\pi|^2$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.5, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_ppdegOn
import Definitions.Def_PCNonBool_qset

namespace PCNonBool

/-- `PPHigh_D(π)`: the set of monomial pairs of the lines of `π` with pairwise pigeon degree at
least `D` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.5, p.27 (PDF p.30): "PPHigh_D(p) = {(m₀, m₁) ∈ Qset(p) :
ppdeg(m₀, m₁) ≥ D} and PPHigh_D(P) = ⋃_{p ∈ P} PPHigh_D(p)"), with `ppdeg` taken in the instance
`G[Ua ⊔ Va]`.

**Formalization Note** The union over lines is a set union: a pair occurring in two lines is
counted once. `D` is real. -/
noncomputable def ppHighOn {F : Type*} [Field F] {U V : Type*} [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (Ua : Finset U) (Va : Finset V) (D : ℝ)
    (π : List (MvPolynomial (Var G) F)) : Finset (Sym2 (Var G →₀ ℕ)) := by
  classical
  exact π.toFinset.biUnion (fun p => (qset p).filter (fun q => D ≤ (ppdegOn G Ua Va q : ℝ)))

end PCNonBool


