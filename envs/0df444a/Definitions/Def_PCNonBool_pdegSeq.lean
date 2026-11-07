-- Prove2me | Definitions.Def_PCNonBool_pdegSeq
-- name    : PCNonBool_pdegSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:51.305461+00:00
-- url     : https://prove2.me/theorems/b9254ceb-d268-4e09-bf25-e60d13a79e60
-- title:
--   Pigeon degree of a refutation
-- statement:
--   The **pigeon degree** of a polynomial is the largest pigeon degree of its monomials, and the pigeon degree of a refutation $\pi=(p_1,\dots,p_\tau)$ is the largest pigeon degree of its lines:
--   $$\mathrm{pdeg}(\pi)=\max_{k}\ \max_{m\in p_k}\mathrm{pdeg}(m).$$
--   A set of axioms "requires pigeon degree $D$" if every refutation has pigeon degree at least $D$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5 (pigeon degree), p.26 (PDF p.29)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_pdegMono

namespace PCNonBool

/-- The pigeon degree of a sequence of polynomials: the largest pigeon degree of a monomial of a
line (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5, p.26 (PDF p.29)). "π requires pigeon degree > b" is `b < pdegSeq G π`. -/
noncomputable def pdegSeq {F : Type*} [Field F] {U V : Type*} [DecidableEq U]
    (G : BipGraph U V) (π : List (MvPolynomial (Var G) F)) : ℕ :=
  (π.map fun p => p.support.sup (pdegMono G)).foldr max 0

end PCNonBool


