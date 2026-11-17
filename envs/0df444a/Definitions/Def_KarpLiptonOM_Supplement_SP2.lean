-- Prove2me | Definitions.Def_KarpLiptonOM_Supplement_SP2
-- name    : KarpLiptonOM_Supplement_SP2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:40:43.234427+00:00
-- url     : https://prove2.me/theorems/6e0793fa-316c-45af-a7e1-315b5eeffe61
-- title:
--   $\mathrm S^{\mathrm P}_2$: symmetric alternation (Definition A.2.2)
-- statement:
--   $\mathrm S^{\mathrm P}_2$ is the class of languages $L$ such that the promise problem $(L,\overline L)$ is in $\mathrm{prS}^{\mathrm P}_2$: there are polynomials $a,b$ and a polynomial-time $V$ with
--
--   $$
--   x\in L\Rightarrow\exists y\,\forall z\;V(x,y,z)=1,\qquad x\notin L\Rightarrow\exists z\,\forall y\;V(x,y,z)=0,
--   $$
--
--   with $y\in\{0,1\}^{a(|x|)}$ and $z\in\{0,1\}^{b(|x|)}$. It satisfies $\mathrm{NP}\cup\mathrm{coNP}\subseteq\mathrm{MA}\subseteq\mathrm S^{\mathrm P}_2\subseteq\mathrm{ZPP}^{\mathrm{NP}}$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.2, p.21

import Mathlib
import Definitions.Def_KarpLiptonOM_toPromise
import Definitions.Def_KarpLiptonOM_Supplement_prSP2

namespace KarpLiptonOM.Supplement

/-- `S₂^P`, the class of languages of `prS₂^P` (Definition A.2.2, Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.21: "`S₂^P` and `O₂^P` are
the corresponding classes of languages"), a language `L` being identified with `(L, L̄)`. -/
def SP2 : Set (Set (List Bool)) := {L | toPromise L ∈ prSP2}

end KarpLiptonOM.Supplement


