-- Prove2me | Definitions.Def_PCNonBool_pdegMono
-- name    : PCNonBool_pdegMono
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:00.379362+00:00
-- url     : https://prove2.me/theorems/b8b61aea-d605-418a-8d9f-3583ffa45340
-- title:
--   Pigeon degree of a monomial
-- statement:
--   For a monomial $m$ in the variables $x_{i,j}$, the **pigeon degree** $\mathrm{pdeg}(m)$ is the number of pigeons mentioned by $m$:
--   $$\mathrm{pdeg}(m)=|\{\,i\in U : x_{i,j}\text{ occurs in } m \text{ for some } j\,\}|.$$
--   For the pigeonhole formulas, the support degree of the paper's general framework simplifies to this measure.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5 (pigeon degree), p.26 (PDF p.29)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var

namespace PCNonBool

/-- The pigeon degree `pdeg(m)` of a monomial `m`: the number of pigeons mentioned by `m`, i.e.
of pigeons `i` such that some variable `x_{i,j}` occurs in `m`
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5, p.26 (PDF p.29)). -/
def pdegMono {U V : Type*} [DecidableEq U] (G : BipGraph U V) (m : Var G →₀ ℕ) : ℕ :=
  (m.support.image (fun e => e.1.1)).card

end PCNonBool


