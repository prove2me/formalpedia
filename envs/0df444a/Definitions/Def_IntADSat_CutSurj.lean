-- Prove2me | Definitions.Def_IntADSat_CutSurj
-- name    : IntADSat_CutSurj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:55.999644+00:00
-- url     : https://prove2.me/theorems/a8b8a143-9e20-482a-9e87-c95253757ca2
-- title:
--   Integer-surjective adjacency cut $A[C,S]\mathbb Z^S=\mathbb Z^C$
-- statement:
--   For a simple graph $G$ on $[n]$ with adjacency matrix $A$ and sets $C,S\subseteq[n]$, the block $A[C,S]$ (rows $C$, columns $S$) is **integer surjective** if
--
--   $$
--   A[C,S]\,\mathbb Z^S=\mathbb Z^C,
--   $$
--
--   i.e. every integer vector indexed by $C$ is an integer combination of the columns of $A$ indexed by $S$, restricted to the rows $C$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemmas B.8 and B.9, p.18 (PDF 19)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat

/-- Integer surjectivity of an adjacency block, `A[C, S]ℤ^S = ℤ^C`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemmas B.8 and B.9, p.18 (PDF 19)): every integer vector on the rows `C` is an integer
combination of the columns of `A_G` indexed by `S`, restricted to the rows `C`. -/
def CutSurj {n : ℕ} (G : SimpleGraph (Fin n)) (C S : Finset (Fin n)) : Prop :=
  ∀ y : Fin n → ℤ, ∃ x : Fin n → ℤ, ∀ c ∈ C, ∑ v ∈ S, adjacency G c v * x v = y c

end IntADSat


