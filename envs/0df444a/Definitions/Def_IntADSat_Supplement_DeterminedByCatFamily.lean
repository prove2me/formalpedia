-- Prove2me | Definitions.Def_IntADSat_Supplement_DeterminedByCatFamily
-- name    : IntADSat_Supplement_DeterminedByCatFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:53:58.357864+00:00
-- url     : https://prove2.me/theorems/acb2eb87-12a5-4ed8-a3a4-e212b2f079e0
-- title:
--   Determined by the caterpillar counts $(\hom(T,G))_{T\in\mathcal F_n}$
-- statement:
--   A graph $G$ is **determined among all finite simple graphs by $(\hom(T,G))_{T\in\mathcal F_n}$** if every finite simple graph $H$ satisfies
--   $$\big[\hom(T,G)=\hom(T,H)\ \text{for all }T\in\mathcal F_n\big]\ \Longrightarrow\ G\cong H .$$
--   The family $\mathcal F_n$ depends only on $n$, not on $G$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem 1.2, p.2 (PDF 3); Corollary C.2, p.21 (PDF 22)

import Mathlib
import Definitions.Def_IntADSat_Supplement_InCatFamily
import Definitions.Def_GenTuranHard_FinGraph

set_option autoImplicit false

namespace IntADSat.Supplement

/-- `G` is **determined among all finite simple graphs by `(hom(T, G))_{T ∈ F_n}`**
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorem 1.2, p.2 (PDF 3); Corollary C.2, p.21 (PDF 22)): every finite simple graph `H` with
`hom(T, G) = hom(T, H)` for all `T ∈ F_n` is isomorphic to `G`.

**Formalization Note** `hom(T, G)` is the published `GenTuranHard.homCount` (`Nat.card (T →g G)`, all
homomorphisms, not necessarily injective). `H` ranges over `SimpleGraph (Fin m)` for every `m`; `T` ranges over every
`T : SimpleGraph (Fin k)` in `F_n` (all labellings, which changes nothing since hom counts are
isomorphism invariant). The family depends only on `n`, not on `G`. -/
def DeterminedByCatFamily (n : ℕ) {N : ℕ} (G : SimpleGraph (Fin N)) : Prop :=
  ∀ (m : ℕ) (H : SimpleGraph (Fin m)),
    (∀ (k : ℕ) (T : SimpleGraph (Fin k)), InCatFamily n T → GenTuranHard.homCount T G = GenTuranHard.homCount T H) →
      Nonempty (G ≃g H)

end IntADSat.Supplement


