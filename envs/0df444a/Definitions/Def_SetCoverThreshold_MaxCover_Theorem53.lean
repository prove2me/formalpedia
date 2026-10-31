-- Prove2me | Definitions.Def_SetCoverThreshold_MaxCover_Theorem53
-- name    : SetCoverThreshold_MaxCover_Theorem53
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T19:42:12.346093+00:00
-- url     : https://prove2.me/theorems/ddaa7dd3-f17f-4ed9-9d97-c6f21c5efafb
-- title:
--   Feige 1998 Max k-Cover Reduction Instance (Theorem 5.3)
-- statement:
--   This definition establishes the Max $k$-Cover reduction instance $\text{maxCoverInst}(\phi, C)$ from Feige's 1998 hardness of approximation paper for Set Cover (Theorem 5.3, Section 5, p. 649).
--
--   Given a 3CNF-5 formula $\phi$ with $M$ clauses and a $k$-prover code $C : [k] \to \{0,1\}^\ell$, the construction produces an instance $\mathcal{I} = (N, \mathcal{S}, k')$ of the Max $k$-Cover problem:
--
--   1. **Ground set size:** Elements of the universe are pairs $(R, \mathbf{x})$, where $R$ is a sequence of $\ell$ random questions and $\mathbf{x} \in [k]^{\{0,1\}^\ell}$ is an answer tuple in the partition system. The total number of points is:
--   $$
--   N = (3M)^\ell \cdot k^{2^\ell}.
--   $$
--
--   2. **Subset family:** The collection of subsets $\mathcal{S}$ is indexed by set indices $s \in \text{SetIdx}(\phi, C)$. Each set consists of all points $(R, \mathbf{x})$ matching the prover answers on the corresponding subcube.
--
--   3. **Cover budget:** The maximum number of sets allowed in a cover is:
--   $$
--   k' = \text{coverBudget}(\phi, C) = 2 \cdot 5^\ell \cdot k.
--   $$
--
--   This reduction instance provides the core bridge connecting the hardness of multi-prover interactive proof systems with the inapproximability of Max $k$-Cover within $(1 - 1/e + \varepsilon)$.
-- source:
--   Uriel Feige, A Threshold of ln n for Approximating Set Cover, Journal of the ACM 45(4):634-652 (1998), p. 649, proof of Theorem 5.3

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Instance
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction

set_option autoImplicit false

namespace SetCoverThreshold.MaxCover

open Classical

/-- **The §5 Max k-Cover reduction instance** (Feige 1998, p. 649, proof of Theorem 5.3):
for a 3CNF-5 formula `φ` and a `k`-prover code `code : Fin k → Fin ℓ → Bool`, the ground set has
`N = (3M)^ℓ · k^{2^ℓ}` points (indexed via `Fintype.equivFin`), the family of subsets lists
`reductionSet φ code (cubeSystem k (Fin ℓ → Bool)) s` for all `s : SetIdx φ code`, and the budget is
`k' = coverBudget φ code`. -/
noncomputable abbrev maxCoverInst (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) : Instance where
  n := Fintype.card (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k))
  sets := List.ofFn (fun i : Fin (Fintype.card (SetIdx φ code)) =>
    (reductionSet φ code (cubeSystem k (Fin ℓ → Bool)) ((Fintype.equivFin (SetIdx φ code)).symm i)).map
      (Fintype.equivFin (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k))).toEmbedding)
  k := coverBudget φ code

end SetCoverThreshold.MaxCover


