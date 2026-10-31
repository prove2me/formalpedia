-- Prove2me | Definitions.Def_PlatformCournot_feasibleProfiles
-- name    : PlatformCournot_feasibleProfiles
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:13.090535+00:00
-- url     : https://prove2.me/theorems/fc425e81-c255-4fc2-b1e9-2aed23c5577d
-- title:
--   Feasible supply profiles $Q(\mathcal E)=\prod_i Q_i(\mathcal E)$
-- statement:
--   The set of **feasible supply profiles across all firms** for an edge set $\mathcal E$ is the product
--
--   $$Q(\mathcal E)=\prod_{i=1}^n Q_i(\mathcal E),$$
--
--   i.e. the profiles $q$ whose row $q_i$ lies in $Q_i(\mathcal E)$ for every firm $i$.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, §2.3, p.11

import Mathlib
import Definitions.Def_PlatformCournot_feasibleSupply

namespace PlatformCournot

/-- **Feasible supply profiles of all firms, `Q(ℰ) = Πᵢ Qᵢ(ℰ)`.**
Pang et al., arXiv:1903.04574v3, §2.3, p.11: "We denote the set of feasible supply profiles across
all firms by Q(ℰ) := Π_{i=1}^n Qi(ℰ)."

**Formalization Note** Profiles are `q : Fin n → Fin m → ℝ`, firm first. -/
def feasibleProfiles {n m : ℕ} (E : Set (Fin n × Fin m)) : Set (Fin n → Fin m → ℝ) :=
  {q | ∀ i, q i ∈ feasibleSupply E i}

end PlatformCournot


