-- Prove2me | Definitions.Def_OptGaussTomo_purifiedDist
-- name    : OptGaussTomo_purifiedDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:06:39.203283+00:00
-- url     : https://prove2.me/theorems/b145a101-ab9f-414c-86e1-820f27d108b8
-- title:
--   Purified distance $P(\rho,\sigma)=\sqrt{1-F(\rho,\sigma)^2}$
-- statement:
--   The purified distance between operators $\rho,\sigma$ is
--
--   $$
--   P(\rho,\sigma)=\sqrt{1-F(\rho,\sigma)^2},
--   $$
--
--   with $F$ the root fidelity. The paper's accuracy guarantee $P(\rho,\hat\rho)\le\varepsilon$ is the same as $F(\rho,\hat\rho)^2\ge1-\varepsilon^2$.
--
--   **Formalization Note** On densities $0\le F\le1$, so the square root is taken of a number in $[0,1]$.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), §1 p.3 (pdf p.3), definition P(ρ, ρ̂) := √(1 − F(ρ, ρ̂)²)

import Mathlib
import Definitions.Def_OptGaussTomo_rootFidelity

namespace OptGaussTomo

/-!
# Purified distance `P(ρ, σ) = √(1 − F(ρ, σ)²)`

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), §1, p.3:
"`P(ρ, ρ̂) := √(1 − F(ρ, ρ̂)²) ≤ ε`, in other words, we require `F(ρ, ρ̂)² ≥ 1 − ε²`".

**Formalization Note.** `F` is the root fidelity `rootFidelity` (Uhlmann form). On densities
`0 ≤ F ≤ 1`, so `Real.sqrt` is applied to a number in `[0, 1]` and `P ≤ ε` is equivalent to
`F² ≥ 1 − ε²` for `0 ≤ ε`.
-/

/-- `P(ρ, σ) = √(1 − F(ρ, σ)²)`. -/
noncomputable def purifiedDist {I : Type} (ρ σ : Matrix I I ℂ) : ℝ :=
  Real.sqrt (1 - rootFidelity ρ σ ^ 2)

end OptGaussTomo


