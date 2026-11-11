-- Prove2me | Definitions.Def_PermInvCC_DensDist
-- name    : PermInvCC_DensDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:59.571344+00:00
-- url     : https://prove2.me/theorems/4f28f316-d82d-45b4-895f-82a1d9034983
-- title:
--   Distributions on $\{\bot\}\cup([0,\infty)\times E)$ with densities
-- statement:
--   The outcome space $\{\bot\}\cup([0,\infty)\times E)$ consists of a point $\bot$ and one half-line for each label $e$. A distribution $P$ on it is given by a mass $p_\bot\ge 0$ at $\bot$ and densities $p_e(z)\ge 0$ on the half-lines; it is a **probability distribution** when
--   $$p_\bot+\sum_e\int_0^\infty p_e(z)\,dz=1 .$$
--
--   These are the distributions on which the Hellinger distance of Definition 2.5 is defined.
--
--   **Formalization Note** The densities are required to be integrable on $(0,\infty)$, so all integrals are genuine; $(0,\infty)$ and $[0,\infty)$ differ by a null set. The label set is any finite type (in use: the cells of an event $E$).
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Definition 2.5, p.10

import Mathlib

namespace PermInvCC

/-- A **distribution on the outcome space `{⊥} ∪ ([0, ∞) × E)`** given by a mass at `⊥` and
densities on the continuous components (Y. Huang and Z. Ye, arXiv:2609.40116, held version
sha256 fe1797dd…, Definition 2.5, p.10): `pbot = p_⊥` and `dens e = p_e`, for `e` in a finite
label set `ι` (the cells of an event `E`).

**Formalization Note.** The densities are nonnegative and integrable on `(0, ∞)`, so every
integral below is a genuine Lebesgue integral and never takes Lean's junk value; `(0, ∞)` and
`[0, ∞)` differ by a null set. `IsProb` says the total mass is one. -/
structure DensDist (ι : Type) [Fintype ι] where
  /-- the mass `p_⊥` at the point `⊥` -/
  pbot : ℝ
  /-- the density `p_e(z)` on the component `[0, ∞) × {e}` -/
  dens : ι → ℝ → ℝ
  pbot_nonneg : 0 ≤ pbot
  dens_nonneg : ∀ e z, 0 ≤ dens e z
  dens_integrable : ∀ e, MeasureTheory.IntegrableOn (dens e) (Set.Ioi 0)

/-- The distribution is a **probability distribution**: `p_⊥ + ∑_e ∫_0^∞ p_e(z) dz = 1`. -/
def DensDist.IsProb {ι : Type} [Fintype ι] (P : DensDist ι) : Prop :=
  P.pbot + ∑ e, ∫ z in Set.Ioi (0 : ℝ), P.dens e z = 1

end PermInvCC


