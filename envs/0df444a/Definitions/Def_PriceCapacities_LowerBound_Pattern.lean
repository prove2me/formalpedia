-- Prove2me | Definitions.Def_PriceCapacities_LowerBound_Pattern
-- name    : PriceCapacities_LowerBound_Pattern
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:22:14.204193+00:00
-- url     : https://prove2.me/theorems/707bf011-b704-46ba-8225-b8c189819249
-- title:
--   The pattern set $G\subset\{\pm1/\sqrt d\}^d$, $N=2^{d-1}$, and $\Phi(\theta)=\frac1N\sum_{x\in G}\omega_x|\langle\theta,x\rangle|$
-- statement:
--   Fix an integer $d\ge1$. Among the $2^d$ vectors of $\mathbb R^d$ whose coordinates are all $\pm1/\sqrt d$, take one vector from each opposite pair $\{x,-x\}$; the resulting set is $G$, with $|G|=N=2^{d-1}$. For weights $\omega=(\omega_x)_{x\in G}$ define
--   $$\Phi(\theta)=\frac1N\sum_{x\in G}\omega_x\,|\langle\theta,x\rangle|\qquad(\theta\in\mathbb R^d).$$
--   $G$ is the small point pattern of the hard instance (§10.1) and $\Phi$ is the target function of Lemma 10.6.
--
--   **Formalization Note.** The representative of each opposite pair is fixed canonically: the one with positive first coordinate. `PatternIdx d` is the set of sign vectors $s\in\{-1,1\}^d$ with $s_1=+1$ and `patternVec s = s/√d`; `patternCount d = 2^(d-1)` is $N$. Every expression the mission builds from $G$ ($|\langle\theta,x\rangle|$, $\Phi$, sums over $G$) is unchanged when a representative $x$ is replaced by $-x$, so the choice is immaterial.
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 32, §10.1 (G, N); p. 36, Lemma 10.6 (Φ)

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_Fourier

open scoped BigOperators

namespace PriceCapacities.LowerBound

/-!
# The pattern set `G` and the target `Φ` (§10.1, Lemma 10.6)

Prabhu, Schwiegelshohn, Shyam, *The Price of Capacities for Clustering Coresets*, STOC 2027
submission (manuscript sha256 ec35f5ef…), p. 32, §10.1 (`G`, `N = 2^{d−1}`); p. 36, Lemma 10.6 (`Φ`).

* `G` takes one vector from each opposite pair among the vectors of `ℝ^d` with all coordinates
  `±1/√d`. The canonical choice made here is the representative whose first coordinate is
  positive: `PatternIdx d` is the set of sign vectors `s ∈ {−1, 1}^d` with `s_0 = 1`, and
  `patternVec s = s/√d ∈ G`. (For `d ≥ 1` this is exactly one vector per opposite pair, and
  `|G| = N = 2^{d−1}`.)
* `patternCount d = N = 2^{d−1}`.
* `Phi ω θ = Φ(θ) = (1/N) Σ_{x ∈ G} ω_x |⟨θ, x⟩|` for weights `ω : G → ℝ`.
-/

/-- Index set of `G`: sign vectors with first coordinate `+1` (one per opposite pair). -/
abbrev PatternIdx (d : ℕ) : Type := {s : Cube d // ∀ j : Fin d, (j : ℕ) = 0 → s j = 1}

/-- The vector `s/√d ∈ ℝ^d` with coordinates `±1/√d`. -/
noncomputable def patternVec {d : ℕ} (s : Cube d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => sgn (s j) / Real.sqrt d)

/-- `N = |G| = 2^{d−1}`. -/
def patternCount (d : ℕ) : ℕ := 2 ^ (d - 1)

/-- `Φ(θ) = (1/N) Σ_{x ∈ G} ω_x |⟨θ, x⟩|`. -/
noncomputable def Phi {d : ℕ} (ω : PatternIdx d → ℝ) (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / (patternCount d : ℝ)) * ∑ x : PatternIdx d, ω x * |inner ℝ θ (patternVec x.1)|

end PriceCapacities.LowerBound


