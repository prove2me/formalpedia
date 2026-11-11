-- Prove2me | Definitions.Def_GaussDiffSVP_buildIdealLaw
-- name    : GaussDiffSVP_buildIdealLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:03:15.824198+00:00
-- url     : https://prove2.me/theorems/64183d95-976e-48eb-a751-cfd542bfc65a
-- title:
--   Ideal cooling tree $\mathrm{BuildIdeal}(p,0)$ (Algorithm 1)
-- statement:
--   The law of the root list of Algorithm 1 for $\Gamma = B\mathbb Z^n$, terminal width $r_0 = \sqrt2\,s$, cooling parameter $u$ (widths $r_j = r_0\gamma^{-j}$, $\gamma = \sqrt{2(1-u)}$), shell width $w$, depth $t$ and $M = M_{\mathrm{leaf}}$:
--
--   1. a leaf (level $t$) at offset $p$ runs $2M$ independent corrected trials at $(p, r_t, S_{r_t}(a_0))$ and keeps the non-failure records;
--   2. a node at level $j<t$ and offset $p$ draws $d$ uniformly from the half grid, builds its children at $p/2+d$ and $-p/2+d$ independently, activates pairs with the coin kernel of level $j+1$, and keeps one difference $x-y$ per edge isolated at both endpoints.
--
--   **Formalization Note** Algorithm 1 uses "pairwise independent coins" without fixing the family, so the law is indexed by an arbitrary coin kernel family; statements assume it has the marginals (45).
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Algorithm 1, p.29; §5.3, p.29

import Mathlib
import Definitions.Def_GaussDiffSVP_isoTreeLaw
import Definitions.Def_GaussDiffSVP_halfGrid
import Definitions.Def_GaussDiffSVP_shell
import Definitions.Def_GaussDiffSVP_leafTrial
import Definitions.Def_GaussDiffSVP_leafLaw

namespace GaussDiffSVP

/-- The ideal cooling tree `BuildIdeal(p, 0)` of Algorithm 1 (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.29) as a law on record
lists, for the lattice `Γ = Bℤⁿ`, terminal width `r₀ = √2 s`, cooling parameter `u`
(`γ = √(2(1 − u))`, `r_j = r₀ γ^{−j}`, `a₀ = 1/(1 + u)`), shell width `w`, depth `t` and
`M = M_leaf`:

* a leaf (level `t`) at offset `p` runs `2M` independent corrected trials at
  `(p, r_t, S_{r_t}(a₀))` (`leafTrial`) and keeps the non-failure records (`leafLaw`);
* a node at level `j < t` and offset `p` draws `d = ½Bē` with `e` uniform on `(ℤ/2)ⁿ`
  (`halfGrid`), builds its children at offsets `p/2 + d` and `−p/2 + d` with independent
  randomness, activates each record pair `(x, y)` with the coin kernel `κ (j + 1) p e` of the
  children's level, and keeps one difference record `x − y` per edge isolated at both endpoints.

**Formalization Note.** Algorithm 1 activates eligible pairs with probability `c_{j+1} ω_r(z)`
"using pairwise independent coins" without fixing the coin family; the law is therefore indexed by
an arbitrary coin kernel family `κ`, and statements about Algorithm 1 assume
`IsCoinKernel (q_j) (κ j p e)` with the probabilities (45) of `coolKernel`. -/
noncomputable def buildIdealLaw {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (w u s : ℝ) (t M : ℕ)
    (κ : ℕ → SuperlatSVP.E n → (Fin n → ZMod 2) → (lL : List (SuperlatSVP.E n)) →
      (lR : List (SuperlatSVP.E n)) → PMF (Fin lL.length × Fin lR.length → Bool))
    (p : SuperlatSVP.E n) : PMF (List (SuperlatSVP.E n)) :=
  isoTreeLaw t (fun x y => x - y) (fun _ _ => PMF.uniformOfFintype (Fin n → ZMod 2))
    (fun q e => (1 / 2 : ℝ) • q + halfGrid B e) (fun q e => -((1 / 2 : ℝ) • q) + halfGrid B e) κ
    (fun q => leafLaw (leafTrial B (Real.sqrt 2 * s / Real.sqrt (2 * (1 - u)) ^ t)
      (shell (Real.sqrt 2 * s / Real.sqrt (2 * (1 - u)) ^ t) w (1 / (1 + u))) q) (2 * M)) t p

end GaussDiffSVP


