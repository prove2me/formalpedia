-- Prove2me | Definitions.Def_GaussDiffSVP_halfGrid
-- name    : GaussDiffSVP_halfGrid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:15.062435+00:00
-- url     : https://prove2.me/theorems/8dae52fd-739a-4f59-9a18-517f74ddfee5
-- title:
--   Half-grid shift $d = \tfrac12 B\bar e$, $e\in(\mathbb Z/2)^n$
-- statement:
--   For $\Gamma = B\mathbb Z^n$ and $e\in(\mathbb Z/2)^n$ with representative $\bar e\in\{0,1\}^n$, $d = \tfrac12 B\bar e$. These $2^n$ points represent the classes of the half grid $(\Gamma/2)/\Gamma$, so a uniform $e$ is the paper's "$d\sim\mathrm{Unif}((\Gamma/2)/\Gamma)$".
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §4.2, p.23; Algorithm 1, line 8, p.29

import Mathlib
import Definitions.Def_SuperlatSVP_lat

namespace GaussDiffSVP

/-- The representative `d = ½ B ē` of a class of the half grid `(Γ/2)/Γ` of `Γ = Bℤⁿ`
(Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §4.2, p.23; Algorithm 1, line 8, p.29: "Draw `d ∼ Unif((Γ/2)/Γ)`"), indexed by
`e ∈ (ℤ/2)ⁿ` with integer representative `ē = (val e_i)_i ∈ {0,1}ⁿ`.

**Formalization Note.** For a basis `B` (`B.det ≠ 0`), `e ↦ ½Bē` is a bijection from `(ℤ/2)ⁿ` onto
a set of representatives of the `2ⁿ` classes of `(Γ/2)/Γ`, so the uniform law on `(ℤ/2)ⁿ` is the
uniform law on the half grid. -/
noncomputable def halfGrid {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ZMod 2) :
    SuperlatSVP.E n :=
  (1 / 2 : ℝ) • SuperlatSVP.vecE (B.mulVec fun i => ((e i).val : ℝ))

end GaussDiffSVP


