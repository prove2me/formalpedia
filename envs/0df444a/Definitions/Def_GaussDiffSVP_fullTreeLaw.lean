-- Prove2me | Definitions.Def_GaussDiffSVP_fullTreeLaw
-- name    : GaussDiffSVP_fullTreeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:00:55.87459+00:00
-- url     : https://prove2.me/theorems/ba03cf03-c26d-43a3-9321-4c3506e32966
-- title:
--   Ideal full difference tree $\mathrm{BuildFullTree}(p,j)$ (Algorithm 3)
-- statement:
--   The law of the list of Algorithm 3 at height $j$ and offset $p$, for $\Gamma = B\mathbb Z^n$, fixed width $r$, shell width $w$ and energies $(a_i)$: height $0$ is a leaf law; at height $j+1$ draw $d$ uniformly from the half grid, build the children at $p/2+d$ and $-p/2+d$ independently, and append a record $x-y$ for every record pair with $x-y\in S_r(a_{j+1})$.
--
--   **Formalization Note** The leaf law is an argument (Algorithm 3's leaves are cooling roots, `buildIdealLaw`), as Theorem 8.2 assumes only a moment bound on the leaves.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Algorithm 3, p.40

import Mathlib
import Definitions.Def_GaussDiffSVP_fullMergeLaw
import Definitions.Def_GaussDiffSVP_halfGrid
import Definitions.Def_GaussDiffSVP_shell

namespace GaussDiffSVP

/-- The ideal full difference tree `BuildFullTree(p, j)` of Algorithm 3 (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.40), for the
lattice `Γ = Bℤⁿ`, fixed width `r`, shell width `w` and energies `(a_i)`, as a law on record
lists, by height `j`:

* height `0`: the leaf law `leaf p` at the prescribed offset;
* height `j + 1`: draw `d = ½Bē` with `e` uniform on `(ℤ/2)ⁿ`, build the children (height `j`)
  at offsets `p/2 + d` and `−p/2 + d` independently, and append one record `x − y` for every
  record pair `(x, y)` with `x − y ∈ S_r(a_{j+1})` (no coins).

**Formalization Note.** Algorithm 3 calls `BuildIdeal(p, 0)` at height `0` "with a fresh leaf pool
and private randomness". Theorem 8.2 assumes only a moment bound on the leaves, so the leaf law is
an argument here; Algorithm 3 is the instance `leaf = buildIdealLaw …`. The deterministic
retention test is a coin kernel concentrated on one activation pattern. -/
noncomputable def fullTreeLaw {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (r w : ℝ) (a : ℕ → ℝ)
    (leaf : SuperlatSVP.E n → PMF (List (SuperlatSVP.E n))) :
    ℕ → SuperlatSVP.E n → PMF (List (SuperlatSVP.E n))
  | 0 => leaf
  | j + 1 => fun p => (PMF.uniformOfFintype (Fin n → ZMod 2)).bind fun e => by
      classical
      exact fullMergeLaw (fullTreeLaw B r w a leaf j ((1 / 2 : ℝ) • p + halfGrid B e))
        (fullTreeLaw B r w a leaf j (-((1 / 2 : ℝ) • p) + halfGrid B e)) (fun x y => x - y)
        (fun lL lR => PMF.pure fun ij => decide (lL.get ij.1 - lR.get ij.2 ∈ shell r w (a (j + 1))))

end GaussDiffSVP


