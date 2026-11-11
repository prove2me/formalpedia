-- Prove2me | Definitions.Def_QVolTransducer_gridIdx
-- name    : QVolTransducer_gridIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:10.050352+00:00
-- url     : https://prove2.me/theorems/acd77f04-148f-4624-91b4-1488f3a1f08a
-- title:
--   Grids $(RB_d)_\zeta=\zeta\mathbb Z^d\cap RB_d$, grid membership oracles $O_{K,\zeta}$ and grid states $|p\rangle$
-- statement:
--   For a spacing $\zeta>0$ and a radius $R$, the **grid** of the ball $RB_d$ is
--
--   $$
--   (RB_d)_\zeta=\zeta\mathbb Z^d\cap RB_d ,
--   $$
--
--   whose points $\zeta z$ are indexed by their integer coordinates $z\in\mathbb Z^d$. For a set $K\subseteq\mathbb R^d$, the **grid membership oracle** is the phase oracle
--
--   $$
--   O_{K,\zeta}:|x\rangle\mapsto(-1)^{[x\in K]}|x\rangle,\qquad x\in(RB_d)_\zeta ,
--   $$
--
--   and for two spacings $\zeta,\zeta'$ the pair of oracles is $O_{K,\zeta}\oplus O_{K,\zeta'}$. For a function $p\ge0$ on grid points, its **quantum state** is
--
--   $$
--   |p\rangle=\sum_{x\in(RB_d)_\zeta}\sqrt{p_x}\,|x\rangle\in\mathbb C^{(RB_d)_\zeta},
--   $$
--
--   where a distribution defined on a subset of the grid (such as $K_\zeta$) is extended by zero. This is the access model and the state space of every transducer in Part II of the paper.
--
--   **Formalization Note** Candidate lattice vectors are taken in the box $|z_i|\le\lceil R/\zeta\rceil$; for $\zeta>0$ every $z$ with $\|\zeta z\|\le R$ lies in that box, so the finite set is exactly the paper's grid. Distributions are functions on $\mathbb Z^d$ read on the grid.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Definition 7.4, p.43; §9 preamble, p.53 (PDF pp.45, 55)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

namespace QVolTransducer

/-- The grid point `ζ z ∈ ζℤ^d ⊆ ℝ^d` with integer coordinates `z ∈ ℤ^d` (Cornelissen, Apers,
Gribling, *Improved quantum volume estimation with transducers and amortized quantum walks*,
arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Definition 7.4, p.43:
"Ω_ζ = ζℤ^d ∩ Ω"). -/
noncomputable def latticePt {d : ℕ} (ζ : ℝ) (z : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => ζ * (z i : ℝ))

open Classical in
/-- The grid `(R B_d)_ζ = ζℤ^d ∩ R B_d` (arXiv:2609.40217, Definition 7.4, p.43, and the §9
preamble, p.53), as the finite set of integer coordinate vectors `z` with `‖ζ z‖ ≤ R`.

**Formalization Note** The candidates are taken in the box `|z_i| ≤ ⌈R/ζ⌉`; for `ζ > 0` (the only
case the paper uses) every `z` with `‖ζ z‖ ≤ R` lies in that box, so this is exactly the paper's
grid. A grid point `x = ζ z` is indexed by `z`. -/
noncomputable def gridIdx (d : ℕ) (ζ R : ℝ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-⌈R / ζ⌉) ⌈R / ζ⌉).filter
    (fun z => ‖latticePt ζ z‖ ≤ R)

/-- The index type of the grid `(R B_d)_ζ`; `ℂ^(Grid d ζ R)` is the paper's `ℂ^{(RB_d)_ζ}`
(arXiv:2609.40217, p.53). -/
abbrev Grid (d : ℕ) (ζ R : ℝ) : Type := {z : Fin d → ℤ // z ∈ gridIdx d ζ R}

open Classical in
/-- The membership oracle on the grid (arXiv:2609.40217, §9 preamble, p.53: "O_{K,ζ}, that for all
x ∈ (RB_d)_ζ acts as O_{K,ζ} : |x⟩ ↦ (−1)^{x∈K} |x⟩"), the phase oracle of the membership bits
of the grid points. -/
noncomputable def gridOracle {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ζ R : ℝ) :
    Matrix (Grid d ζ R) (Grid d ζ R) ℂ :=
  QAlgorithms.phaseOracle fun z => decide (latticePt ζ z.1 ∈ K)

/-- The pair of membership oracles `O_{K,ζ}` and `O_{K,ζ'}` on two grids, as one oracle
`O_{K,ζ} ⊕ O_{K,ζ'}` on `ℂ^{(RB_d)_ζ} ⊕ ℂ^{(RB_d)_{ζ'}}` (arXiv:2609.40217, Theorem 9.16, p.61:
"accessible through membership oracles O_{K,ζ} and O_{K,ζ/γ}", used with `ζ' = ζ/γ`). -/
noncomputable def twoGridOracle {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ζ ζ' R : ℝ) :
    Matrix (Grid d ζ R ⊕ Grid d ζ' R) (Grid d ζ R ⊕ Grid d ζ' R) ℂ :=
  Matrix.fromBlocks (gridOracle K ζ R) 0 0 (gridOracle K ζ' R)

/-- The quantum state `|p⟩ = Σ_{x ∈ (RB_d)_ζ} √(p_x) |x⟩ ∈ ℂ^{(RB_d)_ζ}` of a function `p` on
grid points (arXiv:2609.40217, §9 preamble, p.53). A distribution on a subset of the grid is
extended by zero ("Whenever we have a distribution that is defined on a subset of (RB_d)_ζ, we
generically extend it with 0's on its complement"); here `p` is given on all of `ℤ^d` and read on
the grid. -/
noncomputable def gridState {d : ℕ} {ζ R : ℝ} (p : (Fin d → ℤ) → ℝ) :
    EuclideanSpace ℂ (Grid d ζ R) :=
  WithLp.toLp 2 (fun z => ((Real.sqrt (p z.1) : ℝ) : ℂ))

end QVolTransducer


