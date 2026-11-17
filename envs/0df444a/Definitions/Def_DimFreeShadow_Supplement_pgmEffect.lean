-- Prove2me | Definitions.Def_DimFreeShadow_Supplement_pgmEffect
-- name    : DimFreeShadow_Supplement_pgmEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:59:15.235129+00:00
-- url     : https://prove2.me/theorems/87bd3361-0c78-4f98-90a7-6db25d97af7c
-- title:
--   Definition 2.1 — the completed pretty-good measurement $G_y=\bar\rho^{-1/2}q_y\sigma_y\bar\rho^{-1/2}+q_y(I-P)$
-- statement:
--   Let $\{(q_x,\sigma_x):x\in\mathcal X\}$ be a finite ensemble of states on a finite-dimensional Hilbert space $\mathcal K$, with weights $q_x$. Write
--
--   $$
--   \bar\rho:=\sum_{x}q_x\sigma_x
--   $$
--
--   for its average state and $P$ for the orthogonal projector onto $\operatorname{supp}\bar\rho$. The **completed pretty-good measurement** (PGM) of the ensemble has the effects
--
--   $$
--   G_y:=\bar\rho^{-1/2}\,q_y\sigma_y\,\bar\rho^{-1/2}+q_y(I-P),\qquad y\in\mathcal X,
--   $$
--
--   where the inverse square root is taken on $\operatorname{supp}\bar\rho$ and extended by zero on its kernel. The second term completes the effects to a resolution of the identity on the whole space; it has no effect on any state of the ensemble.
--
--   The paper uses this construction with $\sigma_x=\rho_x$ (one copy, Theorem 2.4) and with $\sigma_x=\rho_x^{\otimes n}$ and posterior weights in each round of the sequential PGM (Eq. (2)).
--
--   **Formalization Note** The ensemble is given by weights $q:\mathcal X\to\mathbb R$ and matrices $\sigma_x$ on any finite index type; the ensemble conditions are hypotheses of the theorems. $\bar\rho^{-1/2}$ and $P$ are the published spectral constructions `WildeQIT.Recover.supportPow ρ̄ (−1/2)` and `WildeQIT.Recover.supportProj ρ̄` (eigenvalue $0\mapsto0$). A zero weight $q_y=0$ gives $G_y=0$, which is the paper's convention for labels outside the support of the posterior (p.8).
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Definition 2.1, Eq. (1), pp.5–6; Eq. (2), p.6

import Mathlib
import Definitions.Def_WildeQIT_Recover_spectralFun

namespace DimFreeShadow

namespace Supplement

/-- **Average state of a finite ensemble** `ρ̄ := Σ_x q_x σ_x` (arXiv:2608.06345, sha256
a1a42249…, Definition 2.1, p.5–6; with `σ_x = ρ_x^{⊗T}`).

**Formalization Note** The ensemble conditions (`q_x > 0`, `Σ_x q_x = 1`, each `σ_x` a state)
are hypotheses of the statements that use it. -/
noncomputable def pgmAvg {X ι : Type} [Fintype X] (q : X → ℝ) (σ : X → Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  ∑ x, (q x : ℂ) • σ x

/-- **The completed pretty-good measurement** (arXiv:2608.06345, sha256 a1a42249…,
Definition 2.1, Eq. (1), p.5–6): "The operators
`G_x := ρ̄^{−1/2} q_x ρ_x^{⊗T} ρ̄^{−1/2} + q_x (I − P)`, `x ∈ X`, (1)
form the completed pretty-good measurement, where `ρ̄ := Σ_x q_x ρ_x^{⊗T}` is the average state
of the T-copy ensemble, P denotes the orthogonal projector onto supp ρ̄, and the inverse is taken
on supp ρ̄."

**Formalization Note** The ensemble states are passed as a family `σ : X → Matrix ι ι ℂ` on
any finite index type `ι`: `σ_x = ρ_x` on `ℂ^d` for `T = 1` (§2.4, Theorem 2.4) and
`σ_x = ρ_x^{⊗n}` on `Fin n → d` for the rounds of Algorithm 1 (Eq. (2), p.6). The inverse
square root on the support, extended by zero, is the published
`WildeQIT.Recover.supportPow ρ̄ (−1/2)`, and `P = Π_{supp ρ̄}` is
`WildeQIT.Recover.supportProj ρ̄`. A zero weight `q_y = 0` gives `G_y = 0`, which is the
paper's convention "set `G_{y|h} = 0` when `y ∉ X_h`" (p.8); zero-weight states contribute
nothing to `ρ̄`, so summing over all of `X` equals the paper's sum over `X_h`. -/
noncomputable def pgmEffect {X ι : Type} [Fintype X] [Fintype ι] [DecidableEq ι]
    (q : X → ℝ) (σ : X → Matrix ι ι ℂ) (y : X) : Matrix ι ι ℂ :=
  WildeQIT.Recover.supportPow (pgmAvg q σ) (-1 / 2) * ((q y : ℂ) • σ y) *
      WildeQIT.Recover.supportPow (pgmAvg q σ) (-1 / 2) +
    (q y : ℂ) • (1 - WildeQIT.Recover.supportProj (pgmAvg q σ))

end Supplement

end DimFreeShadow


