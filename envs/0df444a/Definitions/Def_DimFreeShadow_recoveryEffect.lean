-- Prove2me | Definitions.Def_DimFreeShadow_recoveryEffect
-- name    : DimFreeShadow_recoveryEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:17.170609+00:00
-- url     : https://prove2.me/theorems/b5a74d7e-1c83-45d2-92cc-cc87755c2b7a
-- title:
--   Eq. (5) — the recovery-PGM effects $D_{y,t}$ and the ensemble state $B_t$
-- statement:
--   Let $\{(p_x,\rho_x):x\in\mathcal X\}$ be a finite ensemble of states on $\mathcal H$. For $t\ge 0$ put $B_t=\sum_x p_x\rho_x^{\otimes t}$, let $P_t$ be the projection onto $\operatorname{supp}B_t$, and let $\beta_0(u)=\pi/(2(\cosh(\pi u)+1))$, an even probability density on $\mathbb R$. The **recovery-PGM effects** are
--
--   $$
--   D_{y,t}=p_y\int_{\mathbb R}\beta_0(u)\,B_t^{-(1+iu)/2}\rho_y^{\otimes t}B_t^{-(1-iu)/2}\,du+p_y(I-P_t),
--   $$
--
--   with complex powers computed on $\operatorname{supp}B_t$ and extended by zero. Algorithm 2 draws $t$ uniformly from $\{0,\dots,N-1\}$ and measures the first $t$ copies with $\{D_{y,t}\}_y$.
--
--   **Formalization Note** Complex powers and $P_t$ are the published `supportPow` and `supportProj`. $\beta_0$ is the published `betaZero`. The integral is entrywise; each entry is continuous in $u$ and bounded by a constant times $\beta_0(u)$, hence integrable. At $t=0$ the space is one-dimensional and $D_{y,0}=p_y$.
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), §2.3, Eq. (5), p.8

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_WildeQIT_Recover_spectralFun

namespace DimFreeShadow

open ShadowTomography.UpperBound (tensorPow)
open QAlgorithms.Papers.Independent.Dependency50.P21 (betaZero)

/-- **The `t`-copy ensemble state** `B_t := Σ_x p_x ρ_x^{⊗t}` (arXiv:2608.06345, sha256
a1a42249…, §2.3, p.8), for a finite ensemble `{(p_x, ρ_x) : x ∈ X}` (§2.1, p.5).

**Formalization Note** `H^{⊗t}` is indexed by `Fin t → d`; at `t = 0` it is the one-point space
and `B_0 = Σ_x p_x` (a `1 × 1` matrix). The ensemble conditions (`p_x > 0`, `Σ_x p_x = 1`,
each `ρ_x` a state) are hypotheses of the statements. -/
noncomputable def ensembleState {X d : Type} [Fintype X] (p : X → ℝ)
    (ρ : X → Matrix d d ℂ) (t : ℕ) : Matrix (Fin t → d) (Fin t → d) ℂ :=
  ∑ x, (p x : ℂ) • tensorPow (ρ x) t

/-- **The recovery-PGM effects** (arXiv:2608.06345, sha256 a1a42249…, §2.3, Eq. (5), p.8):
"Fix an integer budget N ≥ 1, and for 0 ≤ t < N set Bt := Σx pxρ⊗t x, Pt := Πsupp Bt,
β0(u) := π/(2(cosh(πu) + 1)). Define
`Dy,t := py ∫R β0(u) Bt^{−(1+iu)/2} ρy^{⊗t} Bt^{−(1−iu)/2} du + py(I − Pt)`. (5)
Complex powers here are computed on supp Bt and extended by zero."

**Formalization Note** `β₀` is the published `P21.betaZero`. Complex powers and `P_t` are
`WildeQIT.Recover.supportPow`/`WildeQIT.Recover.supportProj` (spectral, `0 ↦ 0`). The matrix-valued integral is taken entrywise (Bochner
integral of each entry over `ℝ` with Lebesgue measure); each entry is continuous in `u` and
bounded by a constant times `β₀(u)`, so it is integrable and Lean's default value for a
non-integrable integrand is never used. At `t = 0`, `H^{⊗0}` is one-dimensional and
`D_{y,0} = p_y` (Algorithm 2, line 3). -/
noncomputable def recoveryEffect {X d : Type} [Fintype X] [Fintype d] [DecidableEq d]
    (p : X → ℝ) (ρ : X → Matrix d d ℂ) (t : ℕ) (y : X) :
    Matrix (Fin t → d) (Fin t → d) ℂ :=
  (p y : ℂ) • Matrix.of (fun i j => ∫ u : ℝ, (betaZero u : ℂ) *
      (WildeQIT.Recover.supportPow (ensembleState p ρ t) (-(1 + (u : ℂ) * Complex.I) / 2) * tensorPow (ρ y) t *
        WildeQIT.Recover.supportPow (ensembleState p ρ t) (-(1 - (u : ℂ) * Complex.I) / 2)) i j) +
    (p y : ℂ) • (1 - WildeQIT.Recover.supportProj (ensembleState p ρ t))

end DimFreeShadow


