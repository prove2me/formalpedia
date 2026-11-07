-- Prove2me | Definitions.Def_EllipsoidFitting_primalIter
-- name    : EllipsoidFitting_primalIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:15.000922+00:00
-- url     : https://prove2.me/theorems/7975a842-ce37-40c3-9d95-81a69d4b9dae
-- title:
--   The primal iteration $(Q_i,H_i)$
-- statement:
--   Fix points with Gram matrix $M$, $\gamma=2m/d^2$ and a normalizer $c$ (the paper's is $C_F$). The correction is
--   $$
--   \operatorname{correct}(H)=\frac1{1-\gamma}\bigl(L^*M^{-1}L(-H)+\gamma H\bigr),
--   $$
--   and the iteration is
--   $$
--   Q_0=-c\,R,\quad H_0=G_c(Q_0),\qquad Q_{i+1}=Q_i+\operatorname{correct}(H_i),\quad H_{i+1}=G_c(Q_{i+1})-G_c(Q_i),
--   $$
--   with $G_c(X)=F(X)-cI-X$. With $c=C_F$, $H_i=\sum_{j\ge2}b_j\bigl(P_j(Q_i)-P_j(Q_{i-1})\bigr)$ is the paper's newly created higher-order deviation.
--
--   The candidate fitting matrix is $\frac1{C_F}F(Q_i)$; its constraint violation is controlled by Proposition 2.3.
--
--   **Formalization Note** $1/(1-\gamma)$ is Lean's junk $0$ at $\gamma=1$, and $M^{-1}$ is $0$ for singular $M$; the theorems assume $\gamma\ne1$ and $M$ invertible.
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), §2.1, pp.9–10 (PDF pp.11–12), Summary of the Initialization and Iterative Procedure

import Mathlib
import Definitions.Def_EllipsoidFitting_perturbR
import Definitions.Def_EllipsoidFitting_Fpos

set_option autoImplicit false

namespace EllipsoidFitting

open Matrix

/-- **The primal correction.** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase Transition for
Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), §2.1, p.10: "∆i = correct(Hi) :=
1/(1 − γ) (L∗M−1L(−Hi) + γ · Hi)".

`correctPrimal v X = (1/(1 − γ)) (L*M⁻¹L(−X) + γ X)` with `γ = 2m/d²`.

**Formalization Note** `1/(1 − γ)` is Lean's junk `0` at `γ = 1`; statements about the iteration
assume `γ ≠ 1`. -/
noncomputable def correctPrimal {m d : ℕ} (v : Fin m → Fin d → ℝ)
    (X : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / (1 - gammaRatio d m)) • (projS v (-X) + gammaRatio d m • X)

/-- **The primal iteration** (§2.1, pp.9–10, "Summary of the Initialization and Iterative
Procedure"): "Pick Q0 = −CF · R"; "Hi := ∑_{j≥2} bj · (Pj(Qi) − Pj(Qi−1)) for i ≥ 1, with H0 :=
∑_{j≥2} bj · Pj(Q0)"; "∆i = correct(Hi)"; "Qi+1 := Qi + ∆i".

`primalState v c i = (Q_i, H_i)` with normalizer `c` in place of `C_F`:
`Q_0 = −c R`, `H_0 = G_c(Q_0)`, `Q_{i+1} = Q_i + correct(H_i)`, `H_{i+1} = G_c(Q_{i+1}) − G_c(Q_i)`,
where `G_c(X) = F(X) − c I − X` (`Ghigh`).

**Formalization Note** `∑_{j≥2} b_j (P_j(Q_i) − P_j(Q_{i−1}))` is `G(Q_i) − G(Q_{i−1})` with
`G = Ghigh C_F` (see `Ghigh`). The paper's iteration is `c = C_F`. -/
noncomputable def primalState {m d : ℕ} (v : Fin m → Fin d → ℝ) (c : ℝ) :
    ℕ → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ
  | 0 => (-(c • perturbR v), Ghigh c (-(c • perturbR v)))
  | i + 1 =>
      ((primalState v c i).1 + correctPrimal v (primalState v c i).2,
        Ghigh c ((primalState v c i).1 + correctPrimal v (primalState v c i).2) -
          Ghigh c (primalState v c i).1)

/-- The inner matrix `Q_i` of the primal iteration. -/
noncomputable def primalQ {m d : ℕ} (v : Fin m → Fin d → ℝ) (c : ℝ) (i : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (primalState v c i).1

/-- The new higher-order deviation `H_i` of the primal iteration. -/
noncomputable def primalH {m d : ℕ} (v : Fin m → Fin d → ℝ) (c : ℝ) (i : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (primalState v c i).2

end EllipsoidFitting


