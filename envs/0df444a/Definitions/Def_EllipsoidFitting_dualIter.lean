-- Prove2me | Definitions.Def_EllipsoidFitting_dualIter
-- name    : EllipsoidFitting_dualIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:44.357183+00:00
-- url     : https://prove2.me/theorems/17a3747b-e3a1-4412-9293-c5e2fe9d5be8
-- title:
--   The dual iteration $(W_i,H_i)$
-- statement:
--   Fix points with Gram matrix $M$, $\gamma=2m/d^2$, a normalizer $c$ (the paper's is $C_F$) and a scalar $c_R$. The dual correction is
--   $$
--   \operatorname{correct}(H)=\frac1\gamma\Pi_SH-H,
--   $$
--   and the iteration is
--   $$
--   W_0=c\,c_R\,R,\quad H_0=G_c(W_0),\qquad W_{i+1}=W_i+\operatorname{correct}(H_i),\quad H_{i+1}=G_c(W_{i+1})-G_c(W_i).
--   $$
--   The dual witness is $\frac1{C_F}F(W)-\Pi_S^\perp I_d$; Proposition 3.5 controls how far $\frac1{C_F}F(W_i)$ is from $S$.
--
--   **Formalization Note** $H_0$ is unscaled, $H_0=G(W_0)$, as in the summary (p.38) and the proof (p.39, "$F(W_0)=C_FI_d+W_0+H_0$"); the underbrace on p.37 placing $1/C_F$ inside $H_0$ is read as a slip. The paper writes the update as $\Delta_{i+1}=\operatorname{correct}(H_i)$, $W_{i+1}=W_i+\Delta_{i+1}$.
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), §3.2, pp.37–38 (PDF pp.39–40), Summary of the Initialization and Iterative Procedure for Refutation

import Mathlib
import Definitions.Def_EllipsoidFitting_perturbR
import Definitions.Def_EllipsoidFitting_Fpos

set_option autoImplicit false

namespace EllipsoidFitting

open Matrix

/-- **The dual correction.** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase Transition for
Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), §3.2, p.38: "∆i+1 = correct(Hi) :=
(1/γ ΠS Hi − Hi) = 1/γ (L∗M−1LHi − γHi)".

`correctDual v X = (1/γ) Π_S X − X` with `γ = 2m/d²`. -/
noncomputable def correctDual {m d : ℕ} (v : Fin m → Fin d → ℝ)
    (X : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / gammaRatio d m) • projS v X - X

/-- **The dual iteration** (§3.2, p.38, "Summary of the Initialization and Iterative Procedure
for Refutation"): "W0 := CF cR R"; "Hi := ∑_{j≥2} bj (Pj(Wi) − Pj(Wi−1))"; "∆i+1 = correct(Hi)";
"Wi+1 := Wi + ∆i+1".

`dualState v c cR i = (W_i, H_i)` with normalizer `c` in place of `C_F`:
`W_0 = c c_R R`, `H_0 = G_c(W_0)`, `W_{i+1} = W_i + correctDual(H_i)`,
`H_{i+1} = G_c(W_{i+1}) − G_c(W_i)`, where `G_c(X) = F(X) − c I − X` (`Ghigh`).

**Formalization Note** `H_0` is unscaled, `H_0 = G(W_0)`: the proof on p.39 uses "F(W0) = CF Id
+ W0 + H0" and the summary on p.38 gives no `1/C_F`; the underbrace on p.37 that puts `1/C_F`
inside `H_0` is read as a slip. The paper's iteration is `c = C_F`. -/
noncomputable def dualState {m d : ℕ} (v : Fin m → Fin d → ℝ) (c cR : ℝ) :
    ℕ → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ
  | 0 => (c • cR • perturbR v, Ghigh c (c • cR • perturbR v))
  | i + 1 =>
      ((dualState v c cR i).1 + correctDual v (dualState v c cR i).2,
        Ghigh c ((dualState v c cR i).1 + correctDual v (dualState v c cR i).2) -
          Ghigh c (dualState v c cR i).1)

/-- The dual inner matrix `W_i`. -/
noncomputable def dualW {m d : ℕ} (v : Fin m → Fin d → ℝ) (c cR : ℝ) (i : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (dualState v c cR i).1

/-- The new image-constraint deviation `H_i` of the dual iteration. -/
noncomputable def dualH {m d : ℕ} (v : Fin m → Fin d → ℝ) (c cR : ℝ) (i : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (dualState v c cR i).2

end EllipsoidFitting


