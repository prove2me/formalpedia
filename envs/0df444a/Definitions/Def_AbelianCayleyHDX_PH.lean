-- Prove2me | Definitions.Def_AbelianCayleyHDX_PH
-- name    : AbelianCayleyHDX_PH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:33:50.507521+00:00
-- url     : https://prove2.me/theorems/1b516834-f4a6-4ff4-b218-c57a57333080
-- title:
--   The operator $P_H = (\tilde H^{\mathsf T}\tilde H - \rho I_M)/(2\rho)$
-- statement:
--   For a binary matrix $H$ with $M$ columns and $\rho \in \mathbb N$,
--   $$P_H = \frac{\tilde H^{\mathsf T} \tilde H - \rho I_M}{2\rho}.$$
--   For a relation matrix as in Section 2.4 it is the normalized adjacency operator of the link at the identity of $X_H$ (Eq. (2.1)).
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Eq. (2.1), p.9

import Mathlib
import Definitions.Def_AbelianCayleyHDX_Htilde

namespace AbelianCayleyHDX

/-- **The operator `P_H`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Eq. (2.1), p.9): `P_H = (H̃ᵀ H̃ − ρ I_M) / (2ρ)`, the
normalized adjacency operator of the link at the identity of `X_H`. -/
noncomputable def PH {ι κ : Type*} [Fintype ι] [DecidableEq κ] (H : Matrix ι κ (ZMod 2)) (ρ : ℕ) :
    Matrix κ κ ℝ :=
  (1 / (2 * (ρ : ℝ))) • ((Htilde H).transpose * Htilde H - (ρ : ℝ) • (1 : Matrix κ κ ℝ))

end AbelianCayleyHDX


