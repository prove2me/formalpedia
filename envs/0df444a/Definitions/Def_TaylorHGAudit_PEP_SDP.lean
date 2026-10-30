-- Prove2me | Definitions.Def_TaylorHGAudit_PEP_SDP
-- name    : TaylorHGAudit_PEP_SDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:48:24.425806+00:00
-- url     : https://prove2.me/theorems/6cd12449-1a0f-4a36-b642-0721fcb81288
-- title:
--   Reciprocal coefficient matrices and independent SDP value
-- statement:
--   Let $I=\{0,\ldots,N,*\}$. Use the published vectors $h_i,u_i\in\mathbb R^{N+2}$, with $h_*=u_*=0$, the first $N+1$ coordinates for gradients, and the final coordinate for the initial displacement. Put $q=1/L$, $a=(1-\mu q)^{-1}$, $\Delta h=h_i-h_j$, and $\Delta u=u_i-u_j$. Writing $\operatorname{sym}(v,w)=vw^\top+wv^\top$, define
--
--   $$2A_{ij}=a\operatorname{sym}(u_j,\Delta h)+qa\Delta u\Delta u^\top-\mu qa\operatorname{sym}(u_i,\Delta h)+\mu a\Delta h\Delta h^\top.$$
--
--   The radius matrix is the published $A_R=e_{N+2}e_{N+2}^\top$. Extend $v\in\mathbb R^{N+1}$ by $v_*=0$. Independently of any function, set
--
--   $$w^{\rm sdp}_{\mu,L}=\sup_{G,v}\left\{b^\top v+\operatorname{Tr}(CG):\ G\succeq0,\ v_j-v_i+\operatorname{Tr}(GA_{ij})\le0\ (i,j\in I),\ \operatorname{Tr}(GA_R)\le R^2\right\}.$$
--
--   These explicit coefficients and constraints define the matrix problem in Theorem 5. No realization, function witness, or rank constraint is part of its definition.
--
--   **Formalization Note** Both $G$ and $C$ are real matrices; Mathlib's `PosSemidef` includes symmetry. The supremum is in `EReal`. At finite $L$, the coefficients of $2A_{ij}$ equal $L/(L-\mu),1/(L-\mu),\mu/(L-\mu),L\mu/(L-\mu)$ with the third term using $h_j-h_i$. At infinity the coefficients are $1,0,0,\mu$. This reciprocal reading retains the source's entire stated parameter range; $\mu<L$ excludes the zero denominator.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, §3.3 coefficient matrices, p. 13 (PDF 13); Theorem 5 and (sdp-PEP), p. 14 (PDF 14); infinity conventions, Definition 1 p. 5 (PDF 5), Corollary 2 p. 11 (PDF 11).

import Mathlib
import Definitions.Def_TaylorHGAudit_PEP_Class
import Definitions.Def_TaylorHG_PEP_SDP

namespace TaylorHGAudit.PEP

/-- Reciprocal reading of §3.3, p. 13: `a = 1/(1-μ/L)`.
Every theorem uses `μ < L`, hence the denominator is strictly positive. -/
noncomputable def reciprocalA (μ : NNReal) (L : ENNReal) : ℝ :=
  1 / (1 - (μ : ℝ) * invL L)

/-- The full p. 13 coefficient matrix, including `L=∞`.
At finite L the coefficients in `2 Aᵢⱼ` are `L/(L-μ), 1/(L-μ), μ/(L-μ), Lμ/(L-μ)`;
at infinity they are `1, 0, 0, μ`. The third symmetric term uses `h_j-h_i`. -/
noncomputable def Amat {N : ℕ} (μ : NNReal) (L : ENNReal)
    (H : Matrix (Fin N) (Fin N) ℝ) (i j : Option (Fin (N + 1))) :
    Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ :=
  let hi := TaylorHG.PEP.hvec H i
  let hj := TaylorHG.PEP.hvec H j
  let ui := TaylorHG.PEP.uvec i
  let uj := TaylorHG.PEP.uvec j
  let q := invL L
  let a := reciprocalA μ L
  (1 / 2 : ℝ) •
    (a • (TaylorHG.PEP.outer uj (hi - hj) + TaylorHG.PEP.outer (hi - hj) uj) +
     (q * a) • TaylorHG.PEP.outer (ui - uj) (ui - uj) +
     ((μ : ℝ) * q * a) •
       (TaylorHG.PEP.outer ui (hj - hi) + TaylorHG.PEP.outer (hj - hi) ui) +
     ((μ : ℝ) * a) • TaylorHG.PEP.outer (hi - hj) (hi - hj))

/-- Independent constraints of (sdp-PEP), p. 14. `PosSemidef` includes real symmetry.
All ordered pairs, including both star orientations and diagonal pairs, occur. -/
def SdpFeasible {N : ℕ} (μ : NNReal) (L : ENNReal) (R : ℝ)
    (H : Matrix (Fin N) (Fin N) ℝ)
    (G : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) (v : Fin (N + 1) → ℝ) : Prop :=
  G.PosSemidef ∧
  (∀ i j : Option (Fin (N + 1)), TaylorHG.PEP.fext v j - TaylorHG.PEP.fext v i +
    (G * Amat μ L H i j).trace ≤ 0) ∧
  (G * TaylorHG.PEP.ARmat N).trace ≤ R ^ 2

/-- The independent extended-real value of (sdp-PEP), p. 14.
No rank constraint, function witness or attainment condition occurs. -/
noncomputable def sdpValue {N : ℕ} (μ : NNReal) (L : ENNReal) (R : ℝ)
    (H : Matrix (Fin N) (Fin N) ℝ) (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) : EReal :=
  sSup {r : EReal | ∃ (G : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ)
      (v : Fin (N + 1) → ℝ),
    SdpFeasible μ L R H G v ∧ r = ((b ⬝ᵥ v + (C * G).trace : ℝ) : EReal)}

end TaylorHGAudit.PEP


