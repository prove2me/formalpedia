-- Prove2me | Definitions.Def_DecodablePOMDP_RevealResidual
-- name    : DecodablePOMDP_RevealResidual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:53.649725+00:00
-- url     : https://prove2.me/theorems/af356747-33b6-4114-8935-12f970bd4c90
-- title:
--   Reveal channel $R_h$ and residual channel $N_h$
-- statement:
--   With $c=\rho/2$, the **reveal channel** and the **residual channel** of $J_h$ are
--
--   $$R_h((y,\hat s)\mid s)=\begin{cases}\dfrac{J_h((y,s)\mid s)}{d_{h,s}},&\hat s=s,\\[1ex]0,&\hat s\ne s,\end{cases}\qquad N_h=\frac{J_h-cR_h}{1-c}.$$
--
--   Under $d_{h,s}\ge\rho$ both are channels, $J_h=cR_h+(1-c)N_h$, and $R_h$ only emits observations whose second coordinate is the true state (Lemma 2). The killed POMDP uses $R_h$ on a reveal and $N_h$ otherwise.
--
--   **Formalization Note** Division by $d_{h,s}$ and by $1-c$ is only reached with $d_{h,s}\ge\rho>0$ and $\rho\le1$.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), App. A.2, p.14

import Mathlib
import Definitions.Def_DecodablePOMDP_Augmented

namespace DecodablePOMDP

/-- **Reveal channel** `R_h` (A.2, p.14):
`R_h((y, ŝ) | s) = J_h((y, s) | s) / d_{h,s}` if `ŝ = s`, and `0` if `ŝ ≠ s`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.2, p.14: "define the reveal channel
Rh by Rh((y, ŝ)|s) = Jh((y,s)|s)/dh,s if ŝ = s, 0 if ŝ ≠ s".

**Formalization Note.** `z = (y, ŝ)`; `J_h((y, s) | s) = K_h(y | s) D_h(s | y)`. Lean's `x / 0 = 0`
is never reached under the ρ-decoder hypothesis (`d_{h,s} ≥ ρ > 0`). -/
noncomputable def reveal {S A O : Type} [DecidableEq S] [Fintype O] (P : POMDP S A O)
    (D : ℕ → O → S → ℝ) (h : ℕ) (s : S) (z : O × S) : ℝ :=
  if z.2 = s then P.K h s z.1 * D h z.1 s / decodeProb P D h s else 0

/-- **Residual channel** `N_h := (J_h − c R_h) / (1 − c)` with mixing coefficient `c = ρ/2`
(A.2, p.14).

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.2, p.14: "we define the residual
channel by Nh := (Jh − cRh)/(1 − c)", with "c = ρ/2" (Lemma 2, p.7). -/
noncomputable def residual {S A O : Type} [DecidableEq S] [Fintype O] (P : POMDP S A O)
    (D : ℕ → O → S → ℝ) (ρ : ℝ) (h : ℕ) (s : S) (z : O × S) : ℝ :=
  ((augmented P D).K h s z - ρ / 2 * reveal P D h s z) / (1 - ρ / 2)

end DecodablePOMDP


