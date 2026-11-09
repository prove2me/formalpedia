-- Prove2me | Definitions.Def_OnlineCarpoolingLei_Oblivious_Majorant
-- name    : OnlineCarpoolingLei_Oblivious_Majorant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:00.537187+00:00
-- url     : https://prove2.me/theorems/d79f8b20-fe2f-4559-b9b0-41c9573d2fa3
-- title:
--   The high-dimensional transform $\Psi_f(x)=\Psi_{g_{x^\perp}}(\langle x,e\rangle)$
-- statement:
--   Fix an edge $e=\mathbf 1_u-\mathbf 1_v$, so $\|e\|^2=2$, and write
--   $$x^\perp=x-\tfrac12\langle x,e\rangle e$$
--   for the orthogonal projection onto $e^\perp$. For $f:\mathbb R^n\to\mathbb R$ and $y\in e^\perp$ let $g_y(s)=f\big(y+\tfrac s2e\big)$, the restriction of $f$ to the line through $y$ parallel to $e$, parametrized so that $s=\langle x,e\rangle$. Define
--   $$\Psi_f(x)=\Psi_{g_{x^\perp}}(\langle x,e\rangle),$$
--   with $\Psi_g$ as in (5.1). The moves $x\mapsto x\pm e$ shift the coordinate $s$ by $\pm2$. Lemma 6.1 shows that $\Psi_f$ is again a test function in $\mathcal C_+$, majorizes the value of an allowed move, and has Gaussian integral at most that of $f$.
--
--   **Formalization Note** $g_y$ is defined for every $y$; only $y=x^\perp\in e^\perp$ is used.
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Section 6 and Lemma 6.1, p.11 (PDF p.11)

import Mathlib
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Model
import Definitions.Def_OnlineCarpoolingLei_Oblivious_OneDimTransform

/-!
Yuhao Lei, *Online carpooling against an oblivious adversary*, STOC 2027 submission #416
(October 2026), §6 (p.11): the projection `x^⊥ = x − (1/2)⟨x,e⟩e`, the restriction
`g_y(s) = f(y + (s/2) e)`, and `Ψ_f(x) = Ψ_{g_{x^⊥}}(⟨x, e⟩)`.
-/

namespace OnlineCarpoolingLei.Oblivious

/-- `x^⊥ = x − (1/2)⟨x, e⟩ e`, the projection onto `e^⊥`. -/
noncomputable def perp {n : ℕ} (e : Edge n) (x : Fin n → ℝ) : Fin n → ℝ :=
  x - ((1 / 2 : ℝ) * ip x e.vecR) • e.vecR

/-- `g_y(s) = f(y + (s/2) e)`, the restriction of `f` to the line through `y` parallel to `e`
(used for `y ∈ e^⊥`). -/
noncomputable def gLine {n : ℕ} (f : (Fin n → ℝ) → ℝ) (e : Edge n) (y : Fin n → ℝ) : ℝ → ℝ :=
  fun s => f (y + (s / 2) • e.vecR)

/-- `Ψ_f(x) = Ψ_{g_{x^⊥}}(⟨x, e⟩)`. -/
noncomputable def psiF {n : ℕ} (e : Edge n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  psi1 (gLine f e (perp e x)) (ip x e.vecR)

end OnlineCarpoolingLei.Oblivious


