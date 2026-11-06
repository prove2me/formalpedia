-- Prove2me | Definitions.Def_DecodablePOMDP_Update
-- name    : DecodablePOMDP_Update
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:00.6972+00:00
-- url     : https://prove2.me/theorems/c28510fd-4e7b-4ad0-9c77-44d49d0dd66b
-- title:
--   The weight update (12) and its normalisation (13)
-- statement:
--   Let $\psi_q(s')=\sum_sT_h(s'\mid s,a)\,\phi^u_{h,q}(s)$ and $c=\rho/2$. For an alive observation $\tilde z$ at stage $h+1$, the unnormalised weights are
--
--   $$\overline w_{h+1,q'}(\tilde z)=\begin{cases}c\sum_{q\in\mathcal Q}w_q\sum_{s'}R_{h+1}(\tilde z\mid s')\,\psi_q(s'),&q'=0,\\ (1-c)\,w_q\sum_{s'}N_{h+1}(\tilde z\mid s')\,\psi_q(s'),&q'=q+1\in\{1,\dots,L-1\},\\ (1-c)\,w_\perp\,\mathbf 1\{h<L\}\sum_{s'}N_{h+1}(\tilde z\mid s')\,\psi_\perp(s'),&q'=\perp,\end{cases}\tag{12}$$
--
--   and, with $\Lambda_h(\tilde z)=\sum_{q'}\overline w_{h+1,q'}(\tilde z)$, the updated weights are $w'_{q'}(\tilde z)=\overline w_{h+1,q'}(\tilde z)/\Lambda_h(\tilde z)$ (13).
--
--   By Lemma 5 this update is exact on the represented beliefs.
--
--   **Formalization Note** When $\Lambda_h(\tilde z)=0$ the normalisation gives the zero vector; the planner never uses that case (footnote 3).
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), App. A.5, p.16, (12)–(13)

import Mathlib
import Definitions.Def_DecodablePOMDP_Admissible

namespace DecodablePOMDP

/-- **Unnormalised weight update** (12) (A.5, p.16). With `ψ_q(s') = Σ_s T_h(s' | s, a) ϕ^u_{h,q}(s)`
and `c = ρ/2`, for an alive observation `z̃` at stage `h + 1`:
* `w_{h+1,0}(z̃) = c Σ_{q∈Q} w_{h,q} Σ_{s'} R_{h+1}(z̃ | s') ψ_q(s')`;
* `w_{h+1,q+1}(z̃) = (1 − c) w_{h,q} Σ_{s'} N_{h+1}(z̃ | s') ψ_q(s')` for `q + 1 ∈ {1, …, L−1}`;
* `w_{h+1,⊥}(z̃) = (1 − c) w_{h,⊥} 1{h < L} Σ_{s'} N_{h+1}(z̃ | s') ψ_⊥(s')`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.5, p.16, (12). -/
noncomputable def unnormWeight {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L h : ℕ) (u : Suffix A O S)
    (w : Option (Fin L) → ℝ) (a : A) (z : O × S) : Option (Fin L) → ℝ
  | some r =>
      if hr : r.val = 0 then
        ρ / 2 * ∑ q, w q * ∑ s', reveal P D (h + 1) s' z *
          ∑ s, P.T h s a s' * phiU P D ρ L h u q s
      else
        (1 - ρ / 2) * w (some ⟨r.val - 1, by omega⟩) * ∑ s', residual P D ρ (h + 1) s' z *
          ∑ s, P.T h s a s' * phiU P D ρ L h u (some ⟨r.val - 1, by omega⟩) s
  | none =>
      (1 - ρ / 2) * w none * (if h < L then 1 else 0) * ∑ s', residual P D ρ (h + 1) s' z *
        ∑ s, P.T h s a s' * phiU P D ρ L h u none s

/-- **Normalised weight update** `w'` (13) (A.5, p.16): `w'_{q'}(z̃) = w_{h+1,q'}(z̃) / Λ_h(z̃)` with
`Λ_h(z̃) = Σ_{q'} w_{h+1,q'}(z̃)`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.5, p.16: "For an alive observation z̃,
define Λh(z̃) := Σ_{q′∈Q} wh+1,q′(z̃). … For z̃ such that Λh(z̃) > 0, we normalize
w′_{q′}(z̃) = wh+1,q′(z̃)/Λh(z̃) (13)".

**Formalization Note.** Lean's `x / 0 = 0` gives the zero vector when `Λ_h(z̃) = 0`; the planner
never uses that branch (footnote 3, p.11). -/
noncomputable def updWeight {S A O : Type} [DecidableEq S] [Fintype S] [Fintype O]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L h : ℕ) (u : Suffix A O S)
    (w : Option (Fin L) → ℝ) (a : A) (z : O × S) : Option (Fin L) → ℝ :=
  fun q' => unnormWeight P D ρ L h u w a z q' / ∑ q, unnormWeight P D ρ L h u w a z q

end DecodablePOMDP


