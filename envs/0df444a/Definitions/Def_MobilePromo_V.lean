-- Prove2me | Definitions.Def_MobilePromo_V
-- name    : MobilePromo_V
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:54.714873+00:00
-- url     : https://prove2.me/theorems/eaa0a0c1-2f86-4c5e-b619-bae365a3a0e9
-- title:
--   The clairvoyant dynamic program: $V_{i,t}$, $f^l$, $b^*_{i,t,l}$ and $\mathcal{U}_{A\Gamma_l}$
-- statement:
--   For $\alpha\in\mathbb R$, put
--
--   $$
--   f^l(b_l,\alpha,\gamma_l)=p_l(\gamma_l,b_l)(b_l-e-\alpha),\qquad b_l^*(\alpha,\gamma_l)=\arg\min_{b_l\in B}f^l(b_l,\alpha,\gamma_l).
--   $$
--
--   The optimal cost-to-go of a season when $\gamma$ is known satisfies $V_{i,T+1}(\boldsymbol c;\gamma)=0$ and
--
--   $$
--   V_{i,t}(\boldsymbol c;\gamma)=\mathbb 1\{\mathcal F\ne\emptyset\}\sum_{l}q_l\min_{b_l\in B}f^l\bigl(b_l,\Delta V_{i,t+1}(\boldsymbol c;\gamma),\gamma_l\bigr)+V_{i,t+1}(\boldsymbol c;\gamma),
--   $$
--
--   where, for $\mathcal F\ne\emptyset$, $\Delta V_{i,t+1}(\boldsymbol c;\gamma)=V_{i,t+1}(\boldsymbol c;\gamma)-V_{i,t+1}((c_1,\dots,c_g-1,\dots,c_m);\gamma)$. The optimal bid (7) is $b^*_{i,t,l}(\boldsymbol c;\gamma)=b_l^*(\Delta V_{i,t+1}(\boldsymbol c;\gamma),\gamma_l)$ if $\mathcal F\ne\emptyset$, and $0$ (no bid) otherwise. Finally,
--
--   $$
--   \mathcal U_{A\Gamma_l}=\bigl\{(\alpha,\gamma_l)\in[b^{\min}-e,0]\times\Gamma_l^{(0)}\ \big|\ b^{\min}<b_l^*(\alpha,\gamma_l)<b^{\max}\bigr\}.
--   $$
--
--   **Formalization Note** The recursion runs on the number of periods left, which is exact for $t\le T+1$. The inner minimum is an infimum of real numbers and $b^*_l$ a chosen minimizer; under Assumption 1 and $\gamma_l\in\Gamma_l^{(0)}$ the infimum is attained, by continuity on the compact $B$, and Lemma A.1(i) makes the minimizer unique. Every theorem therefore takes $\gamma\in\Gamma^{(0)}$.
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, recursion and (7), p.14; Lemma A.1, A1–A2 (PDF 35–36)

import Mathlib
import Definitions.Def_MobilePromo_Model
import Definitions.Def_MobilePromo_Season

set_option autoImplicit false

namespace MobilePromo

/-- `f^l(b_l, α, γ_l) = p_l(γ_l, b_l)(b_l - e - α)` (SSRN 3523491, Lemma A.1, A1, PDF 35). -/
noncomputable def f (M : Model) (l : Fin M.L) (b α : ℝ) (γl : Param (M.n l)) : ℝ :=
  M.p l γl b * (b - M.e - α)

/-- `min_{b ∈ B} f^l(b, α, γ_l)`, the inner minimum of the recursion of p.14.

**Formalization Note** An infimum of reals. Under Assumption 1 and `γ_l ∈ Γ_l⁽⁰⁾` it is attained, because
`f^l` is continuous on the compact `B`; every theorem takes `γ ∈ Γ⁽⁰⁾`. -/
noncomputable def minF (M : Model) (l : Fin M.L) (α : ℝ) (γl : Param (M.n l)) : ℝ :=
  sInf ((fun b => f M l b α γl) '' M.B)

/-- `b*_l(α, γ_l) = arg min_{b ∈ B} f^l(b, α, γ_l)` (SSRN 3523491, Lemma A.1, A1, PDF 35).

**Formalization Note** A chosen minimizer; Lemma A.1(i) (`lemma_A1_i`) shows it is the only one for
`γ_l ∈ Γ_l⁽⁰⁾`. -/
noncomputable def bStarOf (M : Model) (l : Fin M.L) (α : ℝ) (γl : Param (M.n l)) : ℝ :=
  Classical.epsilon fun b => b ∈ M.B ∧ ∀ b' ∈ M.B, f M l b α γl ≤ f M l b' α γl

/-- The optimal cost-to-go with `r` periods left (SSRN 3523491, recursion on p.14), so that `Vgo r` is
`V_{i, T + 1 - r}`, the current period being `T - r`. -/
noncomputable def Vgo (M : Model) {T : ℕ} (S : Season T) (γ : M.ParamVec) :
    ℕ → (Fin S.m → ℕ) → ℝ
  | 0, _ => 0
  | r + 1, c =>
    if (S.activeSet (T - r) c).Nonempty then
      ∑ l, M.q l * minF M l (Vgo M S γ r c - Vgo M S γ r (S.afterWin (T - r) c)) (γ l)
        + Vgo M S γ r c
    else Vgo M S γ r c

/-- The optimal cost-to-go `V_{i,t}(c; γ)` of season `S` (SSRN 3523491, p.14):
`V_{i,t}(c; γ) = 1{F ≠ ∅} ∑_l q_l min_{b_l ∈ B} p_l(γ_l, b_l)[b_l - e - ΔV_{i,t+1}(c; γ)] + V_{i,t+1}(c; γ)`,
with `V_{i,T+1} = 0` and `ΔV_{i,t+1}(c; γ) = V_{i,t+1}(c; γ) - V_{i,t+1}((c₁, …, c_g - 1, …, c_m); γ)`.

**Formalization Note** The recursion runs on the periods left, `T + 1 - t`, a truncated subtraction that
is exact for `t ≤ T + 1`. The value is `0` for `t ≥ T + 1`; `t = 0` is junk and never used. -/
noncomputable def V (M : Model) {T : ℕ} (S : Season T) (γ : M.ParamVec) (t : ℕ)
    (c : Fin S.m → ℕ) : ℝ :=
  Vgo M S γ (T + 1 - t) c

/-- `ΔV_{i,t+1}(c; γ)` (SSRN 3523491, p.14). -/
noncomputable def DeltaV (M : Model) {T : ℕ} (S : Season T) (γ : M.ParamVec) (t : ℕ)
    (c : Fin S.m → ℕ) : ℝ :=
  V M S γ (t + 1) c - V M S γ (t + 1) (S.afterWin t c)

/-- The optimal bid `b*_{i,t,l}(c; γ)` of (7) (SSRN 3523491, (7), p.14): `b*_l(ΔV_{i,t+1}(c; γ), γ_l)` if
`F ≠ ∅`, and `0` (no bid) if `F = ∅`. -/
noncomputable def bStar (M : Model) {T : ℕ} (S : Season T) (γ : M.ParamVec) (t : ℕ)
    (c : Fin S.m → ℕ) (l : Fin M.L) : ℝ :=
  if (S.activeSet t c).Nonempty then bStarOf M l (DeltaV M S γ t c) (γ l) else 0

/-- The set `UAΓ_l` of Lemma A.1(ii) (SSRN 3523491, A2, PDF 36):
`{(α, γ_l) ∈ [bmin - e, 0] × Γ_l⁽⁰⁾ | bmin < b*_l(α, γ_l) < bmax}`. -/
def UAΓ (M : Model) (l : Fin M.L) : Set (ℝ × Param (M.n l)) :=
  {x | x.1 ∈ Set.Icc (M.bmin - M.e) 0 ∧ x.2 ∈ M.Γ₀ l ∧
    M.bmin < bStarOf M l x.1 x.2 ∧ bStarOf M l x.1 x.2 < M.bmax}

end MobilePromo


