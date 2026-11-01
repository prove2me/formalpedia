-- Prove2me | Definitions.Def_LPResolvingRM_tauS
-- name    : LPResolvingRM_tauS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:42:10.860984+00:00
-- url     : https://prove2.me/theorems/0fb3cc4b-54c4-49d8-ac88-b07c6ae8a4ca
-- title:
--   The region $\mathfrak B$, the stopping time $\tau_S$, and stopping times adapted to $(B_t)$
-- statement:
--   With the binding set $\mathcal I^*$ of $y^*$ and its complement $\mathcal I'$, the region of the general nondegenerate case is
--   $$\mathfrak B:=\Big(\bigotimes_{i\in\mathcal I^*}[b_i-L,b_i+L]\Big)\otimes\Big(\bigotimes_{i\in\mathcal I'}[b_i-L,+\infty)\Big),$$
--   and the stopping time at which the LP's structure may change is
--   $$\tau_S:=\min\{t\le T: b_t\notin\mathfrak B\}\cup\{T+1\}.$$
--   A random time $\tau'$ is a **stopping time adapted to $(B_t)$** when the event $\{\tau'=t\}$ is decided by $B_1,\dots,B_t$.
--
--   **Formalization Note** This is the definition of Appendix C.1 (p.35); the §3.2 display (p.11) prints "$>-L$" for $\mathcal I'$, a typo.
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Appendix C.1, p.35; Corollary 1, p.11

import Definitions.Def_LPResolvingRM_regret

open scoped Classical

namespace LPResolvingRM

/-- **The region `𝔅`** of the general nondegenerate case (arXiv:2101.11092v3, Appendix C.1,
p.35): `𝔅 := ⨂_{i∈I*} [b_i − L, b_i + L] ⨂ ⨂_{i∈I'} [b_i − L, +∞)`, where `I*` is the binding
set of the optimal solution `y*` of LP (6) and `I'` its complement. -/
def region {n m : ℕ} (I : Instance n m) (ystar : Fin n → ℝ) (L : ℝ) (r : Fin m → ℝ) : Prop :=
  (∀ i ∈ binding I ystar, |r i - I.b i| ≤ L) ∧ (∀ i ∉ binding I ystar, I.b i - L ≤ r i)

/-- **The stopping time `τ_S`** (arXiv:2101.11092v3, Appendix C.1, p.35):
`τ_S := min{t ≤ T : |b_{i,t} − b_i| > L for some i ∈ I*} ∪ {t ≤ T : b_{i,t} − b_i < −L for some
i ∈ I'} ∪ {T + 1} = min{t ≤ T : b_t ∉ 𝔅} ∪ {T + 1}`.

**Formalization Note.** `t` ranges over the paper's periods `1, …, T`, and
`b_t = LPResolvingRM.avgCap … (t − 1)`. This is the C.1 definition; the §3.2 display (p.11)
prints "> −L" for `I'`, a typo. -/
noncomputable def tauS {n m : ℕ} (I : Instance n m) (ystar : Fin n → ℝ) (L : ℝ) (T : ℕ)
    (ω : Fin T → Fin n) (β : Fin T → Bool) : ℕ :=
  if h : ∃ t, 1 ≤ t ∧ t ≤ T ∧ ¬ region I ystar L (avgCap I T ω β (t - 1)) then Nat.find h
  else T + 1

/-- `τ'` is a **stopping time adapted to the process `B_t`** (arXiv:2101.11092v3, Corollary 1,
p.11): whether `τ' = t` is decided by `B_1, …, B_t`, i.e. two sample paths with the same
`B_1, …, B_t` (the Lean `cap … k` for `k < t`) agree on the event `{τ' = t}`. -/
def IsBStoppingTime {n m : ℕ} (I : Instance n m) (T : ℕ)
    (τ' : (Fin T → Fin n) → (Fin T → Bool) → ℕ) : Prop :=
  ∀ ω β ω' β' t, (∀ k < t, cap I T ω β k = cap I T ω' β' k) → (τ' ω β = t ↔ τ' ω' β' = t)

end LPResolvingRM


