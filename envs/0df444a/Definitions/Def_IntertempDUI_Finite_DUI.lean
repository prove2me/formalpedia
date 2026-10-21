-- Prove2me | Definitions.Def_IntertempDUI_Finite_DUI
-- name    : IntertempDUI_Finite_DUI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:58.079207+00:00
-- url     : https://prove2.me/theorems/d0072178-d29a-4254-806c-4df273103eb3
-- title:
--   §4 — discounted utility integral representation
-- statement:
--   A discounted utility integral representation consists of a continuous utility $u:\mathcal X\to\mathbb R$ and a normalized continuous increasing time weight $\rho$ on $[0,T]$. The time weight satisfies $\rho(0)=0$ and $\rho(T)=1$.
--
--   $$\alpha\succeq_{\mathcal S}\beta\quad\Longleftrightarrow\quad\int_{\mathcal S}u(\alpha(t))\,d\rho(t)\ge\int_{\mathcal S}u(\beta(t))\,d\rho(t).$$
--
--   The formula applies to feasible restrictions on each span and to the corresponding primitive interval orders. This is the representation characterized by Theorem 1.
--
--   **Formalization Note** The source's Riemann–Stieltjes expression is modeled by the Lebesgue–Stieltjes measure of a continuous `StieltjesFunction`, restricted to the span. The extension of $\rho$ outside $[0,T]$ is auxiliary.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, SSRN 3232014 (August 10, 2018), p. 12, equation (7); https://ssrn.com/abstract=3232014

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Axioms

namespace IntertempDUI.Finite

/-- The span integral in (7), using the Lebesgue–Stieltjes measure associated to ρ. -/
noncomputable def rsIntegral {T : ℝ} (hT : 0 ≤ T)
    (ρ : StieltjesFunction ℝ) (S : Set (Time T)) (g : Time T → ℝ) : ℝ :=
  ∫ t in Subtype.val '' S, g (Set.projIcc (0 : ℝ) T hT t) ∂ρ.measure

/-- The normalized discounted utility representation (7), pp. 12–13. -/
def IsDUIRep {T : ℝ} {X : Type*} [TopologicalSpace X]
    (hT : 0 ≤ T) (A : Set (Traj T X)) (pref : Pref T X)
    (ρ : StieltjesFunction ℝ) (u : X → ℝ) : Prop :=
  Continuous u ∧ Continuous (ρ : ℝ → ℝ) ∧
  StrictMonoOn (ρ : ℝ → ℝ) (Set.Icc 0 T) ∧
  ρ 0 = 0 ∧ ρ T = 1 ∧
  (∀ S, IsTimeSpan S → ∀ a ∈ A, ∀ b ∈ A,
    induced A pref S a b ↔
      rsIntegral hT ρ S (u ∘ a) ≥ rsIntegral hT ρ S (u ∘ b)) ∧
  (∀ I, IsTimeInterval I → ∀ a ∈ A, ∀ b ∈ A,
    pref I a b ↔
      rsIntegral hT ρ I (u ∘ a) ≥ rsIntegral hT ρ I (u ∘ b))

end IntertempDUI.Finite


