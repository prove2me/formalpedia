-- Prove2me | Definitions.Def_ZeroOneSCO_Algorithm
-- name    : ZeroOneSCO_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:53:07.620415+00:00
-- url     : https://prove2.me/theorems/609ddf8e-9305-432d-abed-6d2975c410b3
-- title:
--   A run of Algorithm 1 (SNSCO)
-- statement:
--   A **run** of Algorithm 1 with parameters $\rho,\tau,\underline\mu,\gamma>0$ and $\nu,\pi\in(0,1)$ is a sequence $(w^\ell,T_\ell,H^\ell,\mu_\ell,d^\ell,t_\ell)_{\ell\ge0}$ such that, with $\mathcal V_\ell:=U_{T_\ell}$ built from $\Lambda^\ell$, for every $\ell$:
--
--   1. $T_\ell\in\mathbb T(\Lambda^\ell;s)$ and $H^\ell\in\partial\varphi(w^\ell;\mathcal V_\ell)$;
--   2. $\mu_0=\min\{\underline\mu,\rho\|F(w^0;\mathcal V_0)\|\}$ and $\mu_\ell=\min\{\nu\mu_{\ell-1},\rho\|F(w^\ell;\mathcal V_\ell)\|\}$ for $\ell\ge1$;
--   3. if the system $\nabla F_{\mu_\ell}(w^\ell;\mathcal V_\ell)\,d=-F(w^\ell;\mathcal V_\ell)$ is solvable, then $d^\ell$ solves it, and otherwise $d^\ell=-F(w^\ell;\mathcal V_\ell)$;
--   4. $t_\ell$ is the least $t\in\{0,1,2,\dots\}$ with $\|G(x^\ell+\pi^t d^\ell_x)\|_0^+\le(\gamma+1)s$, where $d^\ell_x$ is the first $K$ entries of $d^\ell$;
--   5. $w^{\ell+1}=w^\ell+\pi^{t_\ell}d^\ell$.
--
--   Any selection of $T_\ell$ and $H^\ell$ is allowed. This predicate is the object about which the local convergence theorem speaks.
--
--   **Formalization Note** The run has no stopping test, which corresponds to $\mathtt{tol}=0$ and $\mathtt{maxIt}=\infty$: a stopped run is a prefix of such a sequence. A run need not exist from a given start, since $H^\ell$ or the least $t_\ell$ may fail to exist.
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, p.19, Algorithm 1, (77)–(80)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_ZeroOneSCO_Columns
import Definitions.Def_ZeroOneSCO_Equations

namespace ZeroOneSCO

/-- A run of Algorithm 1 (SNSCO), arXiv:2210.11889v5, p.19, with sequences `w^ℓ`, `T_ℓ`, `H^ℓ`, `µ_ℓ`,
`d^ℓ`, `t_ℓ` and parameters `ρ, τ, µ̲, γ > 0`, `ν, π ∈ (0,1)`. Write `V_ℓ := U_{T_ℓ}`.
The selection is (77), the regularization is line 2 and (79), the direction is lines 4–8 with (78),
the step size is line 9 with (80), the update is line 10.

**Formalization Note.** A run has no stopping test: `tol = 0` and `maxIt = ∞`. A stopped run is a
prefix of such a sequence. Every selection `T_ℓ`, `H^ℓ` is allowed. A run need not exist from a
given start, as `H^ℓ` or the least `t_ℓ` may fail to exist. -/
structure IsSNSCORun {K M N : ℕ} [NeZero M] (f : Pt K → ℝ) (G : Pt K → Mat M N) (Ω : Set (Pt K))
    (s : ℕ) (ρ τ μbar γ ν π : ℝ) (w : ℕ → Wsp K M N) (T : ℕ → Finset (Fin N))
    (H : ℕ → Wsp K M N →L[ℝ] Pt K) (μ : ℕ → ℝ) (d : ℕ → Wsp K M N) (t : ℕ → ℕ) : Prop where
  ρ_pos : 0 < ρ
  τ_pos : 0 < τ
  μbar_pos : 0 < μbar
  γ_pos : 0 < γ
  ν_mem : 0 < ν ∧ ν < 1
  π_mem : 0 < π ∧ π < 1
  /-- `T_ℓ ∈ 𝕋(Λ^ℓ; s)`, (77). -/
  select_T : ∀ ℓ, T ℓ ∈ TSet (Lam G τ (w ℓ)) s
  /-- `H^ℓ ∈ ∂ϕ(w^ℓ; U_{T_ℓ})`, (77). -/
  select_H : ∀ ℓ, H ℓ ∈ NonsmoothNewton.Shared.clarkeJac
    (fun v => phi f G Ω τ v (U (T ℓ) (Lam G τ (w ℓ)))) (w ℓ)
  /-- Line 2: `µ_0 = min{µ̲, ρ‖F(w⁰; U_{T_0})‖}`. -/
  mu_zero : μ 0 = min μbar (ρ * ‖Fmap f G Ω τ (w 0) (U (T 0) (Lam G τ (w 0)))‖)
  /-- (79): `µ_{ℓ+1} = min{νµ_ℓ, ρ‖F(w^{ℓ+1}; U_{T_{ℓ+1}})‖}`. -/
  mu_succ : ∀ ℓ, μ (ℓ + 1) = min (ν * μ ℓ)
    (ρ * ‖Fmap f G Ω τ (w (ℓ + 1)) (U (T (ℓ + 1)) (Lam G τ (w (ℓ + 1))))‖)
  /-- Lines 4–5: if (78) is solvable, `d^ℓ` solves it. -/
  dir_solve : ∀ ℓ, (∃ d' : Wsp K M N,
      applyMat (newtonMat G (μ ℓ) (w ℓ) (U (T ℓ) (Lam G τ (w ℓ))) (H ℓ)) d' =
        -Fmap f G Ω τ (w ℓ) (U (T ℓ) (Lam G τ (w ℓ)))) →
    applyMat (newtonMat G (μ ℓ) (w ℓ) (U (T ℓ) (Lam G τ (w ℓ))) (H ℓ)) (d ℓ) =
      -Fmap f G Ω τ (w ℓ) (U (T ℓ) (Lam G τ (w ℓ)))
  /-- Lines 6–7: otherwise `d^ℓ = −F(w^ℓ; U_{T_ℓ})`. -/
  dir_fallback : ∀ ℓ, (¬ ∃ d' : Wsp K M N,
      applyMat (newtonMat G (μ ℓ) (w ℓ) (U (T ℓ) (Lam G τ (w ℓ))) (H ℓ)) d' =
        -Fmap f G Ω τ (w ℓ) (U (T ℓ) (Lam G τ (w ℓ)))) →
    d ℓ = -Fmap f G Ω τ (w ℓ) (U (T ℓ) (Lam G τ (w ℓ)))
  /-- Line 9, (80): `t_ℓ` is the least `t ∈ {0, 1, 2, …}` with
  `‖G(x^ℓ + π^t d^ℓ_x)‖₀⁺ ≤ (γ + 1)s`. -/
  step_least : ∀ ℓ, IsLeast
    {r : ℕ | (plusZero (G (xPart (w ℓ) + π ^ r • xPart (d ℓ))) : ℝ) ≤ (γ + 1) * s} (t ℓ)
  /-- Line 10: `w^{ℓ+1} = w^ℓ + π^{t_ℓ} d^ℓ`. -/
  update : ∀ ℓ, w (ℓ + 1) = w ℓ + π ^ t ℓ • d ℓ

end ZeroOneSCO


