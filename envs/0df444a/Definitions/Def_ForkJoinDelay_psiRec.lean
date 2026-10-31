-- Prove2me | Definitions.Def_ForkJoinDelay_psiRec
-- name    : ForkJoinDelay_psiRec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:15.479935+00:00
-- url     : https://prove2.me/theorems/ab0cbeef-7ddc-4c40-80dd-759b5da8a1d3
-- title:
--   The transform computed by the recursion, $\Psi^{\mathrm{rec}}_{k,h_1,h_2}$
-- statement:
--   Define $\Psi^{\mathrm{rec}}_{k,h_1,h_2}(w_0,w_{FJ})$ by recursion on $k$:
--
--   $$\Psi^{\mathrm{rec}}_{0,h_1,h_2}=\mathrm{step}(Z)_{h_1,h_2},\qquad \Psi^{\mathrm{rec}}_{k,h_1,h_2}=\mathrm{step}\bigl(\Psi^{\mathrm{rec}}_{k-1,\cdot,\cdot}\bigr)_{h_1,h_2}\quad(k\ge1),$$
--
--   where $\mathrm{step}$ is the right-hand side of (3) and (6), with $a$ in the closed form of (4) and $b,c,d$ its tail sums, and $Z_{x,y}=Z_{x,y}(w_{FJ})$ is the boundary transform (5).
--
--   This is the computational method of §3. It is defined without reference to the queueing model; the goal theorem states that it computes the model's transform.
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), Eq. (6), p.12 (k = 0) and Eq. (3), p.11 (k ≥ 1)

import Mathlib
import Definitions.Def_ForkJoinDelay_boundaryLST
import Definitions.Def_ForkJoinDelay_recStep

namespace ForkJoinDelay

/-- **The transform computed by the recursion, `Ψ^rec_{k,h₁,h₂}(w₀, w_FJ)`.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, Eq. (6), p.12 (`k = 0`) and Eq. (3), p.11 (`k ≥ 1`):

`Ψ^rec_{0,h₁,h₂} = step Z h₁ h₂` and `Ψ^rec_{k,h₁,h₂} = step Ψ^rec_{k−1} h₁ h₂`,

where `step` is `recStep` (the right-hand side of (3) and (6), with `a` in the closed form (4)
and `b, c, d` the tail sums of pp.10–11) and `Z_{x,y} = boundaryLST μ₁ μ₂ x y w_FJ` is (5).

**Formalization Note.** This is the computational recipe of §3, defined by recursion on `k`
alone; it does not mention the queueing model. The goal theorem `joint_lst_recursion` states
that it equals the model's transform `psi`. -/
noncomputable def psiRec (μ₀ μ₁ μ₂ : ℝ) (w₀ wFJ : ℂ) : ℕ → ℕ → ℕ → ℂ
  | 0 => fun h₁ h₂ => recStep μ₀ μ₁ μ₂ w₀ (fun x y => boundaryLST μ₁ μ₂ x y wFJ) h₁ h₂
  | k + 1 => fun h₁ h₂ => recStep μ₀ μ₁ μ₂ w₀ (psiRec μ₀ μ₁ μ₂ w₀ wFJ k) h₁ h₂

end ForkJoinDelay


