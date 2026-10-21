-- Prove2me | Definitions.Def_JSEQDelay_Diffusion_Collapse
-- name    : JSEQDelay_Diffusion_Collapse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:39.886272+00:00
-- url     : https://prove2.me/theorems/e86b21c6-f25c-4315-84b4-abf25cdd376c
-- title:
--   (46)–(47), p. 18 — the estimate gap Δ̂ⁿ, the stopping times θⁿ and stopped processes
-- statement:
--   For the $n$-th JSEQ network let $\overline{R}^n(t)=K^{-1}\langle\hat R^n(t),\mathbf 1\rangle$ and
--   $$\hat\Delta^n(t)=\max_{k\in\mathbb K}\hat R^n_k(t)-\overline R^n(t),\qquad t\ge0.\tag{46}$$
--   For a sequence $(r_n)$ of positive numbers converging to zero (the set $\mathcal Z$), let
--   $$\theta^n=\inf\{t\ge0:\hat\Delta^n(t)\ge r_n\},\tag{47}$$
--   with $\inf\emptyset=+\infty$. For a path $Z$, $Z(\cdot\wedge\theta^n)$ is the path stopped at $\theta^n$. The joint process $(\hat A^n,\hat Q^n,\hat L^n,\hat M^n)$ takes values in $\mathbb R^{4K}$.
--
--   These objects appear in Lemmas 5.2 and 5.3, the state-space-collapse step of the proof of Theorem 4.4; the goal itself does not use them.
--
--   **Formalization Note** $\theta^n$ takes values in $[0,\infty]$ so that $\inf\emptyset=\infty$ rather than a junk $0$; the stopped path equals $Z(t)$ for $t\le\theta^n$ and $Z(\theta^n)$ afterwards, and is never stopped when $\theta^n=\infty$. The joint process is the concatenation `Fin.append` of the four $K$-dimensional processes.
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), p. 18, §5.2, (46)–(47); Lemma 5.2, p. 18; Lemma 5.3, p. 20

import Mathlib
import Definitions.Def_JSEQDelay_Diffusion_Model

namespace JSEQDelay.Diffusion

open scoped ENNReal

/-!
Atar & Lipshutz (authors' manuscript of January 12, 2020), §5.2, (46)–(47), p. 18: the
state-space-collapse gap `Δ̂ⁿ`, the stopping times `θⁿ`, and stopped processes.
-/

/-- `Δ̂ⁿ(t) = max_k R̂ⁿ_k(t) − K⁻¹⟨R̂ⁿ(t), 𝟏⟩` (46): the gap between the largest scaled estimated
queue length and their average, for the `n`-th network `(Q, A)`. -/
noncomputable def Delta {Ω : Type*} {K : ℕ} (n : ℕ) (mu : Fin K → ℝ) (τ : ℝ → Fin K → ℝ)
    (Ψ : Path K → Path K → Path K) (Q A : Ω → Path K) : Ω → ℝ → ℝ :=
  fun ω t => (⨆ k, Rhat n mu τ Ψ Q A ω t k) - (∑ k, Rhat n mu τ Ψ Q A ω t k) / K

/-- The random time `θⁿ = inf{t ≥ 0 : Δ̂ⁿ(t) ≥ rₙ}` (47), in `[0, ∞]`, with `inf ∅ = ∞`. -/
noncomputable def theta {Ω : Type*} (r : ℝ) (D : Ω → ℝ → ℝ) : Ω → ℝ≥0∞ :=
  fun ω => ⨅ (t : ℝ) (_ : 0 ≤ t ∧ r ≤ D ω t), ENNReal.ofReal t

/-- The path `Z` stopped at `θ ∈ [0, ∞]`, `Z(· ∧ θ)`: equal to `Z(t)` for `t ≤ θ` and to `Z(θ)`
for `t > θ` (never stopped when `θ = ∞`). -/
noncomputable def stopAt {m : ℕ} (θ : ℝ≥0∞) (Z : ℝ → Fin m → ℝ) : ℝ → Fin m → ℝ :=
  fun t => if ENNReal.ofReal t ≤ θ then Z t else Z θ.toReal

/-- The joint `4K`-dimensional scaled process `(Âⁿ, Q̂ⁿ, L̂ⁿ, M̂ⁿ)` of the `n`-th network
(Lemmas 5.2–5.3, pp. 18, 20). -/
noncomputable def quad {Ω : Type*} {K : ℕ} (n : ℕ) (mu : Fin K → ℝ)
    (Ψ : Path K → Path K → Path K) (Q A : Ω → Path K) : Ω → ℝ → Fin (K + K + K + K) → ℝ :=
  fun ω t => Fin.append (Fin.append (Fin.append (Ahat n mu A ω t) (Qhat n Q ω t))
    (Lhat n mu Q ω t)) (Mhat n Ψ Q A ω t)

end JSEQDelay.Diffusion


