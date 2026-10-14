-- Prove2me | Definitions.Def_HighUncertHT_Game_Lindley
-- name    : HighUncertHT_Game_Lindley
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:33:32.865121+00:00
-- url     : https://prove2.me/theorems/73354e12-6cad-4652-a501-d999865e1d7f
-- title:
--   §7, pp. 31–32 — the process Wⁿ_k = W̃ⁿ_{k/n} driving the adversary's feedback control (61)
-- statement:
--   In §7 the paper sets $(\tilde W^n,\tilde R^n)=\Gamma(\hat X^n+\hat Y^n)$ (label 'tot' suppressed) and $\mathsf W^n_k=\tilde W^n_{k/n}$. At the epochs $k/n$, $\hat X^n+\hat Y^n=n^{-1/2}\sum_{j\le k}(J^{\mathrm{tot},n}_j-1)$, by the definitions of $X$, $Y$, $b^{\pi\ell n}$ and Assumption 2, and these processes are constant between epochs; so $\mathsf W^n$ is given by the **Lindley recursion**
--   $$
--   \mathsf W^n_0=0,\qquad \mathsf W^n_k=\max\big(\mathsf W^n_{k-1}+n^{-1/2}(J^{\mathrm{tot},n}_k-1),\,0\big),\quad k\ge1,
--   $$
--   a function of the job sizes only. It is the state fed to the measurable selectors in the adversary's control (61).
--
--   **Formalization Note** The recursion is defined on job-size sequences (index $0$ unused) and on histories $(J_1,\dots,J_m)$, the argument of a feedback map at step $m$.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, pp. 31–32, §7, definition of (W̃ⁿ, R̃ⁿ) = Γ(X̂ⁿ + Ŷⁿ) and Wⁿ_k = W̃ⁿ_{k/n}, (58)

import Mathlib

namespace HighUncertHT.Game

/-!
Atar, Castiel, Shadmi, arXiv:2204.05733v1, §7, pp. 31–32: the process `Wⁿ_k = W̃ⁿ_{k/n}`, where
`(W̃ⁿ, R̃ⁿ) = Γ(X̂ⁿ + Ŷⁿ)` (label `tot` suppressed). At the times `k/n`,
`X̂ⁿ + Ŷⁿ = n^{-1/2} Σ_{j ≤ k} (J^{tot,n}_j - 1)` (definitions (25) of `X`, `Y`, of `b^{πℓn}` and
Assumption 2, `Σ_ℓ 1/µ^ℓ = 1`; cf. (58)), and both processes are constant between these times, so
the Skorokhod map reduces to the Lindley recursion

  `Wⁿ_0 = 0`, `Wⁿ_k = max(Wⁿ_{k-1} + n^{-1/2}(J^{tot,n}_k - 1), 0)`,

which is what is defined, as a function of the job sizes only.
-/

variable {L : ℕ}

/-- The Lindley recursion for `Wⁿ_k` along a job-size sequence `J` (`J k ℓ` is the paper's
`J^{ℓn}_k` for `k ≥ 1`; `J 0` is not used). -/
noncomputable def lindley (n : ℕ) (J : ℕ → Fin L → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => max (lindley n J k + (Real.sqrt n)⁻¹ * (∑ ℓ, J (k + 1) ℓ - 1)) 0

/-- `Wⁿ_m` as a function of the history `x = (ω 0, Jⁿ₁, …, Jⁿ_m)` (the argument of an adversary
feedback map at step `m`): the history is extended by `0` beyond `m`, which `lindley` at `m` does
not read. -/
noncomputable def lindleyHist (n m : ℕ) (x : (i : Finset.Iic m) → (Fin L → ℝ)) : ℝ :=
  lindley n (fun k => if hk : k ≤ m then x ⟨k, Finset.mem_Iic.2 hk⟩ else 0) m

end HighUncertHT.Game


