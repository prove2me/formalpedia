-- Prove2me | Definitions.Def_AgnosticTNS_Run_IsAccurate
-- name    : AgnosticTNS_Run_IsAccurate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:37:44.458229+00:00
-- url     : https://prove2.me/theorems/7666bb7a-a61c-4af5-af50-2448b6f1776e
-- title:
--   Every Sub-Tomography call of a run is accurate
-- statement:
--   For an input $\rho$, a run is **accurate** if at every compressing step $i$ the estimate satisfies $\|\sigma_i-\hat\sigma_i\|_1\le\gamma_i$, where $\sigma_i=\mathrm{tr}_{[n]\setminus M_i}(K_{<i}\rho K_{<i}^\dagger)$ (3.36), and the final estimate satisfies $\|\tau-\hat\tau\|_1\le\gamma_{\mathrm{fin}}$, where $\tau=\mathrm{tr}_{[n]\setminus R_L}(K_c\rho K_c^\dagger)$ (3.44). This is the hypothesis "every call to Sub-Tomography succeeds with its requested trace-norm accuracy" of Proposition 3.5.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Proposition 3.5, p.21; Eqs. (3.36)–(3.37), (3.44), p.21–22

import Mathlib
import Definitions.Def_AgnosticTNS_Run_Kupto
import Definitions.Def_AgnosticTNS_ptrace
import Definitions.Def_WildeQIT_traceNorm
open Matrix

namespace AgnosticTNS

/-- **Every Sub-Tomography call of a run succeeds with its requested accuracy**, Proposition 3.5,
p.21 (accuracies from §3.2 and Algorithm 1 lines 10, 19, 20) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): at every compressing step `i`,
`‖σ_i − σ̂_i‖₁ ≤ γ_i` for the true subnormalised reduced state `σ_i = tr_{[n]∖M_i}(K_{<i} ρ K_{<i}†)`
(3.36), and `‖τ − τ̂‖₁ ≤ γ_fin` for `τ = tr_{[n]∖R_L}(K_c ρ K_c†)` (3.44).

**Formalization Note** `‖·‖₁` is the published `WildeQIT.traceNorm`. -/
def Run.IsAccurate {d n : ℕ} {Ls : LearningSequence n} (run : Run d n Ls) (p : Fin Ls.L → ℕ)
    (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (γ : Fin Ls.L → ℝ) (γfin : ℝ) : Prop :=
  (∀ i, p i < (Mset Ls run.R i).card →
    WildeQIT.traceNorm (ptrace (Mset Ls run.R i)
      (run.Kupto p i.val * ρ * (run.Kupto p i.val)ᴴ) - run.σhat i) ≤ γ i) ∧
  WildeQIT.traceNorm (ptrace (run.R Ls.root)
      (run.Kupto p Ls.L * ρ * (run.Kupto p Ls.L)ᴴ) - run.τhat) ≤ γfin

end AgnosticTNS


