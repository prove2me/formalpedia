-- Prove2me | Definitions.Def_UninformedMG_vdagger
-- name    : UninformedMG_vdagger
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:56.380561+00:00
-- url     : https://prove2.me/theorems/8c9c10a0-b365-4964-b12c-d8724d80750d
-- title:
--   The rounded empirical value $v^\dagger$
-- statement:
--   Fix opponent policies $\nu^1,\dots,\nu^K$ and a learner policy $\mu^{\mathrm{emp}}$. The **rounded empirical value** is $v^\dagger_{H+1}=0$, $v^\dagger_1(s)=0$ for $s\in S_1$, and, for $h=H,\dots,2$ and $s\in S_h$, $v^\dagger_h(s)$ is the smallest multiple of $1/(HK)$ no smaller than
--   $$\max_{j\in\{1,\dots,K\}}\sum_{a,b}\mu^{\mathrm{emp}}_h(a\mid s)\nu^j_h(b\mid s)\Big[\frac{\ell_h(s,a,b)}H+P_hv^\dagger_{h+1}(s,a,b)\Big].$$
--
--   With $\mu^{\mathrm{emp}}$ attaining the minimum in (1), $v^\dagger$ is the grid candidate against which the proof of Theorem 2.1 compares the algorithm.
--
--   **Formalization Note** "The smallest multiple of $1/(HK)$ no smaller than $m$" is $\lceil HKm\rceil/(HK)$. Lean layers are 0-based.
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), proof of Theorem 2.1, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_UninformedMG_enr

namespace UninformedMG

variable {H : ℕ}

/-- The normalized one-step expression `∑_{a,b} x(a) y(b) [ℓ_h(s,a,b)/H + P_h f(s,a,b)]` (proof of
Theorem 2.1, p.25). -/
noncomputable def normStage (G : Game H) (h : Fin H) (x : G.Act h → ℝ) (y : G.Opp h → ℝ)
    (f : G.St h.succ → ℝ) (s : G.St h.castSucc) : ℝ :=
  ∑ a, ∑ b, x a * y b * (G.loss h s a b / (H : ℝ) + PV G h f s a b)

/-- **The rounded empirical value `v†`** (proof of Theorem 2.1, p.25 = PDF p.27). For opponent
policies `ν^1, …, ν^K` and a learner policy `μ^emp`: `v†_{H+1} = 0`, `v†_1(s) = 0` for `s ∈ S_1`,
and for `h = H, …, 2` and `s ∈ S_h`, `v†_h(s)` is the smallest multiple of `1/(HK)` no smaller
than `max_{j ∈ {1,…,K}} ∑_{a,b} μ^emp_h(a|s) ν^j_h(b|s) [ℓ_h(s,a,b)/H + P_h v†_{h+1}(s,a,b)]`.

**Formalization Note.** Lean layer `h` is paper step `h + 1`, so layer `0` is forced to `0` and
the terminal layer `H` is `0`. "The smallest multiple of `1/(HK)` no smaller than `m`" is
`⌈HK·m⌉/(HK)` (`Int.ceil`). The maximum over `j` is the real `⨆` over `Fin K`, a maximum for
`K ≥ 1`. -/
noncomputable def vdagger (G : Game H) {K : ℕ} (ν : Fin K → OPolicy G) (μe : LPolicy G) :
    (h : Fin (H + 1)) → G.St h → ℝ :=
  Fin.reverseInduction (motive := fun h => G.St h → ℝ) (fun _ => 0)
    (fun i f s => if i.val = 0 then 0 else
      (⌈(H : ℝ) * K * ⨆ j : Fin K, normStage G i (μe i s) (ν j i s) f s⌉ : ℝ) / ((H : ℝ) * K))

end UninformedMG


