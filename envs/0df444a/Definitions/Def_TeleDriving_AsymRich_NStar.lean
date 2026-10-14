-- Prove2me | Definitions.Def_TeleDriving_AsymRich_NStar
-- name    : TeleDriving_AsymRich_NStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:02.527114+00:00
-- url     : https://prove2.me/theorems/8a4c4a55-ed66-4457-88be-f57a83ef5976
-- title:
--   Theorem 2.C, p. 22 — the minimal number of drivers n*_λ within ϵ of the full service level
-- statement:
--   Fix a service rate $\mu$, a demand rate $\lambda$, a tolerance $\epsilon$ and a fleet of $m$ vehicles. The number of drivers that comes within $\epsilon$ of the service level of a system with one driver per vehicle is
--
--   $$n^* = \min\{\, n \in \{1,\dots,m\} : SL(m,m) - SL(m,n) < \epsilon \,\}.$$
--
--   In Theorem 2.C of Benjaafar, Wang and Yang this is applied with $m = m_\lambda = \lfloor\alpha\lambda s\rfloor$ and the rate (4), giving $n^*_\lambda$; the theorem compares $n^*_\lambda$ to the fleet size $m_\lambda$.
--
--   **Formalization Note** The paper writes $\min\{n : SL(m_\lambda,m_\lambda) - SL(m_\lambda,n) < \epsilon\}$ and leaves the range of $n$ implicit; here $n$ ranges over $\{1,\dots,m\}$, where $SL(m,n)$ is defined. For $\epsilon > 0$ and $m \ge 1$ the set contains $n = m$, so the minimum exists; Lean's value $0$ on the empty set occurs only when $m = 0$ or $\epsilon \le 0$.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), p. 22, Theorem 2.C (definition of n*_λ)

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AsymRich

/-- n*_λ = min{n : SL(m, m) − SL(m, n) < ε}, Theorem 2.C, p. 22, with n ranging over {1, …, m}
(the set contains n = m when m ≥ 1; sInf ∅ = 0 is never used). -/
noncomputable def nStar (mu : ℕ → ℝ → ℝ) (lam eps : ℝ) (m : ℕ) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ n ≤ m ∧ TeleDriving.ScarceFleet.SL mu lam m m - TeleDriving.ScarceFleet.SL mu lam m n < eps}

end TeleDriving.AsymRich


