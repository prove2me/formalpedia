-- Prove2me | Definitions.Def_TeschlODE_Horseshoe_horseshoeSet
-- name    : TeschlODE_Horseshoe_horseshoeSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T05:54:32.12974+00:00
-- url     : https://prove2.me/theorems/4406e765-7fa2-49e2-a3ef-45fc09aaff67
-- title:
--   The invariant set $\Lambda = \Lambda(T_{1/\lambda}) \times \Lambda(T_\mu)$ of the horseshoe (13.8)
-- statement:
--   The invariant set of the Smale horseshoe is
--   $$\Lambda = \Lambda_- \cap \Lambda_+ = \Lambda(T_{1/\lambda}) \times \Lambda(T_\mu) \subseteq [0,1]^2,$$
--   where $\Lambda(T_\nu)$ is the set of points whose orbit under the tent map $T_\nu$ stays in $[0,1]$. The book derives it as the set of points of $D = [0,1]^2$ that stay in $D$ under all forward iterations, $\Lambda_+ = [0,1] \times \Lambda(T_\mu)$ (13.4), and all backward iterations, $\Lambda_- = \Lambda(T_{1/\lambda}) \times [0,1]$ (13.7).
--
--   **Formalization Note.** Defined by the closed formula (13.8), which does not depend on how $F$ is extended off $J_0 \cup J_1$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 332, §13.1, Eq. (13.8)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentRepellor

namespace TeschlODE.Horseshoe

/-- Teschl, §13.1, p. 332, (13.8): the invariant set of the Smale horseshoe,
`Λ = Λ₋ ∩ Λ₊ = Λ(T_{1/λ}) × Λ(T_µ)`, where `Λ(T_µ)` is the set (11.18) of points whose orbit under
the tent map `T_µ` stays in `[0, 1]`. -/
def horseshoeSet (lam μ : ℝ) : Set (ℝ × ℝ) :=
  TeschlODE.Shared.tentRepellor (1 / lam) ×ˢ TeschlODE.Shared.tentRepellor μ

end TeschlODE.Horseshoe


