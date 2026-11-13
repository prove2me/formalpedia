-- Prove2me | Definitions.Def_SigRoute_Qgamma
-- name    : SigRoute_Qgamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:39:56.457885+00:00
-- url     : https://prove2.me/theorems/7d7a0552-f4f6-40ec-a37c-4c0cd04a1ccc
-- title:
--   Fresh-coin profile $\mathcal Q_\gamma$, $\eta_X(\lambda)$ and $\varepsilon_{\mathrm{eff}}$
-- statement:
--   Let $\varepsilon_A,\varepsilon_B$ be the soundness errors of the two arms and $\gamma$ the forgery rate. Define
--
--   $$
--   \mathcal Q_\gamma=\bigl\{(q_A,q_B)\in[0,1]^2:\ q_A\le g\varepsilon_A,\ q_B\le(1-g)\varepsilon_B\ \text{for some } g\in[0,\gamma]\bigr\},
--   $$
--
--   and, for credits $u_A,u_B$ and $\lambda>0$,
--
--   $$
--   \eta_X(\lambda)=\varepsilon_X\bigl(e^{\lambda u_X}-1\bigr),\qquad \varepsilon_{\mathrm{eff}}=\varepsilon_B+\gamma(\varepsilon_A-\varepsilon_B)^+ ,
--   $$
--
--   with $z^+=\max\{z,0\}$.
--
--   These are the profile of Lemma 13 and the quantities in which Theorem 14's bound for fresh-coin arms is written.
--
--   **Formalization Note** The printed $\mathcal Q_\gamma$ has no lower bound on $q_A,q_B$; it is intersected with $[0,1]^2$ because Definition 12 requires a soundness profile to lie in $[0,1]^2$. The coefficients in $\Lambda$ are positive, so this does not change the supremum.
-- source:
--   Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Lemma 13, p.7; Theorem 14, p.7

import Mathlib
import Definitions.Def_SigRoute_Arm

namespace SigRoute

/-- The fresh-coin profile `Q_γ = {(q_A, q_B) : q_A ≤ g ε_A, q_B ≤ (1 − g) ε_B for some g ∈ [0, γ]}`
(Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Lemma 13, p.7), for soundness errors `ε : Arm → ℝ` and a forgery rate `γ`.

**Formalization Note** The set is intersected with `[0,1]²`: Definition 12 (p.7) requires a soundness
profile to be a subset of `[0,1]²`, and the printed set has no lower bound on `q_A, q_B`. This does not
change the supremum in Theorem 14, whose coefficients are positive. -/
def Qgamma (ε : Arm → ℝ) (γ : ℝ) : Set (ℝ × ℝ) :=
  {q | q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ∧
    ∃ g ∈ Set.Icc (0 : ℝ) γ, q.1 ≤ g * ε Arm.A ∧ q.2 ≤ (1 - g) * ε Arm.B}

/-- `η_X(λ) = ε_X (e^{λu_X} − 1)` (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Theorem 14, p.7). -/
noncomputable def eta (ε : Arm → ℝ) (u : Arm → ℝ) (lam : ℝ) (X : Arm) : ℝ :=
  ε X * (Real.exp (lam * u X) - 1)

/-- The effective soundness error `ε_eff = ε_B + γ (ε_A − ε_B)⁺` (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Lemma 13, p.7), with
`z⁺ = max{z, 0}` (§2, p.4). -/
def epsEff (ε : Arm → ℝ) (γ : ℝ) : ℝ :=
  ε Arm.B + γ * max (ε Arm.A - ε Arm.B) 0

end SigRoute


