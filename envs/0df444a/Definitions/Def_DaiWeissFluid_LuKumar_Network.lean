-- Prove2me | Definitions.Def_DaiWeissFluid_LuKumar_Network
-- name    : DaiWeissFluid_LuKumar_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:45:33.019984+00:00
-- url     : https://prove2.me/theorems/18f0b4e1-ae8a-4d0b-b905-b7024d0ee992
-- title:
--   The Lu–Kumar four-class line and priority policy
-- statement:
--   The **Lu–Kumar line** has route $1\to2\to3\to4$ and two stations: classes $1,4$ are served at station $1$, while classes $2,3$ are served at station $2$. Thus
--   $$\rho_1=m_1+m_4,\qquad \rho_2=m_2+m_3.$$
--   The named priority discipline gives class $4$ priority over class $1$ at station $1$, and class $2$ priority over class $3$ at station $2$. Its rank permutation is $(4,2,3,1)$ when written in the paper’s class labels. The cumulative content $Q_k^+(t)=\sum_{l=1}^{k}Q_l(t)$ and the two components $G_1=\theta_1Q_1^++(1-\theta_1)Q_4^+$, $G_2=\theta_2Q_2^++(1-\theta_2)Q_3^+$ are defined for later statements.
--
--   This module fixes the network and the functions used in both parts of Theorem 5.1.
--
--   **Formalization Note** Classes and stations are numbered from zero in Lean: paper class $k$ is Lean index $k-1$. Paths are total real-time functions, with the fluid equations imposed for $t\ge0$. The paper’s “increases only when empty” conditions (1.13) and (4.4) are represented by constancy on intervals of positive content.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 125, Figure 2 and (5.1); pp. 127–128, (5.3)–(5.4)

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel

namespace DaiWeissFluid.LuKumar

/-- Figure 2: the four-class line visits stations 1, 2, 2, 1. -/
def luKumar (m : Fin 4 → ℝ) : ReentrantLine 2 4 := ⟨![0, 1, 1, 0], m⟩

/-- The Lu–Kumar priority order, with classes 4 and 2 highest at their respective stations. -/
def piLK : Equiv.Perm (Fin 4) := Equiv.swap 0 3

/-- The cumulative class content `Q_k⁺(t)` of (2.2), using zero-based indices. -/
noncomputable def Qplus (Q : ℝ → Fin 4 → ℝ) (k : Fin 4) (t : ℝ) : ℝ :=
  ∑ l ∈ Finset.univ.filter (· ≤ k), Q t l

/-- The first Lyapunov component of (5.3). -/
noncomputable def G1 (θ : ℝ) (Q : ℝ → Fin 4 → ℝ) (t : ℝ) : ℝ :=
  θ * Qplus Q 0 t + (1 - θ) * Qplus Q 3 t

/-- The second Lyapunov component of (5.4). -/
noncomputable def G2 (θ : ℝ) (Q : ℝ → Fin 4 → ℝ) (t : ℝ) : ℝ :=
  θ * Qplus Q 1 t + (1 - θ) * Qplus Q 2 t

end DaiWeissFluid.LuKumar


