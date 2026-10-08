-- Prove2me | Definitions.Def_DaiWeissFluid_ThreeBuffer_Line
-- name    : DaiWeissFluid_ThreeBuffer_Line
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T20:28:05.048386+00:00
-- url     : https://prove2.me/theorems/72eed6f4-a954-4ead-92f6-b833fa8454c1
-- title:
--   The three-buffer line 1→2→1 (Figure 1), $Q_k^+$ (2.2), and the Lyapunov components $G_1, G_2$ of Theorem 3.1
-- statement:
--   The **three-buffer two-station reentrant line** of Figure 1 has $I = 2$ stations and $K = 3$ classes with route $1 \to 2 \to 1$: classes $1$ and $3$ are served at station $1$, class $2$ at station $2$, with mean service times $m = (m_1, m_2, m_3)$. Its nominal workloads are $\rho_1 = m_1 + m_3$ and $\rho_2 = m_2$.
--
--   For any reentrant line, the cumulative fluid levels are (2.2)
--
--   $$
--   Q_k^+(t) = \sum_{l=1}^{k} Q_l(t), \qquad k = 1,\dots,K .
--   $$
--
--   For the three-buffer line, the proof of Theorem 3.1 uses the constant $\theta = m_1/(m_1+m_3)$ and the two linear Lyapunov components
--
--   $$
--   G_1(t) = \theta\, Q_1^+(t) + (1-\theta)\, Q_3^+(t), \qquad G_2(t) = Q_2^+(t).
--   $$
--
--   These are the ingredients of the piecewise-linear Lyapunov function $G = \max\{G_1, G_2\}$ that drives the stability proof.
--
--   **Formalization Note.** Indices are 0-based: `threeBuffer m` has station map `![0, 1, 0]` (classes `0, 2` at station `0`, class `1` at station `1`), and `m 0, m 1, m 2` are $m_1, m_2, m_3$. `lyap m Q 0` is $G_1$ and `lyap m Q 1` is $G_2$; `Qplus Q k t` sums `Q t l` over `l ≤ k`. Here θ is a constant of the paper's proof, not of the theorem.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 120, Figure 1, (2.2), (3.1); p. 121, proof of Theorem 3.1

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel

namespace DaiWeissFluid.ThreeBuffer

/-- The three-buffer two-station reentrant line of Figure 1 (p. 120): route `1 → 2 → 1`, i.e.
classes 1 and 3 at station 1 and class 2 at station 2. In 0-based indices: classes `0, 2` at
station `0`, class `1` at station `1`; `m` is the vector of mean service times `(m₁, m₂, m₃)`. -/
def threeBuffer (m : Fin 3 → ℝ) : ReentrantLine 2 3 := ⟨![0, 1, 0], m⟩

/-- `Q_k⁺(t) = ∑_{l ≤ k} Q_l(t)` (2.2), for any number `K` of classes (0-based). -/
noncomputable def Qplus {K : ℕ} (Q : ℝ → Fin K → ℝ) (k : Fin K) (t : ℝ) : ℝ :=
  ∑ l ∈ Finset.univ.filter (· ≤ k), Q t l

/-- The constant `θ = m₁ / (m₁ + m₃)` of the proof of Theorem 3.1 (p. 121). -/
noncomputable def theta (m : Fin 3 → ℝ) : ℝ := m 0 / (m 0 + m 2)

/-- The two linear Lyapunov components of the proof of Theorem 3.1 (p. 121), 0-based:
`lyap m Q 0 = G₁ = θ Q₁⁺ + (1 - θ) Q₃⁺` and `lyap m Q 1 = G₂ = Q₂⁺`. -/
noncomputable def lyap (m : Fin 3 → ℝ) (Q : ℝ → Fin 3 → ℝ) : Fin 2 → ℝ → ℝ :=
  ![fun t => theta m * Qplus Q 0 t + (1 - theta m) * Qplus Q 2 t, fun t => Qplus Q 1 t]

end DaiWeissFluid.ThreeBuffer


