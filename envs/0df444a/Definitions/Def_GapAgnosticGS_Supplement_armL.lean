-- Prove2me | Definitions.Def_GapAgnosticGS_Supplement_armL
-- name    : GapAgnosticGS_Supplement_armL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:29:12.974827+00:00
-- url     : https://prove2.me/theorems/e1a1657a-d621-42ef-ba56-25d940ca3644
-- title:
--   Guided-state complexity $L(h,\{p_j\},|\psi_I\rangle)$ (Definition 4.2)
-- statement:
--   Let $E$ be a hidden-basis environment with hidden orthonormal basis $\{|\phi_j\rangle\}_{j=1}^n$, arm rewards $p_j$ and best reward $p_\star=\max_j p_j$, and let $|\psi_I\rangle=\sum_j c_j|\phi_j\rangle$ be an initial selector state, $c_j=\langle\phi_j|\psi_I\rangle$. For a resolution $h>0$ the **guided-state complexity** is
--
--   $$
--   L(h,\{p_j\},|\psi_I\rangle)=\sum_{j}\frac{|c_j|^2}{\max\{p_\star-p_j,\;h\}^2}.
--   $$
--
--   It weights each arm by its initial weight $|c_j|^2$ and the inverse square of its reward gap, capped at the resolution $h$. Since $\sum_j|c_j|^2=1$, $L\le h^{-2}$; if the best arms carry weight at least $\gamma^2$, then $L\ge\gamma^2/h^2$. It is the instance-dependent quantity in the query bounds of Theorems 4.3 and 4.4.
--
--   **Formalization Note** $c_j$ is the inner product with the environment's hidden basis vector `Env.φ j`; the definition is used only with $h>0$.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Definition 4.2, Eq. (8), p.18 (PDF p.19); (7), p.17 (PDF p.18)

import Definitions.Def_GapAgnosticGS_pStar

namespace GapAgnosticGS.Supplement

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Definition 4.2, p.18 (PDF p.19): "Given a HidQMAB instance, h > 0, and an initial state
|ψ_I⟩ as in (7), define L(h, {p_j}, |ψ_I⟩) := Σ_j |c_j|² / max{p⋆ − p_j, h}²", with
`|ψ_I⟩ = Σ_j c_j |ϕ_j⟩` ((7), p.17, PDF p.18). The **guided-state complexity** `L(h, {p_j}, |ψ⟩)`,
`c_j = ⟨ϕ_j|ψ⟩` in the environment's hidden basis.

**Formalization Note.** Used only with `h > 0`, so no denominator vanishes. -/
noncomputable def armL {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A}
    {Prj : Matrix A A ℂ} (Env : HidEnv n A a₀ Prj) (h : ℝ) (ψ : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ∑ j, ‖inner ℂ (Env.φ j) ψ‖ ^ 2 / (max (pStar Env - reward Env j) h) ^ 2

end GapAgnosticGS.Supplement


