-- Prove2me | Definitions.Def_LSWCuttingPlane_ChasingZero_Setting
-- name    : LSWCuttingPlane_ChasingZero_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:59.230568+00:00
-- url     : https://prove2.me/theorems/b005c0ee-7286-4f36-a43c-8182aa3a8213
-- title:
--   §7.2, Algorithm 4 and proof of Theorem 34, pp. 42–43 — the chasing 0⃗ trajectory under argmax |yᵢ|, the potential Φ and η
-- statement:
--   This file fixes the objects of the **stochastic chasing $\vec 0$ game** of Lee, Sidford and Wong (§7.2, Algorithm 4) when the player uses the largest-coordinate strategy of Theorem 34, together with the two quantities that appear in the proof of that theorem.
--
--   Coordinates are indexed by $[m]$, and vectors are $\vec x\in\mathbb R^m$.
--
--   1. **Largest-coordinate strategy.** For an observation $\vec y\in\mathbb R^m$ (with $m\ge 1$), $\operatorname{argmax}_i |y_i|$ is the least index $i$ among those at which $|y_i|$ is maximal.
--   2. **Trajectory.** Given the adversary's steps $\vec\Delta^{(1)},\vec\Delta^{(2)},\dots$ and the observations $\vec y^{(1)},\vec y^{(2)},\dots$ (each a function of the outcome $\omega$), the point of the game is defined by $\vec x^{(1)}=\vec 0$ and, with $i^{(k)}=\operatorname{argmax}_i |y^{(k)}_i|$,
--   $$x^{(k+1)}_{i^{(k)}}=0,\qquad x^{(k+1)}_j=x^{(k)}_j+\Delta^{(k)}_j\quad (j\ne i^{(k)}).$$
--   3. **Potential.** For $\alpha\in\mathbb R$,
--   $$\Phi(\vec x)=\sum_{i} e^{\alpha x_i}+\sum_i e^{-\alpha x_i}.$$
--   4. **The quantity $\eta$.** $\eta=\max\big(\max_i e^{\alpha x_i},\ \max_i e^{-\alpha x_i}\big)$.
--
--   These are the common vocabulary of Theorem 34 and the milestones of its proof.
--
--   **Formalization Note** Coordinates are `Fin m`, 0-based, so the paper's coordinate $i$ is Lean's `i - 1`. The paper's argmax has no tie rule; ties are broken by the least index (Theorem 34 is claimed for any choice). Rounds are shifted by one: `traj Δ y k` is the paper's $\vec x^{(k+1)}$, and `Δ k`, `y k` are $\vec\Delta^{(k+1)}$, $\vec y^{(k+1)}$, so `traj Δ y 0 = 0` is $\vec x^{(1)}=\vec 0$. $m\ge1$ is required (`NeZero m`) so that the argmax and the maxima exist.
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2, pp. 42–43, §7.2, Algorithm 4, Theorem 34 and its proof (definitions of Φ and η)

import Mathlib

namespace LSWCuttingPlane.ChasingZero

/-!
Lee–Sidford–Wong, arXiv:1508.04874v2, §7.2, pp. 42–44: the stochastic chasing 0⃗ game
(Algorithm 4), the largest-coordinate strategy of Theorem 34, and the potential `Φ` and the
quantity `η` of its proof. Coordinates are `Fin m` (0-based; the paper's `[m] = {1, …, m}`).
-/

variable {m : ℕ}

/-- The set of coordinates `i` at which `|v i|` is maximal. -/
noncomputable def maxAbsCoords (v : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∀ j, |v j| ≤ |v i|)

theorem maxAbsCoords_nonempty [NeZero m] (v : Fin m → ℝ) : (maxAbsCoords v).Nonempty := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|) Finset.univ_nonempty
  exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => hi j (Finset.mem_univ _)⟩⟩

/-- The player's strategy of Theorem 34, `i = argmaxᵢ |vᵢ|`, with ties broken by the least
index of `Fin m`. -/
noncomputable def argmaxAbs [NeZero m] (v : Fin m → ℝ) : Fin m :=
  (maxAbsCoords v).min' (maxAbsCoords_nonempty v)

/-- The trajectory of the stochastic chasing 0⃗ game (Algorithm 4) when the player uses
`argmaxAbs`. `Δ k ω` is the adversary's step `Δ⃗^(k+1)` and `y k ω` the observation `y⃗^(k+1)`.
`traj Δ y k ω` is the paper's `x⃗^(k+1)`: it starts at `x⃗^(1) = 0⃗`, and
`x⃗^(k+1) = x⃗^(k) + Δ⃗^(k)` except that the coordinate `i^(k) = argmaxᵢ |yᵢ^(k)|` is set to `0`. -/
noncomputable def traj {Ω : Type*} [NeZero m] (Δ y : ℕ → Ω → Fin m → ℝ) :
    ℕ → Ω → Fin m → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun ω => Function.update (traj Δ y k ω + Δ k ω) (argmaxAbs (y k ω)) 0

/-- The potential of the proof of Theorem 34: `Φ(x) = ∑ᵢ e^{α xᵢ} + ∑ᵢ e^{−α xᵢ}`. -/
noncomputable def Phi (α : ℝ) (x : Fin m → ℝ) : ℝ :=
  ∑ i, Real.exp (α * x i) + ∑ i, Real.exp (-α * x i)

/-- `η = max (maxᵢ e^{α xᵢ}, maxᵢ e^{−α xᵢ})` from the proof of Theorem 34. -/
noncomputable def eta [NeZero m] (α : ℝ) (x : Fin m → ℝ) : ℝ :=
  max (Finset.univ.sup' Finset.univ_nonempty (fun i => Real.exp (α * x i)))
    (Finset.univ.sup' Finset.univ_nonempty (fun i => Real.exp (-α * x i)))

end LSWCuttingPlane.ChasingZero


