-- Prove2me | Definitions.Def_QuantumLTF_Membership_ltf
-- name    : QuantumLTF_Membership_ltf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:35:00.724302+00:00
-- url     : https://prove2.me/theorems/2c499ba0-4fd3-4ae3-93d8-328e86a0f1ea
-- title:
--   Linear threshold function $f_{w,\theta}$
-- statement:
--   For $w\in\mathbb R^n$ and $\theta\in\mathbb R$, the linear threshold function (LTF) with normal $w$ and threshold $\theta$ is
--   $$f_{w,\theta}(x)=\mathrm{sign}(\langle w,x\rangle-\theta),\qquad x\in\mathbb R^n,$$
--   and $f_w:=f_{w,0}$. It is the concept class of the mission.
--
--   **Formalization Note** The definition takes any $w$. The paper's $w\in\mathbb S^{n-1}$ is a hypothesis $\|w\|=1$ on the target wherever it is meant. An output hypothesis need not be normalized.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §2.1, unnumbered, p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_sgn

namespace QuantumLTF.Membership

/-- **Linear threshold function.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §2.1, unnumbered, p. 15 (PDF p. 16):
`f_{w,θ}(x) := sign(⟨w, x⟩ − θ)`; `f_w := f_{w,0}` is `ltf w 0`.

**Formalization Note.** Defined for every `w`. The source's `w ∈ S^{n−1}` is the hypothesis `‖w‖ = 1`
wherever the target is meant; an output hypothesis need not be normalized (Reading 5 of the goal). -/
noncomputable def ltf {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℤ :=
  sgn (inner ℝ w x - θ)

end QuantumLTF.Membership


