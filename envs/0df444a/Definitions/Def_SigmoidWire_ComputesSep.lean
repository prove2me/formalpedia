-- Prove2me | Definitions.Def_SigmoidWire_ComputesSep
-- name    : SigmoidWire_ComputesSep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:06:12.008961+00:00
-- url     : https://prove2.me/theorems/c77fd9f6-2774-470f-8748-af82cac9b4e3
-- title:
--   Computing $f$ with $\varepsilon$-separation (Definition 3.1)
-- statement:
--   A $\sigma$-circuit $C$ computes $f:\{0,1\}^n\to\{0,1\}$ with **$\varepsilon$-separation** if there is a threshold $\theta\in[0,1]$ such that for every $x\in\{0,1\}^n$,
--
--   $$
--   f(x)=0\implies C(x)\le\theta,\qquad f(x)=1\implies C(x)>\theta+\varepsilon.
--   $$
--
--   Separation is the robustness measure of the paper. "Noticeable" separation is $\Omega(n^{-k})$ for some $k\ge1$, and separation $0$ is the no-separation regime.
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Definition 3.1, pp.14–15

import Mathlib
import Definitions.Def_SigmoidWire_Circuit

namespace SigmoidWire

/-- **Computing `f` with `ε`-separation** (Definition 3.1).

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Definition 3.1, pp.14–15
(PDF pp.16–17): a σ-circuit `C` computes `f : {0,1}^n → {0,1}` with `ε`-separation if there exists
`θ ∈ [0, 1]` such that for every `x ∈ {0,1}^n`, `f(x) = 0 ⟹ C(x) ≤ θ` and
`f(x) = 1 ⟹ C(x) > θ + ε`.

**Formalization Note.** Boolean values are `Bool` (`false` for `0`, `true` for `1`); `C(x)` is
`C.eval σ x`. -/
def ComputesSep {n : ℕ} (σ : ℝ → ℝ) (C : Circuit n) (f : (Fin n → Bool) → Bool) (ε : ℝ) : Prop :=
  ∃ θ ∈ Set.Icc (0 : ℝ) 1, ∀ x : Fin n → Bool,
    (f x = false → C.eval σ x ≤ θ) ∧ (f x = true → θ + ε < C.eval σ x)

end SigmoidWire


