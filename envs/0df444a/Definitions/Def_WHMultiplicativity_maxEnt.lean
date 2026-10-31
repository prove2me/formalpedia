-- Prove2me | Definitions.Def_WHMultiplicativity_maxEnt
-- name    : WHMultiplicativity_maxEnt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:22:51.581951+00:00
-- url     : https://prove2.me/theorems/3aaede9e-bac5-4b0b-aba6-87337bed6adc
-- title:
--   Maximally entangled vector $\Phi_m = d^{-1/2}\sum_\alpha |\alpha\alpha\rangle$
-- statement:
--   On $\mathbb C^d\otimes\mathbb C^d$ with the fixed basis $|\alpha\rangle\otimes|\beta\rangle$, the **maximally entangled vector** is
--
--   $$
--   \Phi_m = \sum_{\alpha=1}^{d} \frac{1}{\sqrt d}\, |\alpha\alpha\rangle ,
--   $$
--
--   the Schmidt diagonal vector $\Phi = \sum_\alpha c_\alpha|\alpha\alpha\rangle$ with all $c_\alpha = 1/\sqrt d$. It is a unit vector, and both of its reduced density operators are $\tfrac1d\mathbb 1$. Werner and Holevo insert it, for $d = 3$, into $S\otimes S$ to exhibit the violation of multiplicativity.
--
--   **Formalization Note** A basis vector $|\alpha\rangle\otimes|\beta\rangle$ is indexed by a function $y : \{0,1\} \to \{0,\dots,d-1\}$ with $y(0) = \alpha$, $y(1) = \beta$, which is the index type of the tensor product of superoperators used in the mission. The coordinate of $\Phi_m$ at $y$ is $1/\sqrt d$ if $y(0) = y(1)$ and $0$ otherwise.
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, §II, p.2 (after eq. (10)): all c_α = 1/√d

import Mathlib

namespace WHMultiplicativity

/-- Werner and Holevo, arXiv:quant-ph/0203003v1, §II, p.2 (after eq. (10)): the maximally
entangled vector `Φ_m = Σ_α c_α |αα⟩` with all `c_α = 1/√d`, on `ℂ^d ⊗ ℂ^d`.

**Formalization Note.** A basis vector `|α⟩ ⊗ |β⟩` of `ℂ^d ⊗ ℂ^d` is indexed by the function
`y : Fin 2 → Fin d` with `y 0 = α`, `y 1 = β` (the index type of `QAlgorithms.piSuperop` with two
factors); `|α⟩` is the `α`-th standard basis vector, the paper's "fixed basis". The coordinate of
`Φ_m` at `y` is `1/√d` if `y 0 = y 1` and `0` otherwise. The paper uses `d = 3`. -/
noncomputable def maxEnt (d : ℕ) : (Fin 2 → Fin d) → ℂ :=
  fun y => if y 0 = y 1 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0

end WHMultiplicativity


