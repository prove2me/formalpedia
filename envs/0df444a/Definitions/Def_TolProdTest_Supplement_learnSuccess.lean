-- Prove2me | Definitions.Def_TolProdTest_Supplement_learnSuccess
-- name    : TolProdTest_Supplement_learnSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:08:16.08639+00:00
-- url     : https://prove2.me/theorems/6625eda9-777d-400c-9b8b-8038a4978e60
-- title:
--   Success probability of a product-state learner
-- statement:
--   For a density operator $\rho$ on $(\mathbb C^d)^{\otimes n}$ and a product vector $|u\rangle=|u_1\rangle\otimes\cdots\otimes|u_n\rangle$, write $\langle u|\rho|u\rangle$ for the fidelity (the real quadratic form maximized in $F_{\mathrm{prod}}$).
--
--   A learner is a circuit on $N$ encoded copies of $\rho$ and $m$ ancillas together with an output format $(p,o)$ for the fixed decoder. Its **success probability at accuracy $\varepsilon$** is the probability, over the measurement outcome $y$ of all wires when the circuit runs on $\rho^{\otimes N}$, that the decoded product state $|\hat u\rangle$ satisfies
--
--   $$
--   \langle\hat u|\rho|\hat u\rangle\ \ge\ F_{\mathrm{prod}}(\rho)-\varepsilon .
--   $$
--
--   Theorems 4.1 and 4.2 require this probability to be at least $1-\delta$.
--
--   **Formalization Note** The event is decided classically; it is a property of the outcome, not a step of the algorithm.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Problem 1.2, p.2; Theorem 4.1, eq. (80), p.19; Theorem 4.2, eq. (84), p.20

import Mathlib
import Definitions.Def_TolProdTest_fprod
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_TolProdTest_Supplement_outcomeProbMixed
import Definitions.Def_TolProdTest_Supplement_decodeProd

set_option autoImplicit false

open Matrix

namespace TolProdTest.Supplement

/-- The fidelity `⟨u|ρ|u⟩` of an operator `ρ` on `n` qudits with the product vector `|u⟩ = |u_1⟩ ⊗ ⋯ ⊗ |u_n⟩`:
the real part of the quadratic form `Σ_{x,y} conj(u(x)) ρ_{xy} u(y)`, the same expression maximized in the
published `TolProdTest.fprod`. -/
noncomputable def prodFidelity {n d : ℕ} (ρ : Matrix (Config n d) (Config n d) ℂ) (u : Fin n → Fin d → ℂ) : ℝ :=
  (star (prodVec u) ⬝ᵥ (ρ *ᵥ prodVec u)).re

/-- **Success probability of a product-state learner** (Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Problem 1.2, p.2; Theorem 4.1, eq. (80), p.19;
Theorem 4.2, eq. (84), p.20).

The learner runs `gates` on `ρ^{⊗N}` (encoded as in `outcomeProbMixed`, with `m` ancillas in `|0⟩`), measures
every wire, and outputs the pure product state `|û⟩ = prodVec (decodeProd p o y)` decoded from the outcome `y`.
The value is the probability that `⟨û|ρ|û⟩ ≥ F_prod(ρ) − ε`.

**Formalization Note** The event is decided classically (`Classical.propDecidable`); it is a property of the
outcome, not a computation of the algorithm. -/
noncomputable def learnSuccess {N n d m : ℕ} (ρ : Matrix (Config n d) (Config n d) ℂ)
    (gates : List (ShiShallow.Instr (N * n * qd d + m))) (p : ℕ)
    (o : Fin n × Fin d × Bool × Fin (p + 1) ↪ Fin (N * n * qd d + m)) (ε : ℝ) : ℝ :=
  haveI := Classical.decPred
    (fun y : ShiShallow.Bits (N * n * qd d + m) => fprod ρ - ε ≤ prodFidelity ρ (decodeProd p o y))
  outcomeProbMixed (ShadowTomography.UpperBound.tensorPow ρ N) gates
    (fun y => fprod ρ - ε ≤ prodFidelity ρ (decodeProd p o y))

end TolProdTest.Supplement


