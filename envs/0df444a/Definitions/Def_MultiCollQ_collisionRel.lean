-- Prove2me | Definitions.Def_MultiCollQ_collisionRel
-- name    : MultiCollQ_collisionRel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:53.310196+00:00
-- url     : https://prove2.me/theorems/7c4585d3-275a-42a1-bad1-cafb68ad3985
-- title:
--   Finding $\ell$ $r$-collisions in distinct equality classes, and the average success probability
-- statement:
--   Fix $r,\ell\ge1$. An output is a list of $\ell$ groups of $r$ inputs, $g:[\ell]\times[r]\to[N]$. It **finds $\ell$ $r$-collisions of $f$ in distinct equality classes** when
--
--   1. the $r$ inputs of each group are distinct;
--   2. each group has a common function value: $f(g(i,a))=f(g(i,a'))$;
--   3. different groups have different common values: $f(g(i,a))\ne f(g(i',a'))$ for $i\ne i'$.
--
--   Thus the groups lie in distinct equality classes.
--
--   For a phase-query algorithm $A$ with output map $\mathrm{out}$ and a finite family $\Omega$ of functions, the **average success probability** under the uniform distribution on $\Omega$ is
--
--   $$
--   p=\frac{1}{|\Omega|}\sum_{f\in\Omega}\ \Pr\bigl[\mathrm{out}\text{ of the final measurement lies in } R(f)\bigr],
--   $$
--
--   the case $D$ uniform of display (2.3). The algorithm is $U_TO_fU_{T-1}\cdots U_1O_fU_0|\varphi_0\rangle$ with the phase oracle $O_f|x,c,z\rangle=\omega_q^{c f(x)}|x,c,z\rangle$, $\omega_q=e^{2\pi i/q}$ (2.1), followed by a measurement.
--
--   **Formalization Note** Outputs are `Fin ℓ → Fin r → Fin N`. Algorithms are the published `QAlgorithms.QueryAlg` (start state and unitaries independent of $f$, any finite workspace), run with `SelectiveDPT.phaseOracle`; the measurement is a computational-basis measurement of the whole register followed by $\mathrm{out}$ (`SelectiveDPT.successProb`). For $\Omega=\emptyset$ the average is $0$.
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), §2.4, p.14 (the task); §2.1, (2.1), p.9 and (2.3), p.10

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_SelectiveDPT_phaseOracle
import Definitions.Def_SelectiveDPT_Qrel

namespace MultiCollQ

open QAlgorithms

/-- The relation "`g` finds `ℓ` `r`-collisions of `f` in distinct equality classes" (Peng, Hou,
Dong, manuscript (Oct. 2026), §2.4, p.14: "outputting `ℓ` groups of `r` distinct inputs such that
each group has a common function value and different groups have different common values").

**Formalization Note.** An output is `g : Fin ℓ → Fin r → Fin N`, the `ℓ` groups of `r` inputs.
The three conjuncts are: the inputs of a group are distinct; a group has a common value; inputs of
different groups have different values. -/
def collisionRel {N q : ℕ} (r ℓ : ℕ) (f : Fin N → ZMod q) (g : Fin ℓ → Fin r → Fin N) : Prop :=
  (∀ i, Function.Injective (g i)) ∧ (∀ i a a', f (g i a) = f (g i a')) ∧
    ∀ i i', i ≠ i' → ∀ a a', f (g i a) ≠ f (g i' a')

/-- The average success probability `p = Σ_{f ∈ Ω} D(f) Σ_{ρ : (f,ρ) ∈ R} ‖Π_ρ φ'_{T,f}‖²` of a
phase-query algorithm under the uniform distribution `D` on a finite family `Ω` of functions
(Peng, Hou, Dong, manuscript (Oct. 2026), (2.3), p.10).

**Formalization Note.** The algorithm is `QAlgorithms.QueryAlg` with query register
`Fin N × ZMod q` (input `x`, phase label `c`) and workspace `Fin b`, run with the phase oracle
`O_f|x, c⟩ = ω_q^{c f(x)}|x, c⟩` of (2.1) (`SelectiveDPT.phaseOracle`); the output projectors are a
computational-basis measurement of the whole register followed by the output map `out`
(`SelectiveDPT.successProb`). For `Ω = ∅` the value is `0`. -/
noncomputable def avgSuccess {N q b T : ℕ} [NeZero q] {Y : Type*} (Ω : Finset (Fin N → ZMod q))
    (A : QueryAlg (Fin N) (ZMod q) (Fin b) T) (out : (Fin N × ZMod q) × Fin b → Y)
    (R : (Fin N → ZMod q) → Y → Prop) : ℝ :=
  ((Ω.card : ℝ))⁻¹ * ∑ f ∈ Ω, SelectiveDPT.successProb A out R f

end MultiCollQ


