-- Prove2me | Definitions.Def_QCopyMono_IsMonoTester
-- name    : QCopyMono_IsMonoTester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:48.919696+00:00
-- url     : https://prove2.me/theorems/9c5f4a96-88c5-439d-8705-6839fef0beb3
-- title:
--   Function states $|\psi_f\rangle$, distance from monotone, and monotonicity testers on $t$ copies
-- statement:
--   Identify $\{0,1\}^n$ with bit strings $x=(x_1,\dots,x_n)$, ordered coordinate-wise: $x\preceq y$ iff $x_i\le y_i$ for every $i\in[n]$. A Boolean function $f:\{0,1\}^n\to\{0,1\}$ is **monotone** if $f(x)\le f(y)$ whenever $x\preceq y$. The distance between two Boolean functions is
--   $$
--   \mathrm{dist}(f,g)=\Pr_{x\sim\mathrm{Unif}(\{0,1\}^n)}[f(x)\neq g(x)],
--   $$
--   and $f$ is **$\varepsilon$-far from monotone** if $\mathrm{dist}(f,g)\ge\varepsilon$ for every monotone $g$, i.e. $\mathrm{dist}(f,\mathrm{MON}_n)\ge\varepsilon$.
--
--   The **quantum function state** of $f$ is the $(n+1)$-qubit state
--   $$
--   |\psi_f\rangle=2^{-n/2}\sum_{x\in\{0,1\}^n}|x,f(x)\rangle ,
--   $$
--   and $|\psi_f\rangle^{\otimes t}$ is $t$ copies of it. A tester that receives $t$ copies and answers "monotone" or "far" is described by the operator $E$ of its "monotone" answer, an **effect** ($0\preceq E\preceq I$) on the $t$-copy register; it answers "monotone" with probability $\langle\psi_f^{\otimes t}|E|\psi_f^{\otimes t}\rangle$. The effect is a **monotonicity tester with parameters $(\varepsilon,\delta)$ on $t$ copies** if this probability is at least $1-\delta$ for every monotone $f$ and at most $\delta$ for every $f$ that is $\varepsilon$-far from monotone.
--
--   These objects state the goal (Theorem 1) and every tester milestone of the mission.
--
--   **Formalization Note** Bit strings are `QAlgorithms.Qubits n = Fin n → Bool` with `false` $=0$ and `true` $=1$; Mathlib's `Monotone` on `Qubits n → Bool` is the coordinate-wise order with $0<1$. One copy lives on `X n = Qubits n × Bool` (the last qubit holds $f(x)$) and $t$ copies on `Fin t → X n`, with the tensor-power amplitude the product of the one-copy amplitudes. Every measurement on $t$ copies followed by a yes/no decision induces such an effect; no gate or time bound is part of the model, matching the paper, which counts copies only.
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), §1, p.3 (dist, monotone, eq. (1)); §2, p.6 (t copies, arbitrary joint measurement); Theorem 1, pp.3–4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QCopyMono

open QAlgorithms Matrix
open scoped ComplexOrder

/-! # Quantum function states, distance from monotone, and monotonicity testers

P. Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), §1, p.3 (distance, monotone, state (1)) and §2,
p.6 (copy model).

**Formalization Note.**
* The input `x ∈ {0,1}ⁿ` is `QAlgorithms.Qubits n = Fin n → Bool`, with `false = 0` and
  `true = 1`. Mathlib's `Monotone` on `Qubits n → Bool` uses the coordinate-wise order of the
  pi type and the order `false < true` on `Bool`, which is the printed order `x ⪯ y`, `0 ≤ 1`.
* The register of one copy is `X n = Qubits n × Bool`: the `n` input qubits and the qubit
  holding the function value. The `t`-copy register is indexed by `Fin t → X n`, so the
  `t`-fold tensor power is the product of the `t` one-copy amplitudes.
* A tester that uses `t` copies and answers "monotone" or "far" is represented by the effect
  `E` (`0 ⪯ E ⪯ 1`) of its "accept" answer on the `t`-copy register: every joint measurement on
  `|ψ_f⟩^{⊗t}` followed by a yes/no decision induces such an effect, and every such effect is a
  two-outcome joint measurement. The paper counts copies only; no gate or time bound is part of
  the model.
* "ε-far" is `∀ g monotone, ε ≤ dist(f,g)`, which is `dist(f, MONₙ) ≥ ε` because `MONₙ` is a
  finite nonempty set (the minimum is attained). -/

/-- The register of one copy: `n` input qubits and the qubit of the function value. -/
abbrev X (n : ℕ) := Qubits n × Bool

/-- p.3: `dist(f, g) = Pr_{x∼Unif({0,1}ⁿ)}[f(x) ≠ g(x)]`. -/
noncomputable def relDist {n : ℕ} (f g : Qubits n → Bool) : ℝ :=
  ((Finset.univ.filter fun x => f x ≠ g x).card : ℝ) / 2 ^ n

/-- p.3: `f` is `ε`-far from monotone, `dist(f, MONₙ) ≥ ε`, written as `ε ≤ dist(f, g)` for
every monotone `g` (the minimum over the finite nonempty set `MONₙ`). -/
def IsFar {n : ℕ} (ε : ℝ) (f : Qubits n → Bool) : Prop :=
  ∀ g : Qubits n → Bool, Monotone g → ε ≤ relDist f g

/-- p.3, eq. (1): the quantum function state `|ψ_f⟩ = 2^{-n/2} ∑ₓ |x, f(x)⟩`, as its amplitude
vector on `X n`: `2^{-n/2}` at `(x, f x)` and `0` elsewhere. -/
noncomputable def fnState {n : ℕ} (f : Qubits n → Bool) : X n → ℂ :=
  fun z => if z.2 = f z.1 then (((Real.sqrt (2 ^ n))⁻¹ : ℝ) : ℂ) else 0

/-- p.6: the `t`-copy state `|ψ_f⟩^{⊗t}` on the index `Fin t → X n`, the product of the
one-copy amplitudes. For `t = 0` it is the scalar `1` on the one-point index. -/
noncomputable def copyState {n : ℕ} (f : Qubits n → Bool) (t : ℕ) : (Fin t → X n) → ℂ :=
  fun z => ∏ j, fnState f (z j)

/-- An effect (a POVM element): `0 ⪯ E ⪯ 1`. -/
def IsEffect {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Matrix ι ι ℂ) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

/-- The probability `⟨ψ_f^{⊗t}| E |ψ_f^{⊗t}⟩` that the two-outcome measurement with accepting
effect `E` accepts on `t` copies of `|ψ_f⟩`. -/
noncomputable def acceptProb {n t : ℕ} (E : Matrix (Fin t → X n) (Fin t → X n) ℂ)
    (f : Qubits n → Bool) : ℝ :=
  (star (copyState f t) ⬝ᵥ (E *ᵥ copyState f t)).re

/-- Theorem 1, pp.3–4: a quantum algorithm on `t` copies of `|ψ_f⟩` that decides, with success
probability at least `1 - δ`, whether `f` is monotone or `ε`-far from monotone. `E` is the
accepting ("monotone") effect; it is fixed before `f`. -/
def IsMonoTester {n : ℕ} (ε δ : ℝ) (t : ℕ) (E : Matrix (Fin t → X n) (Fin t → X n) ℂ) : Prop :=
  IsEffect E ∧
    (∀ f : Qubits n → Bool, Monotone f → 1 - δ ≤ acceptProb E f) ∧
    (∀ f : Qubits n → Bool, IsFar ε f → acceptProb E f ≤ δ)

end QCopyMono


