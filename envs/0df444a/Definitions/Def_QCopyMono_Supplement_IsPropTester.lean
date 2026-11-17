-- Prove2me | Definitions.Def_QCopyMono_Supplement_IsPropTester
-- name    : QCopyMono_Supplement_IsPropTester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:20:48.021149+00:00
-- url     : https://prove2.me/theorems/143cd7be-e033-44a2-9dd3-de543b45f2bc
-- title:
--   Union-closed and 2-monotone Boolean functions, distance from a property, and testers for a property on $t$ copies of $|\psi_f\rangle$
-- statement:
--   Identify $\{0,1\}^n$ with bit strings ordered coordinate-wise: $x\preceq y$ iff $x_i\le y_i$ for every $i\in[n]$, and $x\prec y$ iff $x\preceq y$ and $x\neq y$. Write $x\vee y$ for the coordinate-wise OR, $(x\vee y)_i=\max\{x_i,y_i\}$.
--
--   A Boolean function $f:\{0,1\}^n\to\{0,1\}$ is
--
--   1. **union-closed** if $f(x)=f(y)=1$ implies $f(x\vee y)=1$, for all $x,y\in\{0,1\}^n$;
--   2. **2-monotone** if there are no $x\prec y\prec z$ with $(f(x),f(y),f(z))=(1,0,1)$.
--
--   For a property $\mathcal P$ (a class of Boolean functions on $\{0,1\}^n$) and $\varepsilon>0$, $f$ is **$\varepsilon$-far from $\mathcal P$** if
--
--   $$
--   \mathrm{dist}(f,\mathcal P)=\min_{g\in\mathcal P}\mathrm{dist}(f,g)\ge\varepsilon,\qquad \mathrm{dist}(f,g)=\Pr_{x\sim\mathrm{Unif}(\{0,1\}^n)}[f(x)\ne g(x)].
--   $$
--
--   A **tester for $\mathcal P$ with parameters $(\varepsilon,\delta)$ on $t$ copies** is a two-outcome measurement on $|\psi_f\rangle^{\otimes t}$, given by its accepting effect $E$ ($0\preceq E\preceq I$), fixed independently of $f$, that accepts with probability $\langle\psi_f^{\otimes t}|E|\psi_f^{\otimes t}\rangle\ge1-\delta$ whenever $f\in\mathcal P$ and with probability at most $\delta$ whenever $f$ is $\varepsilon$-far from $\mathcal P$.
--
--   These objects state the paper's lower bounds for testing union-closedness and 2-monotonicity (Theorem 3). For $\mathcal P$ the monotone functions, the tester is exactly the monotonicity tester of the base mission.
--
--   **Formalization Note** Bit strings are `QAlgorithms.Qubits n = Fin n → Bool` with `false` $=0$, `true` $=1$; $x\vee y$ is `x ⊔ y` and $x\prec y$ is `x < y` in the pi order. The distance, the function state, effects and acceptance probabilities are the published `QCopyMono.IsMonoTester` objects. "$\varepsilon$-far" is written as $\varepsilon\le\mathrm{dist}(f,g)$ for every $g\in\mathcal P$; for the two properties used here the class is finite and nonempty (the constant $0$ function belongs to both), so this is the minimum form.
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), §1, p.3 (dist(f, P)); §1.1, p.4 and §5, p.29 (union-closed, 2-monotone); §2, p.6 (copy model)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester

namespace QCopyMono

namespace Supplement

open QAlgorithms

/-! # Union-closed and 2-monotone functions, distance from a property, testers for a property

P. Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), §1, p.3 (`dist(f, P) = min_{g ∈ P} dist(f, g)`),
§1.1, p.4 and §5, p.29 (union-closed, 2-monotone).

**Formalization Note.**
* Bit strings are `QAlgorithms.Qubits n = Fin n → Bool` with `false = 0`, `true = 1`. The
  coordinate-wise OR `x ∨ y` is `x ⊔ y` in the pi lattice (`⊔` on `Bool` is `||`). The strict
  order `x ≺ y` ("`x ≠ y` and `x_i ≤ y_i` for every `i`") is `x < y` in the pi partial order.
* The copy model, the distance `relDist`, effects `IsEffect` and acceptance probabilities
  `acceptProb` are the published `QCopyMono.IsMonoTester` objects, reused unchanged.
* "ε-far from `P`" is `ε ≤ dist(f, g)` for every `g ∈ P`, the same pattern as the published
  `IsFar` (which is `IsFarFrom Monotone`). For the two properties used here the class is finite
  and nonempty (the constant-`false` function belongs to both), so this equals
  `dist(f, P) ≥ ε` with the minimum attained.
* A tester for `P` with parameters `(ε, δ)` on `t` copies is an accepting effect `E` on the
  `t`-copy register, fixed before `f`, that accepts every `f ∈ P` with probability at least
  `1 − δ` and every `f` that is `ε`-far from `P` with probability at most `δ`. With
  `P = Monotone` it is exactly the published `IsMonoTester`. -/

/-- §1.1, p.4 and §5, p.29: `f` is union-closed if `f(x) = f(y) = 1` implies `f(x ∨ y) = 1`,
where `(x ∨ y)_i = max{x_i, y_i}`. -/
def IsUnionClosed {n : ℕ} (f : Qubits n → Bool) : Prop :=
  ∀ x y : Qubits n, f x = true → f y = true → f (x ⊔ y) = true

/-- §1.1, p.4 and §5, p.29: `f` is 2-monotone if there are no `x ≺ y ≺ z` with
`(f(x), f(y), f(z)) = (1, 0, 1)`; `x ≺ y` means `x ≠ y` and `x_i ≤ y_i` for every `i`. -/
def IsTwoMonotone {n : ℕ} (f : Qubits n → Bool) : Prop :=
  ¬ ∃ x y z : Qubits n, x < y ∧ y < z ∧ f x = true ∧ f y = false ∧ f z = true

/-- p.3: `f` is `ε`-far from the property `P`, `dist(f, P) = min_{g ∈ P} dist(f, g) ≥ ε`,
written as `ε ≤ dist(f, g)` for every `g ∈ P`. -/
def IsFarFrom {n : ℕ} (P : (Qubits n → Bool) → Prop) (ε : ℝ) (f : Qubits n → Bool) : Prop :=
  ∀ g : Qubits n → Bool, P g → ε ≤ relDist f g

/-- pp.3–4, p.6: a quantum algorithm on `t` copies of `|ψ_f⟩` that decides, with success
probability at least `1 − δ`, whether `f` has property `P` or is `ε`-far from `P`. `E` is the
accepting effect of a two-outcome joint measurement on `|ψ_f⟩^{⊗t}`, fixed before `f`. -/
def IsPropTester {n : ℕ} (P : (Qubits n → Bool) → Prop) (ε δ : ℝ) (t : ℕ)
    (E : Matrix (Fin t → X n) (Fin t → X n) ℂ) : Prop :=
  IsEffect E ∧
    (∀ f : Qubits n → Bool, P f → 1 - δ ≤ acceptProb E f) ∧
    (∀ f : Qubits n → Bool, IsFarFrom P ε f → acceptProb E f ≤ δ)

end Supplement

end QCopyMono


