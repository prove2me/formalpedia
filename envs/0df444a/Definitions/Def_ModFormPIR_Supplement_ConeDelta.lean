-- Prove2me | Definitions.Def_ModFormPIR_Supplement_ConeDelta
-- name    : ModFormPIR_Supplement_ConeDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:46:16.195192+00:00
-- url     : https://prove2.me/theorems/c2683713-8af3-4b3d-8a04-2b03e958c044
-- title:
--   Fourier representation, delta functions on a set, and cone-delta functions on $\mathbb Z_q^d$
-- statement:
--   Let $q$ be a prime and $\mathbb F$ a field containing a primitive $q$-th root of unity $\gamma$. For $a\in\mathbb Z_q$ write $\gamma^a$ for $\gamma$ raised to the least nonnegative representative of $a$, and let $\langle w,x\rangle=\sum_i w_ix_i\in\mathbb Z_q$ be the dot product on $\mathbb Z_q^d$.
--
--   Every function $f:\mathbb Z_q^d\to\mathbb F$ has a unique **Fourier representation** $\hat f:\mathbb Z_q^d\to\mathbb F$ with
--
--   $$f(x)=\sum_{w\in\mathbb Z_q^d}\hat f(w)\,\gamma^{\langle w,x\rangle},$$
--
--   and the **Fourier sparsity** of $f$ is the size of the support $\{w:\hat f(w)\neq0\}$ (Definition 4.1).
--
--   For a set $S\subseteq\mathbb Z_q^d$, a function $\delta$ is a **delta function on $S$** if $\delta(0)=1$ and $\delta(x)=0$ for every $x\in S\setminus\{0\}$ (Definition 4.2). The **cone** is $\{x\in\mathbb Z_q^d:\langle x,x\rangle\equiv0\pmod q\}$, and a collection of coefficients $\{c_a\}_{a\in\mathbb Z_q^d}$ is a **cone-delta function** if
--
--   $$\sum_{a\in\mathbb Z_q^d}c_a\gamma^{\langle a,x\rangle}=\begin{cases}1,&x=0,\\0,&x\neq0\text{ on the cone},\\\text{arbitrary},&\text{otherwise}\end{cases}$$
--
--   (Definition 2.1, display (3)).
--
--   These are the objects of the paper's lower bound (Theorem 8.6) and of its lattice construction (Theorem 11.9): a sparse cone-delta function yields a PIR scheme whose servers read few entries.
--
--   **Formalization Note** A function is handled through its coefficient family $c=\hat f$ (the representation is unique, so this is the same data); `fourierEval γ c` is the function and `fourierSupport c` its Fourier support. The power $\gamma^a$ uses `a.val`, the convention of the base mission's quadratic-phase delta expansions.
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Definition 2.1 with (3), p.5 (PDF p.9); Definitions 4.1 and 4.2, p.19 (PDF p.23)

import Mathlib

open Matrix

set_option autoImplicit false

namespace ModFormPIR

namespace Supplement

/-!
# Fourier representations, delta functions on a set, and cone-delta functions

Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027
submission (manuscript sha256 2442f3db…), Definition 2.1 with (3), p.5 (PDF p.9); Definitions 4.1 and 4.2,
p.19 (PDF p.23).

**Formalization Note.**
* `γ` is an element of the field `𝔽` (a primitive `q`-th root of unity in every statement that uses these
  objects), and `γ^a` for `a ∈ ℤ_q` is `γ ^ a.val`; `⟨w, x⟩` is the dot product on `ℤ_q^d` computed in `ℤ_q`.
  This is the convention of the base mission's `ModFormPIR.IsDeltaExpansion`.
* A function `f : ℤ_q^d → 𝔽` is handled through its Fourier coefficients `c = f̂`: by Definition 4.1 the
  representation `f(x) = ∑_w f̂(w) γ^{⟨w,x⟩}` is unique, so a coefficient family and a function are the same
  data. `fourierEval γ c` is the function with Fourier representation `c`, and the Fourier sparsity of that
  function is the number of `w` with `c w ≠ 0` (`fourierSupport c`).
* The cone is `{x ∈ ℤ_q^d : ⟨x, x⟩ ≡ 0 (mod q)}`; a cone-delta function (Definition 2.1, Definition 4.2 with
  the cone) takes the value `1` at `0` and `0` at every other point of the cone, and is unrestricted off the
  cone.
-/

variable {𝔽 : Type*} [Field 𝔽] {q d : ℕ} [NeZero q]

/-- Definition 4.1: the function `x ↦ ∑_{w ∈ ℤ_q^d} c(w) γ^{⟨w,x⟩}` whose Fourier representation is `c`. -/
def fourierEval (γ : 𝔽) (c : (Fin d → ZMod q) → 𝔽) (x : Fin d → ZMod q) : 𝔽 :=
  ∑ w : Fin d → ZMod q, c w * γ ^ (w ⬝ᵥ x).val

/-- Definition 4.1: the Fourier support `{w : c(w) ≠ 0}`; its size is the Fourier sparsity. -/
noncomputable def fourierSupport (c : (Fin d → ZMod q) → 𝔽) : Finset (Fin d → ZMod q) :=
  open Classical in Finset.univ.filter fun w => c w ≠ 0

/-- Definition 4.2: `f` is a delta function on `S`: `f(0) = 1` and `f(x) = 0` for `x ∈ S ∖ {0}`. -/
def IsDeltaOn (S : Set (Fin d → ZMod q)) (f : (Fin d → ZMod q) → 𝔽) : Prop :=
  f 0 = 1 ∧ ∀ x ∈ S, x ≠ 0 → f x = 0

/-- The cone `{x ∈ ℤ_q^d : ⟨x, x⟩ ≡ 0 (mod q)}`. -/
def cone (q d : ℕ) : Set (Fin d → ZMod q) := {x | x ⬝ᵥ x = 0}

/-- Definition 2.1, (3): the coefficients `c` form a cone-delta function, i.e. `∑_a c_a γ^{⟨a,x⟩}` is `1` at
`x = 0`, `0` at every nonzero `x` on the cone, and arbitrary elsewhere. -/
def IsConeDelta (γ : 𝔽) (c : (Fin d → ZMod q) → 𝔽) : Prop :=
  IsDeltaOn (cone q d) (fourierEval γ c)

end Supplement

end ModFormPIR


