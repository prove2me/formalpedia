-- Prove2me | Definitions.Def_SmolenskyAC_Wiring
-- name    : SmolenskyAC_Wiring
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:39.842202+00:00
-- url     : https://prove2.me/theorems/8d94529d-c2d0-4faa-8424-517751400f39
-- title:
--   The wiring $\sigma_s$ of reductions 1) and 4), and wirings in general
-- statement:
--   For integers $a,q,s,n,m$ the map $\sigma:D^n\to D^m$ sends $x$ to the $m$ wires where wire $j<a n$ carries $x_{\lfloor j/a\rfloor}$ (each input on $a$ wires), the next $a(q-s)$ wires carry $1$, and the remaining wires carry $0$.
--
--   A map $\sigma:D^n\to D^m$ is a **wiring** if each of its $m$ coordinates is an input variable $x_i$ or a constant. Substituting a wiring into a circuit on $m$ inputs adds no gate and keeps the depth.
--
--   With $a=r/q$, one $\mathrm{MOD}_r$ gate fed with $\sigma(x)$ and negated computes $\mathrm{MOD}_{s,q}(x)$; this is the reduction the main theorem's proof uses.
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, reductions 1) and 4), p.78 (pdf 2); proof of Theorem 2, p.81 (pdf 5)

import Mathlib
import Definitions.Def_SmolenskyAC_Operations

namespace SmolenskyAC

/-- The wiring of reductions 1) and 4) (Smolensky, STOC 1987, p.78), from `n` inputs to `m` wires:
wire `j < a·n` carries `x_{⌊j/a⌋}` (so each input is on `a` wires), the next `a·(q − s)` wires
carry the constant `1`, and the remaining wires the constant `0`. With `a = r/q`, feeding these
wires to one `MOD_r` gate and negating gives `MOD_{s,q}(x)` (milestone `reduction_wiring`). -/
def wiring (a q s n m : ℕ) (x : Cube n) : Cube m := fun j =>
  if h : j.val < a * n then x ⟨j.val / a, Nat.div_lt_of_lt_mul h⟩
  else decide (j.val < a * n + a * (q - s))

/-- A map `σ : D^n → D^m` is a **wiring** if each of its `m` coordinates is an input variable or a
constant: substituting it into a circuit on `m` inputs connects every input wire to an input or a
constant, and adds no gate. -/
def IsWiring {n m : ℕ} (σ : Cube n → Cube m) : Prop :=
  ∀ j : Fin m, (∃ i : Fin n, ∀ x, σ x j = x i) ∨ ∃ b : Bool, ∀ x, σ x j = b

end SmolenskyAC


