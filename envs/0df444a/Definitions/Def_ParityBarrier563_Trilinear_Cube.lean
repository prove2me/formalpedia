-- Prove2me | Definitions.Def_ParityBarrier563_Trilinear_Cube
-- name    : ParityBarrier563_Trilinear_Cube
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:49.517975+00:00
-- url     : https://prove2.me/theorems/8f186938-af99-4e87-a026-1285224d01bb
-- title:
--   §2 — the Boolean cube, uniform averages, indicators and signs
-- statement:
--   Let $V$ be a finite set of variables. The **Boolean cube** $\{0,1\}^V$ is the set of all assignments $z:V\to\{0,1\}$. A Boolean function is a map $\{0,1\}^V\to\{0,1\}$, and a real function is a map $\{0,1\}^V\to\mathbb R$. Unless stated otherwise, expectations are uniform averages over the cube:
--
--   $$\mathbb E[f]=\frac{1}{2^{|V|}}\sum_{z\in\{0,1\}^V} f(z).$$
--
--   For a Boolean function $H$, its real indicator takes the value $1$ on accepted points and $0$ on rejected points. The **sign** of a Boolean function $f$ is $g=2f-1:\{0,1\}^V\to\{-1,1\}$, which is $+1$ on accepted inputs and $-1$ on rejected inputs. For real functions $\psi,H$ on the same cube, $\mathbb E[\psi H]$ is their **signed inner product**: it is neither centered nor normalized.
--
--   These are the basic objects of every statement in the mission: correlations, CNF norms and restriction averages are all built from them.
--
--   **Formalization Note** A point of the cube is a map `V → Bool` (`true` is $1$). The average divides by the cardinality of the cube, which is $2^{|V|}\ge1$, so it is also defined for empty $V$ (the cube is then a single point).
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, §2 Preliminaries, printed p.9 (PDF p.11)

import Mathlib

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-! §2, printed p.9 / PDF 11: the Boolean cube `{0,1}^V`, uniform averages, indicators and signs.
A point of the cube is an assignment `V → Bool` (`true` = 1, `false` = 0). -/

/-- A Boolean function `{0,1}^V → {0,1}`. -/
abbrev BoolFn (V : Type) := (V → Bool) → Bool

/-- A real-valued function on the cube `{0,1}^V`. -/
abbrev RealFn (V : Type) := (V → Bool) → ℝ

/-- The uniform average `E_z[f(z)]` over the cube `{0,1}^V`
(the default expectation of §2): `2^{-|V|} ∑_z f(z)`. -/
noncomputable def avg {V : Type} [Fintype V] [DecidableEq V] (f : RealFn V) : ℝ :=
  (∑ z : V → Bool, f z) / (Fintype.card (V → Bool) : ℝ)

/-- The `{0,1}`-valued real indicator of a Boolean function (1 on accepted inputs). -/
def ind {V : Type} (H : BoolFn V) : RealFn V := fun z => if H z then 1 else 0

/-- The sign `2f − 1` of a Boolean function `f`: `+1` on accepted and `−1` on rejected inputs. -/
def sgn {V : Type} (f : BoolFn V) : RealFn V := fun z => 2 * ind f z - 1

end ParityBarrier563.Trilinear


