-- Prove2me | Definitions.Def_ParityBarrier563_Trilinear_Supplement_InverseTrace
-- name    : ParityBarrier563_Trilinear_Supplement_InverseTrace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:39:30.964782+00:00
-- url     : https://prove2.me/theorems/7e8a27c0-1d01-4bab-8abd-b63da0cfa171
-- title:
--   Inverse trace in arbitrary binary coordinates
-- statement:
--   Let K be a field with an algebra structure over $\mathbb F_2$ and an ordered basis $e_0,\ldots,e_{n-1}$. Encode $x\in\{0,1\}^n$ by $\iota_e(x)=\sum_i x_ie_i$. Define
--   $$\operatorname{Tr}_n(z)=\sum_{j=0}^{n-1}z^{2^j},\quad I_e(x)=1_{\{\operatorname{Tr}_n(\iota_e(x)^{-1})=1\}},\quad\chi(z)=(-1)^{\operatorname{Tr}_n(z)}.$$
--   For $n\ge1$, the basis identifies K with $\mathbb F_{2^n}$ and the trace lies in its prime subfield. Inverse at zero is zero. The sign is the published $2I_e-1$. Coordinate shifts use XOR; zeroFill embeds a live-coordinate assignment with zero on fixed coordinates. These definitions cover every basis without a preferred polynomial basis.
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), §1.2, printed p.3 / PDF 5; §2, printed p.11 / PDF 13; §5.3, printed p.22 / PDF 24

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Supplement_FiniteAverages

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Coordinate encoding in an arbitrary F₂-basis. A basis with n vectors supplies exactly
all elements of the characteristic-two field, hence the field has 2^n elements. -/
noncomputable def fieldPoint {n : ℕ} {K : Type} [Field K] [Algebra (ZMod 2) K]
    (e : Module.Basis (Fin n) (ZMod 2) K) (x : Fin n → Bool) : K :=
  ∑ i, (if x i then e i else 0)

/-- Absolute trace, calculated in K. Its values lie in the embedded F₂. -/
def absoluteTrace (n : ℕ) {K : Type} [Field K] (z : K) : K :=
  ∑ j : Fin n, z ^ (2 ^ j.val)

/-- Inverse trace, accepting exactly when its F₂ value is one; field inverse at 0 is 0. -/
noncomputable def inverseTrace {n : ℕ} {K : Type} [Field K] [Algebra (ZMod 2) K]
    (e : Module.Basis (Fin n) (ZMod 2) K) : BoolFn (Fin n) :=
  fun x => decide (absoluteTrace n (fieldPoint e x)⁻¹ = 1)

/-- Canonical additive character (-1)^Tr, with Tr computed in K. -/
noncomputable def character (n : ℕ) {K : Type} [Field K] (z : K) : ℝ :=
  if absoluteTrace n z = 1 then -1 else 1

/-- Fill live coordinates and put zero on fixed coordinates, for a shift uniform in live(τ). -/
def zeroFill {V : Type} (τ : Restriction V) (w : Live τ → Bool) : V → Bool :=
  fun v => match h : τ v with
    | none => w ⟨v,h⟩
    | some _ => false

/-- Coordinate XOR equals addition in every F₂-basis. -/
def shift {V : Type} (w : V → Bool) (J : RealFn V) : RealFn V :=
  fun x => J (fun i => Bool.xor (x i) (w i))

end ParityBarrier563.Trilinear.Supplement


