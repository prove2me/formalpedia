-- Prove2me | Definitions.Def_SYKCavity_Ladder
-- name    : SYKCavity_Ladder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:17.065199+00:00
-- url     : https://prove2.me/theorems/8488f936-5c9b-4444-b1f7-1a0a9643d6d8
-- title:
--   The ladder operator $\mathfrak L_\beta=I-K$ on antisymmetric kernels in $L^2([0,1]^2)$
-- statement:
--   Let $G_*(u,v)$ be the two-time saddle kernel. For a kernel $X$ on $[0,1]^2$ the **ladder operator** is
--   $$(\mathfrak L_\beta X)(u,v)=X(u,v)-3\beta^2\int_0^1\!\!\int_0^1G_*(u,s)\,G_*(s,t)^2\,X(s,t)\,G_*(t,v)\,ds\,dt.\qquad(3.30)$$
--   It acts on **antisymmetric** kernels, $X(v,u)=-X(u,v)$, in $L^2([0,1]^2)$. The temperature $\beta$ is **regular** (the $L^2$ inverse exists) when $\mathfrak L_\beta$ is a bijection of the antisymmetric $L^2$ kernels. Norms: $\|X\|_2$ and the essential supremum $\|X\|_\infty$ on $[0,1]^2$.
--
--   Inverting $\mathfrak L_\beta$ is how the hierarchy (4.9) for the centered moments is solved (Lemma 5).
--
--   **Formalization Note** Kernels are functions $\mathbb R^2\to\mathbb R$ compared up to almost-everywhere equality on $[0,1]^2$; membership in $L^2$ is `MemLp X 2`.
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), (3.30), p.25; Lemma 5, p.27; Appendix H, p.129

import Mathlib
import Definitions.Def_SYKCavity_Saddle

open MeasureTheory

namespace SYKCavity

/-!
# The ladder operator `L_β = I − K` on antisymmetric kernels in `L²([0,1]²)`

A. Schmidhuber, A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass
transition*, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5): (3.30), p.25; Lemma 5, p.27;
Appendix H, p.129 ("We work on antisymmetric kernels in `L2([0, 1]2)`, antiperiodically extended in
each argument").

**Formalization Note.**
* `sq` is Lebesgue measure on the unit square `[0,1]²`. A kernel is a function `X : ℝ × ℝ → ℝ`; it is
  in the domain when `MemLp X 2 sq`, and it is antisymmetric when `X(v, u) = −X(u, v)` for
  `sq`-a.e. `(u, v)` (`Antisym`). Kernels are compared up to `sq`-a.e. equality, i.e. as elements of
  `L²`.
* `ladder β X (u, v) = X(u, v) − 3β² ∫∫_{[0,1]²} G*(u, s) G*(s, t)² X(s, t) G*(t, v) ds dt`, (3.30),
  with the two-time kernel `G*(a, b) = gExt β (a − b)`.
* `IsRegular β`: the `L²` inverse of `L_β` on antisymmetric kernels exists, i.e. `L_β` is a bijection
  of the antisymmetric `L²` classes (every antisymmetric `X ∈ L²` is `L_β Y` for an antisymmetric
  `Y ∈ L²`, and `L_β Y = L_β Y'` a.e. forces `Y = Y'` a.e.). `L_β` is bounded on `L²`, so the inverse
  is then bounded (open mapping theorem).
* `‖X‖∞` is the essential supremum `eLpNorm X ∞ sq`; `‖Y‖₂ = eLpNorm Y 2 sq`.
-/

/-- Lebesgue measure on the unit square `[0,1]²`. -/
noncomputable def sq : Measure (ℝ × ℝ) :=
  (volume : Measure (ℝ × ℝ)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)

/-- `X(v, u) = −X(u, v)` for a.e. `(u, v) ∈ [0,1]²`. -/
def Antisym (X : ℝ × ℝ → ℝ) : Prop :=
  (fun q : ℝ × ℝ => X q.swap) =ᵐ[sq] fun q => -X q

/-- `(L_β X)(u, v) = X(u, v) − 3β² ∫∫ G*(u, s) G*(s, t)² X(s, t) G*(t, v) ds dt`, (3.30). -/
noncomputable def ladder (β : ℝ) (X : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p =>
  X p - 3 * β ^ 2 *
    ∫ q, gExt β (p.1 - q.1) * gExt β (q.1 - q.2) ^ 2 * X q * gExt β (q.2 - p.2) ∂sq

/-- The `L²` inverse of `L_β` exists on antisymmetric kernels. -/
def IsRegular (β : ℝ) : Prop :=
  (∀ X : ℝ × ℝ → ℝ, MemLp X 2 sq → Antisym X →
      ∃ Y : ℝ × ℝ → ℝ, MemLp Y 2 sq ∧ Antisym Y ∧ ladder β Y =ᵐ[sq] X) ∧
    ∀ Y Y' : ℝ × ℝ → ℝ, MemLp Y 2 sq → Antisym Y → MemLp Y' 2 sq → Antisym Y' →
      ladder β Y =ᵐ[sq] ladder β Y' → Y =ᵐ[sq] Y'

end SYKCavity


