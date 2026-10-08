-- Prove2me | Definitions.Def_Dubey1986_Inefficiency_Derivative
-- name    : Dubey1986_Inefficiency_Derivative
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:34:04.13846+00:00
-- url     : https://prove2.me/theorems/856acf53-494b-470a-9294-1f16c45f6fe2
-- title:
--   pp. 3–4 — the derivative map $D_u$, the sets $N^*$ and $E^*$, transversality to a linear subspace
-- statement:
--   These are the objects used in the proof of the main theorem (pp. 3–5).
--
--   For a game $u=(u^1,\dots,u^n)$ and a point $s$, $D_u(s)=D(u,s)$ is the $n\times r(n)$ matrix whose $i$-th row is the derivative $Du^i(s)=\big(\partial u^i/\partial x_1(s),\dots,\partial u^i/\partial x_r(s)\big)$.
--
--   $N^*$ is the set of $n\times r(n)$ matrices $A$ whose $i$-th row vanishes on player $i$'s own block of columns:
--   $$N^*=\{A : A_{ij}=0 \text{ for } r(i-1)+1\le j\le r(i)\},$$
--   a linear subspace. $E^*$ is the set of matrices whose rows are linearly dependent.
--
--   A differentiable map $f$ into a finite-dimensional space is **transverse** to a linear subspace $W$ at $x$ if either $f(x)\notin W$, or the image of $Df(x)$ together with $W$ spans the whole target space.
--
--   **Formalization Note** The matrix $D_u(s)$ is encoded as its family of $n$ row functionals $Du^i(s)$ (continuous linear maps $\mathbb R^{r(n)}\to\mathbb R$); $N^*$ is a `Submodule`. Transversality is stated only for linear subspaces: the "splits" clause of the general definition is automatic in finite dimension (the paper's footnote 1, p. 5).
-- source:
--   Dubey, Inefficiency of Nash Equilibria, IIASA WP-83-74 (July 1983), pp. 3–4 (the derivative map D, D_u, N*, E*) and p. 5 with footnote 1 (transversality)

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting

namespace Dubey1986.Inefficiency

/-- The derivative map `D_u(s) = D(u,s)` (pp. 3–4): the `n × r(n)` matrix whose `i`-th row is
`Du^i(s)`, encoded as the family of row functionals. -/
noncomputable def Dmap {n : ℕ} {k : Fin n → ℕ} (u : Fin n → Strat k → ℝ) (s : Strat k) :
    Fin n → (Strat k →L[ℝ] ℝ) :=
  fun i => fderiv ℝ (u i) s

/-- `N* = {A : A_{ij} = 0 for r(i−1)+1 ≤ j ≤ r(i)}` (p. 4): row `i` vanishes on player `i`'s
own block of coordinates. -/
def Nstar {n : ℕ} (k : Fin n → ℕ) : Submodule ℝ (Fin n → (Strat k →L[ℝ] ℝ)) where
  carrier := {A | ∀ i (v : Fin (k i) → ℝ), A i (Pi.single i v) = 0}
  add_mem' := by
    intro A B hA hB i v
    simp [hA i v, hB i v]
  zero_mem' := by
    intro i v
    simp
  smul_mem' := by
    intro c A hA i v
    simp [hA i v]

/-- `E* = {A : the rows of A are linearly dependent}` (p. 4). -/
def Estar {n : ℕ} (k : Fin n → ℕ) : Set (Fin n → (Strat k →L[ℝ] ℝ)) :=
  {A | ¬ LinearIndependent ℝ A}

/-- `f` is transverse to the linear subspace `W` at `x`: either `f x ∉ W`, or the image of
`Df(x)` together with `W` spans the whole (finite-dimensional) target. -/
def TransverseAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (W : Submodule ℝ F) (x : E) : Prop :=
  f x ∉ W ∨ LinearMap.range (fderiv ℝ f x : E →ₗ[ℝ] F) ⊔ W = ⊤

end Dubey1986.Inefficiency


