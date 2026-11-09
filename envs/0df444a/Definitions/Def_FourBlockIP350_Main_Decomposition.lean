-- Prove2me | Definitions.Def_FourBlockIP350_Main_Decomposition
-- name    : FourBlockIP350_Main_Decomposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:06.024196+00:00
-- url     : https://prove2.me/theorems/e71cc3f0-45f1-40b0-ab0c-c93a39fad5ea
-- title:
--   Conformal order, Graver elements, IDP and the uniform dilation property
-- statement:
--   Conformal domination $a\sqsubseteq b$ means matching coordinate signs and $|a_j|\le |b_j|$. The Graver basis is the set of conformally minimal nonzero integer kernel vectors. A polyhedron $P$ has the integer decomposition property when every integer point of $aP$, for every positive integer $a$, is a sum of $a$ integer points of $P$.
--   $$P_{Q,N,w}=\{z\ge0:Qz=Nw\}.$$
--   UniformDilation records this IDP for every positive number of bricks, every generalized n-fold matrix with the indicated block/entry bounds, and every integral right-hand side. It defines a property only: existence, computability and the asymptotic bound for such $N$ remain the content of Proposition 2.6.
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 5–6, Definitions 2.1–2.2; IDP preamble and Proposition 2.6

import Mathlib
import Definitions.Def_FourBlockIP350_Main_BlockData
import Definitions.Def_FourBlockIP350_Main_LatticeConvexity

namespace FourBlockIP350.Main

open scoped BigOperators

/-- Definition 2.1; works also for integer vectors through coercion. -/
def Conformal {V : Type} (a b : V → ℤ) : Prop :=
  ∀ j, 0 ≤ a j * b j ∧ |a j| ≤ |b j|

def GraverBasis {R V : Type} [Fintype V] (A : Matrix R V ℤ) : Set (V → ℤ) :=
  {z | z ≠ 0 ∧ A.mulVec z = 0 ∧
    ∀ w, w ≠ 0 → A.mulVec w = 0 → Conformal w z → w = z}

/-- IDP: all integer points in every positive integral dilation, not just doubling. -/
def HasIDP {V : Type} [Fintype V] (P : Set (V → ℝ)) : Prop :=
  ∀ a : ℕ, 0 < a → ∀ z : V → ℤ,
    (∃ x ∈ P, (fun j => (z j : ℝ)) = (a : ℝ) • x) →
    ∃ v : Fin a → V → ℤ, (∀ i, (fun j => (v i j : ℝ)) ∈ P) ∧ ∑ i, v i = z

def DilationPolyhedron {k n : ℕ} (Q : NFold k n) (N : ℕ) (w : BlockRow k n → ℤ) :
    Set (LocalCol k n → ℝ) :=
  {z | (∀ j, 0 ≤ z j) ∧
    ∀ r, (∑ j, (Q.matrix r j : ℝ) * z j) = (N : ℝ) * (w r : ℝ)}

/-- The property of the period supplied by Proposition 2.6, uniformly over n and RHS.
This predicate does not assert that a period with this property exists. -/
def UniformDilation (k Δ N : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ Q : NFold k n, Q.Bounded Δ → ∀ w, HasIDP (DilationPolyhedron Q N w)

end FourBlockIP350.Main


