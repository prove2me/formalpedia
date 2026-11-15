-- Prove2me | Definitions.Def_SymmetricPSM1041_ORLowerBound_Supplement_ColoringsSubfunctions
-- name    : SymmetricPSM1041_ORLowerBound_Supplement_ColoringsSubfunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:44:52.570284+00:00
-- url     : https://prove2.me/theorems/7d03efc8-1267-4486-8452-53eb5a7301a3
-- title:
--   §4.3 — consistent coloring families and the subfunction count $N_S(f)$
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$, let $K$ be a positive integer and $b\in\{0,1\}$. A family of colorings $\alpha_x:[n]\to[K]$, one for each $x\in\{0,1\}^n$, is a **$b$-consistent $K$-coloring family** for $f$ if for all $x,y$ with $f(x)=f(y)=b$, writing $A_{xy}=\{i:\alpha_x(i)=\alpha_y(i)\}$ for the agreement set, every $z\in\{0,1\}^n$ with $\{i:z_i=1\}\subseteq A_{xy}$ satisfies
--
--   $$f(x\oplus z)=f(y\oplus z),$$
--
--   where $\oplus$ is coordinatewise exclusive or.
--
--   For $S\subseteq[n]$ and $z\in\{0,1\}^n$, the subfunction $f|_{\bar S=z}:\{0,1\}^S\to\{0,1\}$ fixes the coordinates outside $S$ according to $z$. The number $N_S(f)$ of **subfunctions of $f$ on $S$** is the number of distinct functions of this form as $z$ ranges over $\{0,1\}^n$.
--
--   These are the combinatorial quantities of the general lower bound (Theorem 28) and of the Nechiporuk bound (Theorem 29).
--
--   **Formalization Note** Colors $[K]$ are `Fin K`; the family is a function `(Fin n → Bool) → Fin n → Fin K`. The definition itself does not require $K>0$; Theorem 28 assumes it. Subfunctions use the published `restrictFunction`, whose domain is exactly the free coordinates $S$.
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 19, Definition (Consistent Coloring Family) and Theorem 29 (N_S(f)); restriction p. 7

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions

namespace SymmetricPSM1041.ORLowerBound.Supplement

/-- A family `α_x : [n] → [K]` (one coloring per input `x`) is a `b`-consistent `K`-coloring
family for `f` if for all `x, y` with `f x = f y = b` and every `z` supported inside the
agreement set `{i | α_x i = α_y i}`, we have `f (x ⊕ z) = f (y ⊕ z)`. -/
def IsConsistentColoringFamily {n : ℕ} (f : (Fin n → Bool) → Bool) (K : ℕ) (b : Bool)
    (α : (Fin n → Bool) → Fin n → Fin K) : Prop :=
  ∀ x y : Fin n → Bool, f x = b → f y = b →
    ∀ z : Fin n → Bool, (∀ i, z i = true → α x i = α y i) →
      f (fun i => xor (x i) (z i)) = f (fun i => xor (y i) (z i))

/-- `N_S(f)`: the number of distinct subfunctions `f|_{S̄ = z} : {0,1}^S → {0,1}`
over all assignments `z ∈ {0,1}^n` to the coordinates outside `S`. -/
noncomputable def subfunctionCount {n : ℕ} (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.image (fun z : Fin n → Bool => restrictFunction f S z)).card

end SymmetricPSM1041.ORLowerBound.Supplement


