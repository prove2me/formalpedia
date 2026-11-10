-- Prove2me | Definitions.Def_MatMulPolyBarrier_Operational_Fstar
-- name    : MatMulPolyBarrier_Operational_Fstar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:07:30.43459+00:00
-- url     : https://prove2.me/theorems/5be5c2ac-3750-4704-b486-c9686c45287a
-- title:
--   The parameter set $\Theta$, the exponents $p_i$ (5.2) and the functions $F^\star_\theta$ (Definition 5.5)
-- statement:
--   Let $\Theta$ be the set of triples $\theta=(\theta_1,\theta_2,\theta_3)$ of positive real numbers with $\theta_1+\theta_2+\theta_3=1$. For $\theta\in\Theta$ and $\{i,j,k\}=\{1,2,3\}$ put
--   $$p_i:=\frac{\theta_i}{(1-\theta_j)(1-\theta_k)}\qquad(5.2).$$
--   **Definition 5.5.** (i) For an admissible triple $(d_1,d_2,d_3)$ of real numbers let $A_s:=(d_s-\theta_s)/(1-\theta_s)$, $s\in\{1,2,3\}$. Choose indices with $\{i,j,k\}=\{1,2,3\}$, $d_i,d_j\le d_k$ and $A_i\le A_j$, and set
--   $$F^\star_\theta(d_1,d_2,d_3):=A_i^{\,1-p_i}\,\bigl(\theta_jA_i+(1-\theta_j)A_j\bigr)^{p_i}.$$
--   On generators, $F^\star_\theta(P_{x,y,z}):=F^\star_\theta(x,y,z)$. (ii) On formal expressions, $F^\star_\theta(S\oplus T):=F^\star_\theta(S)+F^\star_\theta(T)$, $F^\star_\theta(S\otimes T):=F^\star_\theta(S)F^\star_\theta(T)$ and $F^\star_\theta(S\oplus_\ell T):=\bigl(F^\star_\theta(S)^{1/p_\ell}+F^\star_\theta(T)^{1/p_\ell}\bigr)^{p_\ell}$.
--
--   **Formalization Note.** `θ : Fin 3 → ℝ`, the paper's $\theta_1,\theta_2,\theta_3$ being `θ 0, θ 1, θ 2`; `InTheta θ` is $\theta\in\Theta$; `pExp θ i` is $p_{i+1}$, written with $j=i+1$, $k=i+2$ in `Fin 3` (the formula is symmetric in $j,k$); `Acoord θ d s` is $A_{s+1}$. The definition fixes one admissible choice of indices: $k$ = the first index of a largest entry (`maxIdx`), $i$ = the one of $k+1,k+2$ with the smaller $A$ ($k+1$ on a tie, `idxI`), $j$ the other (`idxJ`); that every admissible choice gives the same value is the separate theorem `definition_5_5_well_defined`. `FstarTriple θ d` is $F^\star_\theta(d)$ for a real triple $d$, and `Fstar θ E` is $F^\star_\theta(E)$ for a formal expression; powers are `Real.rpow` (all bases are $\ge1$ or positive on $\mathcal F$). Values outside admissible triples and outside $\mathcal F$ are never used.
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), p. 38, §5.4: Θ, Eq. (5.2), Definition 5.5

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr

set_option autoImplicit false

/-!
# The parameter set Θ, the exponents `p_i` (5.2) and the functions `F⋆_θ` (Definition 5.5)

Amanov, van den Berg, Zuiddam, *Multiplying matrices via polynomials: operational asymptotic
spectrum barrier*, STOC 2027 submission, p. 38, §5.4: Θ, (5.2), Definition 5.5.

Conventions.
* `θ : Fin 3 → ℝ`; the paper's `θ₁, θ₂, θ₃` are `θ 0, θ 1, θ 2`, and likewise for `p_i`, `A_s`
  and the legs.
* For `{i, j, k} = {0, 1, 2}`, `pExp θ i = θ i / ((1 − θ j)(1 − θ k))`, written with `j = i + 1`,
  `k = i + 2` in `Fin 3` (the formula is symmetric in `j, k`).
* Definition 5.5(i) lets any indices `i, j, k` with `d i, d j ≤ d k` and `A i ≤ A j` be used. The
  Lean definition fixes one choice: `k` is the first index of a largest entry, and `i` is the one
  of the other two indices `k + 1, k + 2` with the smaller `A` (`k + 1` on a tie), `j` the other.
  That the value does not depend on the choice is a theorem of the mission (the well-definedness
  claim of Definition 5.5(i)).
* Powers are real powers `Real.rpow`; on admissible triples every base is `≥ 1`.
* `F⋆_θ` is defined on all formal expressions by the recursion of Definition 5.5(ii); its values
  matter only on expressions in `F`.
-/

namespace MatMulPolyBarrier.Operational

open FExpr

/-- Θ (p. 38): triples of positive reals summing to `1`. -/
def InTheta (θ : Fin 3 → ℝ) : Prop :=
  (∀ s, 0 < θ s) ∧ θ 0 + θ 1 + θ 2 = 1

/-- The exponents (5.2): `p_i := θ_i / ((1 − θ_j)(1 − θ_k))` for `{i, j, k} = {1, 2, 3}`. -/
noncomputable def pExp (θ : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  θ i / ((1 - θ (i + 1)) * (1 - θ (i + 2)))

/-- `A_s := (d_s − θ_s) / (1 − θ_s)` (Definition 5.5(i)). -/
noncomputable def Acoord (θ d : Fin 3 → ℝ) (s : Fin 3) : ℝ :=
  (d s - θ s) / (1 - θ s)

/-- The first index of a largest entry of `d`. -/
noncomputable def maxIdx (d : Fin 3 → ℝ) : Fin 3 :=
  if d 1 ≤ d 0 ∧ d 2 ≤ d 0 then 0 else if d 2 ≤ d 1 then 1 else 2

/-- The index `i` of Definition 5.5(i): of the two indices other than `k = maxIdx d`, the one with
the smaller `A` (`k + 1` on a tie). -/
noncomputable def idxI (θ d : Fin 3 → ℝ) : Fin 3 :=
  if Acoord θ d (maxIdx d + 1) ≤ Acoord θ d (maxIdx d + 2) then maxIdx d + 1 else maxIdx d + 2

/-- The index `j` of Definition 5.5(i): the remaining index. -/
noncomputable def idxJ (θ d : Fin 3 → ℝ) : Fin 3 :=
  if Acoord θ d (maxIdx d + 1) ≤ Acoord θ d (maxIdx d + 2) then maxIdx d + 2 else maxIdx d + 1

/-- Definition 5.5(i): for an admissible triple `d` of reals,
`F⋆_θ(d₁, d₂, d₃) := A_i^{1 − p_i} (θ_j A_i + (1 − θ_j) A_j)^{p_i}`, with the indices chosen by
`maxIdx`, `idxI`, `idxJ`. -/
noncomputable def FstarTriple (θ d : Fin 3 → ℝ) : ℝ :=
  Acoord θ d (idxI θ d) ^ (1 - pExp θ (idxI θ d)) *
    (θ (idxJ θ d) * Acoord θ d (idxI θ d) + (1 - θ (idxJ θ d)) * Acoord θ d (idxJ θ d)) ^
      pExp θ (idxI θ d)

/-- Definition 5.5: `F⋆_θ(P_{x,y,z}) := F⋆_θ(x, y, z)`, `F⋆_θ(S ⊕ T) := F⋆_θ(S) + F⋆_θ(T)`,
`F⋆_θ(S ⊗ T) := F⋆_θ(S) F⋆_θ(T)`, `F⋆_θ(S ⊕_ℓ T) := (F⋆_θ(S)^{1/p_ℓ} + F⋆_θ(T)^{1/p_ℓ})^{p_ℓ}`. -/
noncomputable def Fstar (θ : Fin 3 → ℝ) : FExpr → ℝ
  | P x y z => FstarTriple θ ![(x : ℝ), (y : ℝ), (z : ℝ)]
  | dsum S T => Fstar θ S + Fstar θ T
  | tens S T => Fstar θ S * Fstar θ T
  | psum l S T => (Fstar θ S ^ (1 / pExp θ l) + Fstar θ T ^ (1 / pExp θ l)) ^ pExp θ l

end MatMulPolyBarrier.Operational


