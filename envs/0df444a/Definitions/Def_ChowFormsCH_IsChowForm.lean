-- Prove2me | Definitions.Def_ChowFormsCH_IsChowForm
-- name    : ChowFormsCH_IsChowForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:16.646916+00:00
-- url     : https://prove2.me/theorems/78c39454-6452-4203-aeb5-d535704ba304
-- title:
--   Chow form $C_V$ of an equidimensional projective variety and its lexicographic normalization
-- statement:
--   Let $V\subseteq\mathbb P^n$ and $r\ge 0$. Introduce $r+1$ groups of variables $u_i=(u_{i,0},\dots,u_{i,n})$, $0\le i\le r$, and the general linear forms $L_i=u_{i,0}x_0+\dots+u_{i,n}x_n$. The incidence set is
--   $$
--   W=\{\gamma=(\gamma_{i,j}) : L_{\gamma_0},\dots,L_{\gamma_r} \text{ have a common zero on } V\}.
--   $$
--   A polynomial $C\in K[u]$ is **a Chow form of $V$** if $C\neq 0$, $C$ is squarefree, and the zero set of $C$ is exactly $W$. It is **the (normalized) Chow form $C_V$** if moreover its leading coefficient in the lexicographic order extending $u_{i,j}>u_{i',j'}$ (for $i<i'$, or $i=i'$ and $j<j'$) equals $1$.
--
--   For $V$ equidimensional of dimension $r$ this is the paper's Chow form: the defining equation of the hypersurface $W$ for irreducible $V$, and the product of the components' Chow forms in general. The empty variety has Chow form $1$. Chow forms are the objects the circuits of Theorem 4.9 compute.
--
--   **Formalization Note** Over an algebraically closed field a squarefree polynomial is determined by its zero set up to a nonzero scalar, so "is a Chow form" means "is a nonzero scalar multiple of $C_V$". Variables are indexed by `Fin (r+1) × Fin (n+1)`; the lexicographic leading coefficient uses Mathlib's `MonomialOrder.lex` on `Lex (Fin (r+1) × Fin (n+1))`, in which a smaller index is a larger variable, as in the paper.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), §3.1, pp.21–22

import Mathlib
import Definitions.Def_ChowFormsCH_ProjSpace

set_option autoImplicit false

namespace ChowFormsCH

/-- The set `W` of coefficient tuples `γ = (γ_{i,j})`, `0 ≤ i ≤ r`, `0 ≤ j ≤ n`, such that the
linear forms `L_{γ_i} = γ_{i,0}x₀ + ⋯ + γ_{i,n}xₙ` have a common zero on `V`
(Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH via Chow forms*,
arXiv:2611.05289, held version, sha256 75e796c6…, §3.1, p.21: `W := π₂(V_L)`, "The points of W
correspond to linear subspaces of codimension at most r + 1 that have nonempty intersection with
V"). The variable `u_{i,j}` is indexed by `(i, j) : Fin (r+1) × Fin (n+1)`. -/
def chowIncidence {n : ℕ} {K : Type*} [Field K] (V : Set (ProjSpace n K)) (r : ℕ) :
    Set (Fin (r + 1) × Fin (n + 1) → K) :=
  {γ | ∃ x ∈ V, ∀ i : Fin (r + 1), ∑ j : Fin (n + 1), γ (i, j) * x.1 j = 0}

/-- `C` is a Chow form of `V ⊆ P^n` in the `r + 1` groups of variables `u₀, …, u_r`, up to a
nonzero scalar factor (§3.1, pp.21–22): `C` is a nonzero squarefree polynomial whose zero set in
`K^{(r+1)(n+1)}` is the incidence set `W` of `chowIncidence`.

**Formalization Note** The paper defines `C_V` for an irreducible `V` of dimension `r` as a
defining equation of the hypersurface `W`, and for an equidimensional `V` as the product of the
Chow forms of its components, which is squarefree with zero set `W`. Over an algebraically closed
field a squarefree polynomial is determined by its zero set up to a nonzero scalar, so
`IsChowForm V r C` says exactly that `C` is a nonzero scalar multiple of `C_V`. For `V` empty, `W`
is empty and the Chow forms are the nonzero constants (normalized: `C_∅ = 1`, proof of Theorem 4.9,
p.34). If `V` is not equidimensional of dimension `r` (and not empty) no polynomial qualifies. -/
def IsChowForm {n : ℕ} {K : Type*} [Field K] (V : Set (ProjSpace n K)) (r : ℕ)
    (C : MvPolynomial (Fin (r + 1) × Fin (n + 1)) K) : Prop :=
  C ≠ 0 ∧ Squarefree C ∧
    ∀ γ : Fin (r + 1) × Fin (n + 1) → K, MvPolynomial.eval γ C = 0 ↔ γ ∈ chowIncidence V r

/-- The leading coefficient of `C` in the lexicographic order extending the variable order
`u_{i,j} > u_{i',j'}` iff `i < i'`, or `i = i'` and `j < j'` (§3.1, p.21).

**Formalization Note** Variables are renamed into `Lex (Fin (r+1) × Fin (n+1))`, ordered
lexicographically; Mathlib's `MonomialOrder.lex` makes a smaller variable index more significant
(`X 1 < X 0`), so `u_{0,0}` is the largest variable, as in the paper. -/
noncomputable def chowLeadCoeff {n r : ℕ} {K : Type*} [Field K]
    (C : MvPolynomial (Fin (r + 1) × Fin (n + 1)) K) : K :=
  (MonomialOrder.lex (σ := Lex (Fin (r + 1) × Fin (n + 1)))).leadingCoeff
    (MvPolynomial.rename (toLex : Fin (r + 1) × Fin (n + 1) → Lex (Fin (r + 1) × Fin (n + 1))) C)

/-- `C` is *the* (normalized) Chow form `C_V` of `V ⊆ P^n` in `r + 1` groups of variables: a Chow
form whose leading coefficient in the lexicographic order of `chowLeadCoeff` is `1` (§3.1, p.21:
"We normalize the Chow form so that its leading coefficient in the lexicographic order extending
the variable ordering is always 1"). -/
def IsNormalizedChowForm {n : ℕ} {K : Type*} [Field K] (V : Set (ProjSpace n K)) (r : ℕ)
    (C : MvPolynomial (Fin (r + 1) × Fin (n + 1)) K) : Prop :=
  IsChowForm V r C ∧ chowLeadCoeff C = 1

end ChowFormsCH


