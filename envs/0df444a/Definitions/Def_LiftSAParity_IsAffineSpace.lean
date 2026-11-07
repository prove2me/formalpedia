-- Prove2me | Definitions.Def_LiftSAParity_IsAffineSpace
-- name    : LiftSAParity_IsAffineSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:51.114498+00:00
-- url     : https://prove2.me/theorems/f8f90339-4c3e-4cd7-a27f-4805f8abcfb0
-- title:
--   Linear forms, affine spaces and codimension over $\mathbb F_2$
-- statement:
--   Points are vectors $y\in\mathbb F_2^V$. A **linear form** with support $S\subseteq V$ is $f_S(y)=\sum_{v\in S}y_v=\bigoplus_{v\in S}y_v$ (eq. (1)). An **affine space** is a set of the form
--   $$A=\{y\in\mathbb F_2^V: f_1(y)=b_1,\dots,f_k(y)=b_k\} \tag{3}$$
--   for linear forms $f_1,\dots,f_k$ and bits $b_1,\dots,b_k$. For nonempty $A$ the **codimension** (rank) $\operatorname{cd}A=\operatorname{rk}A$ is the number of independent defining equations, equivalently $|V|-\dim A_{\mathrm{hom}}$ where $A_{\mathrm{hom}}$ is the direction space. A linear form is **constant on** $A$ if $f(x)=f(y)$ for all $x,y\in A$. The **slices** of $A$ by $f$ are $A\cap\{f=0\}$ and $A\cap\{f=1\}$. For a clause $C$, $A_C$ is the set of points that falsify $C$, a subcube of codimension $|\mathrm{vars}(C)|$.
--
--   **Formalization Note** The empty set is an affine space in the sense of (3); the theorems of the mission require nonemptiness wherever the paper does. Codimension is $|V|-\dim\operatorname{vectorSpan}(A)$, meaningful for nonempty $A$. A literal $(v,b)$ is true at $y$ when $y_v=b$ with $1=$ true.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §2, p.7, eqs. (1), (3)

import Mathlib
import Definitions.Def_LiftSAParity_CNF

namespace LiftSAParity

/-- The bit `b` as an element of `𝔽₂ = ZMod 2`: `true ↦ 1`, `false ↦ 0`. -/
def ofBool (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The **linear form** with support `S` (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams
Degree to Unary Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §2, p.7,
eq. (1)): `f_S(y) = ∑_{v ∈ S} y_v` over `𝔽₂`, i.e. the parity `⊕_{v∈S} y_v`. -/
def parity {V : Type*} (S : Finset V) (y : V → ZMod 2) : ZMod 2 :=
  ∑ v ∈ S, y v

/-- **Affine space** (§2, p.7, eq. (3)): "An affine space is a linear space translated by some
offset, that is, it is a set of the form A = {x ∈ F₂^{n×ℓ} : f₁(x) = b₁, . . . , f_k(x) = b_k} for
linear forms f₁, . . . , f_k and b₁, . . . , b_k ∈ {0, 1}."

**Formalization Note** Points are `V → ZMod 2`, a linear form is given by its support
`S t : Finset V`. The empty set is an affine space in this sense (an inconsistent system); the
theorems of the mission say `A.Nonempty` wherever the paper's "affine space" means a nonempty one. -/
def IsAffineSpace {V : Type*} (A : Set (V → ZMod 2)) : Prop :=
  ∃ (k : ℕ) (S : Fin k → Finset V) (b : Fin k → ZMod 2),
    A = {y | ∀ t, parity (S t) y = b t}

/-- **Codimension** (rank) of an affine space (§2, p.7): "If A is nonempty and f₁, . . . , f_k are
linearly independent, then the codimension of A is cd A = k we also call this the rank of A, and
write rk A." Computed as `|V| − dim A_hom`, where the direction space `A_hom` is the vector span of
`A`; for a nonempty affine space this equals the number of independent defining equations.

**Formalization Note** The value is meaningful only for nonempty `A`, which is how every theorem
of the mission uses it (for `∅` it returns `|V|`). -/
noncomputable def codim {V : Type*} [Fintype V] (A : Set (V → ZMod 2)) : ℕ :=
  Fintype.card V - Module.finrank (ZMod 2) (vectorSpan (ZMod 2) A)

/-- The linear form `f_S` is **constant on** `A` (§2, p.7): "A linear form f is constant on A if
f(x) = f(y) for all x, y ∈ A." -/
def IsConstOn {V : Type*} (S : Finset V) (A : Set (V → ZMod 2)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, parity S x = parity S y

/-- The slice `A ∩ {y : f_S(y) = b}` of `A` by the linear form `f_S` (Lemma 3.4 (2), p.12;
§4.2, p.16). -/
def slice {V : Type*} (A : Set (V → ZMod 2)) (S : Finset V) (b : ZMod 2) : Set (V → ZMod 2) :=
  A ∩ {y | parity S y = b}

/-- `A_C` (§2, p.7): "for a clause C we write A_C for the set of assignments that falsify C." A
point `y` falsifies `C` when every literal `(v, b) ∈ C` is false: `y_v ≠ b` (with `true = 1`). -/
def falsifySpace {V : Type*} (C : Clause V) : Set (V → ZMod 2) :=
  {y | ∀ l ∈ C, y l.1 ≠ ofBool l.2}

end LiftSAParity


