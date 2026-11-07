-- Prove2me | Definitions.Def_CopylessCRA_zariskiClosure
-- name    : CopylessCRA_zariskiClosure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:39.247197+00:00
-- url     : https://prove2.me/theorems/6b13c283-9cb2-4a6d-a27a-400a8bd87933
-- title:
--   Zariski closure in $GL(\overline{\mathbb Q})$, identity component, unipotent elements, Jordan parts, $\Gamma_f$, $\mathcal G_f$, (C3), (C4)
-- statement:
--   Let $K$ be a field (in the paper $K=\overline{\mathbb Q}$) and $\iota$ a finite index set.
--
--   1. The *Zariski closure* of a set $S\subseteq GL_\iota(K)$ is the set of common zeros in $GL_\iota(K)$ of all polynomials in the matrix entries that vanish on $S$. A set is *Zariski closed* if it is such a zero set, and *Zariski connected* if it is nonempty and not covered by two relatively closed sets with disjoint traces on it.
--   2. The *identity component* $\mathcal G^\circ$ of $\mathcal G$ is the union of all Zariski-connected subsets of $\mathcal G$ containing $1$.
--   3. A matrix $g$ is *unipotent* if all its eigenvalues are $1$, i.e. $g-1$ is nilpotent. $u$ is *the unipotent Jordan part* of $g$ over a field $F$ if $g=su=us$ with $s$ semisimple over $F$ and $u$ unipotent.
--   4. A set of matrices over $K$ is *triangularizable over $\mathbb Q$* if some basis of $\mathbb Q^\iota$ makes all of its elements upper triangular.
--   5. For invertible rational letter matrices $M_a$: $\Gamma_f\le GL(\mathbb Q)$ is the group they generate and $\mathcal G_f\subseteq GL(\overline{\mathbb Q})$ its Zariski closure.
--   6. **(C3)**: $\mathcal G_f^\circ$ is triangularizable over $\mathbb Q$ and any two unipotent elements of $\mathcal G_f$ commute. **(C4)**: $\Gamma_f$ has a subgroup of finite index that is triangularizable over $\mathbb Q$ and in which any two elements have commuting unipotent Jordan parts (over $\mathbb Q$).
--
--   These are the algebraic conditions of Theorem 1.
--
--   **Formalization Note** The paper uses polynomials in the entries and $\det^{-1}$; on subsets of $GL$ these define the same closed sets, since $\det$ is a unit there. The definitions mirror the published `QAlgorithms.Papers.Independent.Renew46.P22.{zariskiClosure, IsZariskiClosed, IsZariskiConnected}` (stated there for `Fin n`) over any finite index type; at `Fin n` they agree (proved in `Solutions/verification/CopylessCRA_bridge.lean`). Unipotent Jordan parts are a relation, not a choice function. "Upper triangular" is with respect to the order of the new basis given by an injective labelling.
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), §1, p.1 (PDF p.3); §2.3 and (A1)–(A2), p.6 (PDF p.8); Theorem 1 (C3)–(C4), pp.1–2 (PDF pp.3–4)

import Mathlib
open Matrix

namespace CopylessCRA

/-- `ℚ̄`, the algebraic closure of `ℚ`, in which the Zariski closures of §2.3 live. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

section Zariski

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- The entries of a matrix, as a point of `K^{ι × ι}`. -/
def entries (g : Matrix ι ι K) : ι × ι → K := fun ij => g ij.1 ij.2

/-- The common zeros in `GL_ι(K)` of a set of polynomials in the entries. -/
def zeros (P : Set (MvPolynomial (ι × ι) K)) : Set (Matrix ι ι K)ˣ :=
  {g | ∀ p ∈ P, MvPolynomial.eval (entries (g : Matrix ι ι K)) p = 0}

/-- The polynomials in the entries that vanish on a set of invertible matrices. -/
def vanishing (S : Set (Matrix ι ι K)ˣ) : Set (MvPolynomial (ι × ι) K) :=
  {p | ∀ g ∈ S, MvPolynomial.eval (entries (g : Matrix ι ι K)) p = 0}

/-- The **Zariski closure** in `GL_ι(K)` of a set `S` of invertible matrices: the set of common zeros
in `GL_ι(K)` of all polynomials that vanish on `S`. Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register
Automata and Algebraic Groups*, STOC 2027 submission (manuscript sha256 434d3094…), §2.3, p.6
(PDF p.8), with `K = ℚ̄`.

**Formalization Note** The paper uses polynomials in the entries and `det⁻¹`. On subsets of `GL`
the two closures coincide (multiply a polynomial in the entries and `det⁻¹` by a power of `det`,
which is a unit on `GL`), so only polynomials in the entries are used, as in the published
definition `QAlgorithms.Papers.Independent.Renew46.P22.zariskiClosure` (stated there for `Fin n`;
here for any finite index type). -/
def zariskiClosure (S : Set (Matrix ι ι K)ˣ) : Set (Matrix ι ι K)ˣ :=
  zeros (vanishing S)

/-- A subset of `GL_ι(K)` is **Zariski closed** (relative to `GL`) if it is the common zero set of
some set of polynomials in the entries. -/
def IsZariskiClosed (S : Set (Matrix ι ι K)ˣ) : Prop :=
  ∃ P : Set (MvPolynomial (ι × ι) K), S = zeros P

/-- A subset of `GL_ι(K)` is **Zariski connected**: nonempty, and not separated by two relatively
closed subsets (the subspace topology induced by the Zariski topology). -/
def IsZariskiConnected (S : Set (Matrix ι ι K)ˣ) : Prop :=
  S.Nonempty ∧ ∀ U V : Set (Matrix ι ι K)ˣ, IsZariskiClosed U → IsZariskiClosed V →
    S ⊆ U ∪ V → S ∩ U ∩ V = ∅ → S ⊆ U ∨ S ⊆ V

/-- The **identity component** `𝒢°` of a set `𝒢 ⊆ GL_ι(K)`: the connected component of `1` for the
Zariski topology, i.e. the union of all Zariski-connected subsets of `𝒢` containing `1`.

**Formalization Note** This is the topological definition; that `𝒢°` is a closed normal subgroup of
finite index whose cosets are the irreducible components (fact (A1), p.6) is a theorem, not part of
the definition. -/
def identityComponent (G : Set (Matrix ι ι K)ˣ) : Set (Matrix ι ι K)ˣ :=
  ⋃₀ {C | C ⊆ G ∧ (1 : (Matrix ι ι K)ˣ) ∈ C ∧ IsZariskiConnected C}

end Zariski

/-- A square matrix is **unipotent** if all its eigenvalues are `1` (p.4), i.e. `g − 1` is
nilpotent. -/
def IsUnipotent {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R] (g : Matrix ι ι R) : Prop :=
  IsNilpotent (g - 1)

/-- `u` is **the unipotent Jordan part** of `g` over the field `F` (fact (A2), p.6): `g = s u = u s`
with `s` semisimple over `F` and `u` unipotent.

**Formalization Note** A relation, not a choice function: the multiplicative Jordan decomposition of
an invertible matrix over a perfect field is unique, so for invertible `g` exactly one `u` satisfies
it. -/
def IsUnipotentJordanPart {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (g u : Matrix ι ι F) : Prop :=
  ∃ s : Matrix ι ι F, Module.End.IsSemisimple (Matrix.toLin' s) ∧ IsUnipotent u ∧ Commute s u ∧ g = s * u

section Rational

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [Algebra ℚ K]

/-- A rational matrix viewed over `K`. -/
def castMat (A : Matrix ι ι ℚ) : Matrix ι ι K := A.map (algebraMap ℚ K)

/-- The inclusion `GL_ι(ℚ) → GL_ι(K)`. -/
def toGLK : (Matrix ι ι ℚ)ˣ →* (Matrix ι ι K)ˣ :=
  Units.map (RingHom.mapMatrix (algebraMap ℚ K)).toMonoidHom

/-- A set of matrices over `K` is **triangularizable over `ℚ`** (§1, p.1): some basis of `ℚ^ι`
makes all of its elements upper triangular. The basis is the columns of a rational invertible `P`,
listed in the order given by the injective labelling `b`; "upper triangular" is
`(P⁻¹ g P)_{ij} = 0` whenever `b j < b i`. -/
def IsTriangularizableQ (S : Set (Matrix ι ι K)ˣ) : Prop :=
  ∃ (P : (Matrix ι ι ℚ)ˣ) (b : ι → ℕ), Function.Injective b ∧
    ∀ g ∈ S, (castMat (K := K) (↑P⁻¹ : Matrix ι ι ℚ) * (g : Matrix ι ι K) *
      castMat (K := K) (↑P : Matrix ι ι ℚ)).BlockTriangular b

end Rational

section Groups

variable {α ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Γ_f ≤ GL(ℚ)`: the group generated by the (invertible) letter matrices `M_a` (§1, p.1). -/
def letterGroup (M : α → Matrix ι ι ℚ) : Subgroup (Matrix ι ι ℚ)ˣ :=
  Subgroup.closure {g | ∃ a, (g : Matrix ι ι ℚ) = M a}

/-- `𝒢_f ⊆ GL(ℚ̄)`: the Zariski closure of `Γ_f` (§1, p.1; §2.3, p.6). -/
def zariskiGroup (M : α → Matrix ι ι ℚ) : Set (Matrix ι ι Qbar)ˣ :=
  zariskiClosure (toGLK '' (letterGroup M : Set (Matrix ι ι ℚ)ˣ))

/-- Condition **(C3)** of Theorem 1 (p.1, PDF p.3) for the letter matrices `M`: `𝒢°_f` is
triangularizable over `ℚ`, and any two unipotent elements of `𝒢_f` commute. -/
def C3 (M : α → Matrix ι ι ℚ) : Prop :=
  IsTriangularizableQ (identityComponent (zariskiGroup M)) ∧
  ∀ g ∈ zariskiGroup M, ∀ h ∈ zariskiGroup M, IsUnipotent (g : Matrix ι ι Qbar) →
    IsUnipotent (h : Matrix ι ι Qbar) → Commute (g : Matrix ι ι Qbar) (h : Matrix ι ι Qbar)

/-- Condition **(C4)** of Theorem 1 (p.2, PDF p.4): `Γ_f` has a subgroup `Γ₁` of finite index that
is triangularizable over `ℚ` and in which any two elements have commuting unipotent Jordan parts
(Jordan parts over `ℚ`). -/
def C4 (M : α → Matrix ι ι ℚ) : Prop :=
  ∃ Γ₁ : Subgroup (Matrix ι ι ℚ)ˣ, Γ₁ ≤ letterGroup M ∧
    (Γ₁.subgroupOf (letterGroup M)).FiniteIndex ∧
    IsTriangularizableQ (toGLK (K := Qbar) '' (Γ₁ : Set (Matrix ι ι ℚ)ˣ)) ∧
    ∀ g ∈ Γ₁, ∀ h ∈ Γ₁, ∀ ug uh : Matrix ι ι ℚ,
      IsUnipotentJordanPart (g : Matrix ι ι ℚ) ug → IsUnipotentJordanPart (h : Matrix ι ι ℚ) uh →
        Commute ug uh

end Groups

end CopylessCRA


