-- Prove2me | Definitions.Def_ConsModCount_NormalForm
-- name    : ConsModCount_NormalForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:57.372262+00:00
-- url     : https://prove2.me/theorems/64c56fa6-a544-4110-b7ac-e228fb808a23
-- title:
--   Congruences, SI algebras, $\mathrm{Lin}_C$ and unique-extension definitions
-- statement:
--   Fix a conservative minority operation $m$ on $D$; every subset of $D$ is a subalgebra of $(D;m)$.
--
--   1. A **congruence** of a subalgebra $A$ is an equivalence relation on $A$ preserved by $m$; $0$ is equality.
--   2. $A$ is **subdirectly irreducible (SI)** if $|A|\ge2$ and its nonzero congruences have a least element, the **monolith**.
--   3. $C$ has a **two-element monolith block** $B=\{0,1\}$ if $C$ is SI and its monolith is the congruence $\theta_B$ whose only nonsingleton class is $B$, $|B|=2$.
--   4. The **enclosed parity relation** (3) is $\mathrm{Lin}_C=\{(a,b,c)\in B^3:a\oplus b\oplus c=1\}\cup\{(u,u,u):u\in C\setminus B\}$.
--   5. A **definition with introduced variables** of a relation $R\subseteq A_1\times\cdots\times A_k$ is a conjunction of atoms over the $k$ free variables and $m$ introduced variables with actual domains; the atoms are unary subsets, graphs of surjective homomorphisms $A\to U$, graphs of isomorphisms $A\to U$, and relations $\mathrm{Lin}_C$. It has **unique extension** if every tuple of $R$ has exactly one assignment of the introduced variables satisfying all atoms, and every tuple of $A_1\times\cdots\times A_k$ outside $R$ has none.
--
--   These notions state the count-preserving normal form of Lemma 4.
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §2, pp.3–4 (PDF pp.4–5): congruence, SI, monolith, (3) Lin_C, unique extension; Lemma 4, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_ConsModCount_Polymorphism

set_option autoImplicit false

namespace ConsModCount

/-! Algebraic preliminaries of Xie, §2, pp.3–4 (PDF pp.4–5), for one fixed conservative minority
algebra `(D; m)`: every subset of `D` is a subalgebra; congruences, homomorphisms and subdirect
irreducibility refer to this algebra and its subalgebras. -/

/-- `θ` is a **congruence** of the subalgebra `A ⊆ D` of `(D; m)`: an equivalence relation on `A`
(relating only elements of `A`) preserved by `m`. Xie, p.3 (PDF p.4): "A congruence is an
equivalence relation preserved by m." -/
def IsCongr {D : Type} (m : D → D → D → D) (A : Set D) (θ : D → D → Prop) : Prop :=
  (∀ a b, θ a b → a ∈ A ∧ b ∈ A) ∧ (∀ a ∈ A, θ a a) ∧ (∀ a b, θ a b → θ b a) ∧
    (∀ a b c, θ a b → θ b c → θ a c) ∧
    ∀ a b c a' b' c', θ a a' → θ b b' → θ c c' → θ (m a b c) (m a' b' c')

/-- The equality congruence `0` of `A`. -/
def zeroCongr {D : Type} (A : Set D) : D → D → Prop := fun a b => a ∈ A ∧ a = b

/-- A finite subalgebra `A` is **subdirectly irreducible (SI)**: it is nontrivial (at least two
elements) and its nonzero congruences have a least element, the monolith. Xie, p.3 (PDF p.4). -/
def IsSI {D : Type} (m : D → D → D → D) (A : Set D) : Prop :=
  2 ≤ A.ncard ∧ ∃ μ : D → D → Prop, IsCongr m A μ ∧ μ ≠ zeroCongr A ∧
    ∀ θ, IsCongr m A θ → θ ≠ zeroCongr A → ∀ a b, μ a b → θ a b

/-- The block congruence `θ_B` of `C` whose only nonsingleton class is `B ⊆ C`. -/
def blockCongr {D : Type} (C B : Set D) : D → D → Prop :=
  fun a b => a ∈ C ∧ b ∈ C ∧ (a = b ∨ (a ∈ B ∧ b ∈ B))

/-- `C` is an SI subalgebra whose **monolith has the two-element block** `B`: `|B| = 2`, `B ⊆ C`,
`C` is SI and its monolith is `θ_B` (i.e. `θ_B` is a congruence contained in every nonzero
congruence of `C`). Xie, p.3 (PDF p.4). -/
def HasTwoElementMonolithBlock {D : Type} (m : D → D → D → D) (C B : Set D) : Prop :=
  B ⊆ C ∧ B.ncard = 2 ∧ IsSI m C ∧ IsCongr m C (blockCongr C B) ∧
    ∀ θ, IsCongr m C θ → θ ≠ zeroCongr C → ∀ a b, blockCongr C B a b → θ a b

/-- The **enclosed parity relation** (3) of `C` with two-element monolith block `B`, the elements
of `B` named `0, 1` by the labelling `lab`:
`Lin_C = {(a, b, c) ∈ B³ : a ⊕ b ⊕ c = 1} ∪ {(u, u, u) : u ∈ C \ B}`. Xie, (3), p.3 (PDF p.4). -/
def LinRel {D : Type} (C B : Set D) (lab : D → ZMod 2) (a b c : D) : Prop :=
  (a ∈ B ∧ b ∈ B ∧ c ∈ B ∧ lab a + lab b + lab c = 1) ∨ (a ∈ C \ B ∧ b = a ∧ c = a)

/-- `f` is a **homomorphism** on the subalgebra `A`: it commutes with `m` on `A`. -/
def IsSubHom {D : Type} (m : D → D → D → D) (A : Set D) (f : D → D) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, f (m a b c) = m (f a) (f b) (f c)

/-- The atoms of the normal form of Lemma 4 (Xie, p.4, PDF p.5), over variables `V`: a unary subset
`U(x)`; the graph `y = f(x)` of a map `f` on `A` with image `U` (a surjective homomorphism graph or
an isomorphism graph); and a relation `Lin_C(x, y, z)`. -/
inductive NFAtom (D V : Type) : Type
  | unary (U : Set D) (x : V) : NFAtom D V
  | homGraph (A U : Set D) (f : D → D) (x y : V) : NFAtom D V
  | isoGraph (A U : Set D) (f : D → D) (x y : V) : NFAtom D V
  | lin (C B : Set D) (lab : D → ZMod 2) (x y z : V) : NFAtom D V

/-- Truth of an atom under an assignment `σ`. -/
def NFAtom.Holds {D V : Type} (σ : V → D) : NFAtom D V → Prop
  | NFAtom.unary U x => σ x ∈ U
  | NFAtom.homGraph A _ f x y => σ x ∈ A ∧ σ y = f (σ x)
  | NFAtom.isoGraph A _ f x y => σ x ∈ A ∧ σ y = f (σ x)
  | NFAtom.lin C B lab x y z => LinRel C B lab (σ x) (σ y) (σ z)

/-- An atom is **of the allowed kind** for `(D; m)`: a surjective homomorphism graph is the graph of
a homomorphism of `A` onto `U`; an isomorphism graph is the graph of an injective homomorphism of
`A` onto `U`; a `Lin_C` atom has `B` a two-element monolith block of `C`, labelled injectively. -/
def NFAtom.WF {D V : Type} (m : D → D → D → D) : NFAtom D V → Prop
  | NFAtom.unary _ _ => True
  | NFAtom.homGraph A U f _ _ => IsSubHom m A f ∧ f '' A = U
  | NFAtom.isoGraph A U f _ _ => IsSubHom m A f ∧ Set.InjOn f A ∧ f '' A = U
  | NFAtom.lin C B lab _ _ _ => HasTwoElementMonolithBlock m C B ∧ Set.InjOn lab B

/-- Every set (a domain of a map or an ambient `C`) occurring in an atom has at most `d` elements.
Unary atoms impose nothing. -/
def NFAtom.SetsBounded {D V : Type} (d : ℕ) : NFAtom D V → Prop
  | NFAtom.unary _ _ => True
  | NFAtom.homGraph A U _ _ _ => A.ncard ≤ d ∧ U.ncard ≤ d
  | NFAtom.isoGraph A U _ _ _ => A.ncard ≤ d ∧ U.ncard ≤ d
  | NFAtom.lin C _ _ _ _ _ => C.ncard ≤ d

/-- A conjunctive **definition with introduced variables** of a `k`-ary relation: `m` introduced
(auxiliary) variables with actual domains `dom j ⊆ D`, and a finite list of atoms over the `k + m`
variables (free variables first). -/
structure NFDef (D : Type) (k : ℕ) where
  /-- The number of introduced variables. -/
  m : ℕ
  /-- The actual domain of each introduced variable. -/
  dom : Fin m → Set D
  /-- The atoms. -/
  atoms : List (NFAtom D (Fin (k + m)))

/-- The definition has **unique extension** and defines `R` on `A₁ × ⋯ × A_k`: every tuple of
`R` has exactly one assignment to the introduced variables (within their domains) satisfying all
atoms, and every tuple of `A₁ × ⋯ × A_k` outside `R` has none. Xie, p.4 (PDF p.5). -/
def NFDef.UniquelyDefines {D : Type} {k : ℕ} (Φ : NFDef D k) (A : Fin k → Set D)
    (R : Set (Fin k → D)) : Prop :=
  ∀ a : Fin k → D, (∀ i, a i ∈ A i) →
    (a ∈ R → ∃! b : Fin Φ.m → D, (∀ j, b j ∈ Φ.dom j) ∧ ∀ at' ∈ Φ.atoms, at'.Holds (Fin.append a b)) ∧
    (a ∉ R → ∀ b : Fin Φ.m → D, (∀ j, b j ∈ Φ.dom j) → ¬ ∀ at' ∈ Φ.atoms, at'.Holds (Fin.append a b))

end ConsModCount


