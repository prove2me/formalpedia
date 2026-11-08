-- Prove2me | Definitions.Def_FunctionAlgebras_defs
-- name    : FunctionAlgebras_defs
-- status  : Definition
-- author  : @Alien60
-- created : 2026-11-07T16:58:17.445925+00:00
-- url     : https://prove2.me/theorems/536d90ff-9951-4216-85fd-cfb039009b8e
-- title:
--   Clones, polymorphisms, invariant relations, pp-definitions, near-unanimity operations
-- statement:
--   Operations on $A$ are maps `(Fin n → A) → A` ($n\ge0$); relations are sets of tuples `Fin h → A` (or `ι → A`). `Preserves f R`: for any $n$ tuples of $R$, applying $f$ coordinatewise gives a tuple of $R$. `IsClone C`: $C$ contains all projections and is closed under composition. `Pol Q`: operations preserving every relation of $Q$; `Inv F`: relations preserved by every operation of $F$. `PPFormula Q h`: a primitive positive formula with $h$ free and $k$ bound variables, relational atoms from $Q$ and equality atoms; `toRel` is the relation it defines. `IsRelClone Q`: $Q$ contains every relation pp-definable from $Q$. `IsNearUnanimity m`: $m(x,\dots,x,y,x,\dots,x)=x$ for every position of $y$. `Interpolates C f E`: some $p\in C_n$ agrees with $f$ on $E$.
-- source:
--   D. Lau, Function Algebras on Finite Sets, Springer Monographs in Mathematics, 2006, https://doi.org/10.1007/3-540-36023-9, Part II, Sections 1.1, 2.1-2.6, 8.3; K. A. Baker, A. F. Pixley, Polynomial interpolation and the Chinese remainder theorem for algebraic systems, Math. Z. 143 (1975) 165-174, https://doi.org/10.1007/BF01187059, Sections 2-3

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.TFAE
import Mathlib.Logic.Function.Basic

/-!
# Clones, relations and the Pol–Inv connection on a set
(D. Lau, *Function Algebras on Finite Sets*, Springer 2006, Part II, Ch. 2 and §8.3;
K. A. Baker and A. F. Pixley, Math. Z. 143 (1975) 165–174)

Setting.  `A` is a type (the base set `E_k`; theorems add `[Finite A]` where the source needs a
finite set).

* An `n`-ary operation on `A` is a map `(Fin n → A) → A`.  A *family of operations* is
  `F : ∀ n : ℕ, Set ((Fin n → A) → A)` (its `n`-ary members are `F n`).  Nullary operations are
  allowed (Lau uses arities `n ≥ 1`; see the note on `IsRelClone`).
* An `h`-ary relation is a set `R : Set (Fin h → A)` of `h`-tuples; a *family of relations* is
  `Q : ∀ h : ℕ, Set (Set (Fin h → A))`.  Relations on an arbitrary coordinate type `ι` are
  sets `R : Set (ι → A)`.
* `Preserves f R` (Lau §2.6): applying the `n`-ary `f` coordinatewise to any `n` tuples of `R`
  (the rows `rows j`, `j < n`) gives a tuple of `R`.  Equivalently, `R` is a subuniverse of the
  power `(A; f)^ι`.
* `IsClone C` (Lau Part II §1.1–1.2; BP "polynomial functions" of an algebra = its term
  operations): `C` contains all projections and is closed under composition
  `f(g₀,…,g_{n-1})`.
* `Pol Q` (polymorphisms) and `Inv F` (invariant relations), Lau §2.6.
* `PPFormula Q h` is a primitive positive formula over relations of `Q` with `h` free
  variables: `k` existentially quantified variables, `t` relational atoms `rel j (scope j)` and
  `e` equality atoms `eqL l = eqR l`; `PPFormula.toRel` is the `h`-ary relation it defines.
* `IsRelClone Q` (a *co-clone* / relational clone): `Q` contains every relation that is
  primitive-positively definable from relations of `Q`.  This is the closure notion of Lau
  §2.4 (closure under the elementary relation operations and the diagonal `Δ`), in the
  standard equivalent form (Lau Thm 2.5.1; Geiger 1968).  Because nullary operations are
  allowed, no separate convention about the empty relation is needed.
* `IsNearUnanimity m` (Lau §8.3 `d_m`; BP §2): the `(d+1)`-ary `m` returns `x` whenever all
  arguments but at most one are equal to `x`.
-/

universe u

namespace FunctionAlgebras

variable {A : Type u}

/-- `f` preserves `R`: for any `n` tuples `rows 0, …, rows (n-1)` of `R`, the tuple obtained by
applying `f` coordinatewise, `i ↦ f (fun j => rows j i)`, again lies in `R` (Lau §2.6). -/
def Preserves {n : ℕ} {ι : Type*} (f : (Fin n → A) → A) (R : Set (ι → A)) : Prop :=
  ∀ rows : Fin n → ι → A, (∀ j, rows j ∈ R) → (fun i => f (fun j => rows j i)) ∈ R

/-- `C` is a clone: it contains every projection `x ↦ x i` and is closed under composition
`x ↦ f (g 0 x, …, g (n-1) x)`. -/
def IsClone (C : ∀ n : ℕ, Set ((Fin n → A) → A)) : Prop :=
  (∀ (n : ℕ) (i : Fin n), (fun x : Fin n → A => x i) ∈ C n) ∧
  (∀ (n m : ℕ) (f : (Fin n → A) → A) (g : Fin n → (Fin m → A) → A),
    f ∈ C n → (∀ j, g j ∈ C m) → (fun x => f (fun j => g j x)) ∈ C m)

/-- `Pol Q`: the operations preserving every relation of `Q` (Lau §2.6). -/
def Pol (Q : ∀ h : ℕ, Set (Set (Fin h → A))) : ∀ n : ℕ, Set ((Fin n → A) → A) :=
  fun n => {f | ∀ (h : ℕ), ∀ R ∈ Q h, Preserves f R}

/-- `Inv F`: the relations preserved by every operation of `F` (Lau §2.6); `Inv F h` is the set
of `h`-ary invariants (Lau's `Inv_h F`). -/
def Inv (F : ∀ n : ℕ, Set ((Fin n → A) → A)) : ∀ h : ℕ, Set (Set (Fin h → A)) :=
  fun h => {R | ∀ (n : ℕ), ∀ f ∈ F n, Preserves f R}

/-- A primitive positive formula with `h` free variables over the relations of `Q`:
`∃ y₀ … y_{k-1}, ⋀_{j<t} rel j (scope j) ∧ ⋀_{l<e} (eqL l = eqR l)`, where variables are
`Sum.inl i` (free, `i < h`) or `Sum.inr i` (bound, `i < k`). -/
structure PPFormula (Q : ∀ h : ℕ, Set (Set (Fin h → A))) (h : ℕ) where
  /-- number of existentially quantified variables -/
  k : ℕ
  /-- number of relational atoms -/
  t : ℕ
  /-- arity of each relational atom -/
  ar : Fin t → ℕ
  /-- the relation of each atom -/
  rel : ∀ j, Set (Fin (ar j) → A)
  rel_mem : ∀ j, rel j ∈ Q (ar j)
  /-- the variables each atom is applied to -/
  scope : ∀ j, Fin (ar j) → Fin h ⊕ Fin k
  /-- number of equality atoms -/
  e : ℕ
  /-- left and right variables of each equality atom -/
  eqL : Fin e → Fin h ⊕ Fin k
  eqR : Fin e → Fin h ⊕ Fin k

/-- The `h`-ary relation defined by a primitive positive formula. -/
def PPFormula.toRel {Q : ∀ h : ℕ, Set (Set (Fin h → A))} {h : ℕ} (φ : PPFormula Q h) :
    Set (Fin h → A) :=
  {x | ∃ y : Fin φ.k → A,
    (∀ j, (fun i => Sum.elim x y (φ.scope j i)) ∈ φ.rel j) ∧
    (∀ l, Sum.elim x y (φ.eqL l) = Sum.elim x y (φ.eqR l))}

/-- `Q` is a relational clone (co-clone): it contains every relation primitive-positively
definable from its members. -/
def IsRelClone (Q : ∀ h : ℕ, Set (Set (Fin h → A))) : Prop :=
  ∀ (h : ℕ) (φ : PPFormula Q h), φ.toRel ∈ Q h

/-- `m` is a `(d+1)`-ary near-unanimity operation: `m(x,…,x,y,x,…,x) = x` for every position
`i` of the lone `y` (Lau §8.3, BP §2). -/
def IsNearUnanimity {d : ℕ} (m : (Fin (d + 1) → A) → A) : Prop :=
  ∀ (i : Fin (d + 1)) (x y : A), m (Function.update (fun _ => x) i y) = x

/-- The partial function `f` (only its values on `E` matter) is *interpolated on `E`* by a
member of `C n`: some `p ∈ C n` agrees with `f` on `E` (BP §2, "interpolating polynomial"). -/
def Interpolates {n : ℕ} (C : ∀ n : ℕ, Set ((Fin n → A) → A)) (f : (Fin n → A) → A)
    (E : Set (Fin n → A)) : Prop :=
  ∃ p ∈ C n, ∀ x ∈ E, p x = f x

end FunctionAlgebras


