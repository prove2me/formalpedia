-- Prove2me | Definitions.Def_CSPIdealMem_Polymorphism
-- name    : CSPIdealMem_Polymorphism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:27:57.067658+00:00
-- url     : https://prove2.me/theorems/ed4e50c6-f664-4138-b945-0b6265f224fb
-- title:
--   Polymorphisms, Taylor and cyclic operations, endomorphisms, cores, Taylor subdomains, covered endomorphisms
-- statement:
--   Let $\Gamma$ be a constraint language on $D$.
--
--   1. A $k$-ary operation $t:D^k\to D$ is a **polymorphism** of $\Gamma$ if applying it coordinatewise to any $k$ tuples of a relation of $\Gamma$ gives a tuple of that relation. It is **idempotent** if $t(a,\dots,a)=a$ for all $a$.
--   2. An idempotent $t$ is a **Taylor operation** if for every position $i\in\{1,\dots,k\}$ there are words $u,v\in\{x,y\}^k$ with $u_i=x$, $v_i=y$ and $t(u)=t(v)$ for every substitution of domain values for $x,y$. $\Gamma$ **has a Taylor polymorphism** if some polymorphism of arity $k\ge1$ is a Taylor operation.
--   3. $t:D^p\to D$ with $p\ge2$ is **cyclic** if $t(a_1,a_2,\dots,a_p)=t(a_2,\dots,a_p,a_1)$. $t$ **preserves** a relation $R\subseteq D^X$ of assignments if $t(\varphi_1,\dots,\varphi_k)$, computed pointwise, lies in $R$ whenever all $\varphi_j$ do.
--   4. An **endomorphism** is a unary polymorphism; $M=\mathrm{End}(\Gamma)$. $\Gamma$ is a **core** if every endomorphism is injective. The **principal left ideal** of $e\in M$ is $Me=\{u\circ e: u\in M\}$.
--   5. A nonempty $A\subseteq D$ is a **Taylor subdomain** if $(\Gamma|_A)^*$ has a Taylor polymorphism. An endomorphism $e$ is **covered** if $e(D)\subseteq A$ for some Taylor subdomain $A$ (which may be larger than $e(D)$). $E$ denotes the set of covered endomorphisms.
--
--   **Formalization Note** A $k$-ary operation is a map `(Fin k → α) → α`; the words $u,v$ are Boolean vectors with `false` for $x$ and `true` for $y$. Cyclicity is $t(a)=t(a\circ\mathrm{rot})$ with `finRotate p` sending $j$ to $j+1 \bmod p$, so $a\circ\mathrm{rot}=(a_2,\dots,a_p,a_1)$.
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), polymorphisms and Taylor operations, p.3 (PDF 3); endomorphisms, Taylor subdomains, covered maps, p.4 (PDF 4); cyclic operations, p.12 (PDF 12); cores, p.34 (PDF 34); Me, p.35 (PDF 35)

import Mathlib
import Definitions.Def_CSPIdealMem_ConstraintLanguage

namespace CSPIdealMem

/-! # Polymorphisms, Taylor operations, endomorphisms, cores, Taylor subdomains, covered maps

Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109): polymorphisms, idempotent and
Taylor operations, p.3 (PDF 3); endomorphisms, Taylor subdomains, covered endomorphisms, p.4
(PDF 4); cyclic operations, p.12 (PDF 12); preservation of an assignment relation, p.12–13;
cores, p.34 (PDF 34); principal left ideals `Me`, p.35 (PDF 35).

**Formalization Note.** A `k`-ary operation is a map `(Fin k → α) → α`. The two words
`u, v ∈ {x, y}^k` of the Taylor condition are Boolean vectors (`false` = `x`, `true` = `y`).
Subsets `A ⊆ D` of the domain are `Finset`s. -/

variable {α : Type}

/-- `t : α^k → α` is a polymorphism of `Γ` (p.3): applied coordinatewise to any `k` tuples
`r 0, …, r (k-1)` of a relation of `Γ`, it produces a tuple of that relation. -/
def IsPolymorphism (Γ : ConstraintLanguage α) {k : ℕ} (t : (Fin k → α) → α) : Prop :=
  ∀ (i : Γ.ι) (r : Fin k → Fin (Γ.arity i) → α), (∀ j, r j ∈ Γ.rel i) →
    (fun l => t (fun j => r j l)) ∈ Γ.rel i

/-- `t` is idempotent (p.3): `t(a, …, a) = a` for every `a`. -/
def IsIdempotent {k : ℕ} (t : (Fin k → α) → α) : Prop :=
  ∀ a : α, t (fun _ => a) = a

/-- `t` is a Taylor operation (p.3): it is idempotent and, for every position `i`, there are words
`u, v ∈ {x, y}^k` with `u_i = x`, `v_i = y` and `t(u) = t(v)` for every substitution of domain
values for `x, y`. Here `x ↔ false`, `y ↔ true`. -/
def IsTaylorOp {k : ℕ} (t : (Fin k → α) → α) : Prop :=
  IsIdempotent t ∧ ∀ i : Fin k, ∃ u v : Fin k → Bool, u i = false ∧ v i = true ∧
    ∀ x y : α, t (fun j => if u j then y else x) = t (fun j => if v j then y else x)

/-- `Γ` has a Taylor polymorphism (p.3): a polymorphism of some arity `k ≥ 1` that is a Taylor
operation. -/
def HasTaylorPolymorphism (Γ : ConstraintLanguage α) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ∃ t : (Fin k → α) → α, IsPolymorphism Γ t ∧ IsTaylorOp t

/-- `t : α^p → α` is cyclic (p.12): `p ≥ 2` and `t(a_1, a_2, …, a_p) = t(a_2, …, a_p, a_1)`.
With 0-indexed tuples, `(a ∘ finRotate p) j = a (j + 1 mod p)`, i.e. `a ∘ finRotate p` is the
tuple `(a_2, …, a_p, a_1)`. -/
def IsCyclic {p : ℕ} (t : (Fin p → α) → α) : Prop :=
  2 ≤ p ∧ ∀ a : Fin p → α, t a = t (a ∘ finRotate p)

/-- `t : α^k → α` preserves the relation `R ⊆ α^X` on assignments (p.12): applying `t`
coordinatewise to any `k` members `φ_1, …, φ_k` of `R`, `t(φ_1, …, φ_k)(x) = t(φ_1(x), …, φ_k(x))`,
gives a member of `R`. -/
def PreservesRel {X : Type} {k : ℕ} (t : (Fin k → α) → α) (R : Set (X → α)) : Prop :=
  ∀ φ : Fin k → X → α, (∀ j, φ j ∈ R) → (fun x => t (fun j => φ j x)) ∈ R

/-- `e : α → α` is an endomorphism of `Γ` (p.4): a unary polymorphism, i.e. `e` maps every tuple
of every relation of `Γ` (coordinatewise) to a tuple of the same relation. -/
def IsEndomorphism (Γ : ConstraintLanguage α) (e : α → α) : Prop :=
  ∀ (i : Γ.ι), ∀ r ∈ Γ.rel i, e ∘ r ∈ Γ.rel i

/-- `Γ` is a core (p.34): every endomorphism of `Γ` is injective. -/
def IsCore (Γ : ConstraintLanguage α) : Prop :=
  ∀ e : α → α, IsEndomorphism Γ e → Function.Injective e

/-- `A` is a Taylor subdomain of `Γ` (p.4): `A` is nonempty and the singleton expansion
`(Γ|A)*` of the induced language on `A` has a Taylor polymorphism. -/
def IsTaylorSubdomain (Γ : ConstraintLanguage α) (A : Finset α) : Prop :=
  A.Nonempty ∧ HasTaylorPolymorphism ((Γ.restrict A).withPins Finset.univ)

/-- `e` is a covered endomorphism of `Γ` (p.4): an endomorphism whose image is contained in some
Taylor subdomain `A` (a Taylor cover of `e`; it may strictly contain `e(D)`). -/
def IsCovered (Γ : ConstraintLanguage α) (e : α → α) : Prop :=
  IsEndomorphism Γ e ∧ ∃ A : Finset α, IsTaylorSubdomain Γ A ∧ ∀ a, e a ∈ A

/-- The principal left ideal `Me := {u ∘ e : u ∈ M}` of `e` in the endomorphism monoid
`M = End(Γ)` (p.35). -/
def leftIdeal (Γ : ConstraintLanguage α) (e : α → α) : Set (α → α) :=
  {f | ∃ u, IsEndomorphism Γ u ∧ f = u ∘ e}

end CSPIdealMem


