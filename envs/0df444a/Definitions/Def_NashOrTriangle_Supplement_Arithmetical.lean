-- Prove2me | Definitions.Def_NashOrTriangle_Supplement_Arithmetical
-- name    : NashOrTriangle_Supplement_Arithmetical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:48:02.645638+00:00
-- url     : https://prove2.me/theorems/2210f10b-9a57-427e-9316-e5bc694b339b
-- title:
--   $\Sigma^0_1$ and $\Pi^0_2$ sets, completeness and undecidability of promise problems
-- statement:
--   A set $S\subseteq\mathbb N$ is **$\Sigma^0_1$** if $e\in S\iff\exists n\,R(e,n)$ for a computable relation $R$, and **$\Pi^0_2$** if $e\in S\iff\forall m\,\exists n\,R(e,m,n)$ for a computable $R$.
--
--   A **promise problem** is a validity predicate $V$ on instance codes and a property $\Phi$ of valid instances.
--
--   1. $(V,\Phi)$ is **$\Sigma^0_1$-complete** if (membership) there is a computable $R$ with $\Phi(I)\iff\exists n\,R(I,n)$ for every valid $I$, and (hardness) every $\Sigma^0_1$ set $S$ reduces to it: there is a computable $f$ such that every $f(e)$ is valid and $\Phi(f(e))\iff e\in S$.
--   2. **$\Pi^0_2$-complete** is defined in the same way with $\Pi^0_2$ in place of $\Sigma^0_1$.
--   3. $(V,\Phi)$ is **undecidable** if no computable function agrees with $\Phi$ on every valid instance.
--
--   These are the recursion-theoretic notions of Theorems B.1 to B.3, where the instances are "promised to be total and correct".
--
--   **Formalization Note** The relation $R$ must be total and computable on every instance, but it need only agree with $\Phi$ on valid ones.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962cc2efb135d3833e902fa4e861e03acf9d2df3fe8140a50b646da66f7), Theorems B.1–B.3, pp.22–23 (PDF pp.23–24)

import Mathlib

namespace NashOrTriangle.Supplement

/-!
Classes of the arithmetical hierarchy and completeness and undecidability of promise problems on
instance codes `I : ℕ`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorems B.1–B.3, printed pp. 22–23
(PDF pp. 23–24): "Σ0 1-complete", "undecidable", "Π0 2-complete", for instances "promised to be
total and correct".

**Formalization Note** A promise problem is a validity predicate `V` and a property `Φ` of valid
instances. Membership in a class is relative to the promise (the witnessing computable relation
must be total, but it only has to agree with `Φ` on valid instances); hardness is a computable
many-one reduction from every set of the class whose image instances are all valid. Completeness
is membership and hardness.
-/

/-- `S` is a `Σ⁰₁` set (recursively enumerable): `e ∈ S ↔ ∃ n, R(e, n)` for a computable `R`. -/
def IsSigma01 (S : ℕ → Prop) : Prop :=
  ∃ R : ℕ × ℕ → Bool, Computable R ∧ ∀ e, S e ↔ ∃ n, R (e, n) = true

/-- `S` is a `Π⁰₂` set: `e ∈ S ↔ ∀ m, ∃ n, R(e, m, n)` for a computable `R`. -/
def IsPi02 (S : ℕ → Prop) : Prop :=
  ∃ R : ℕ × ℕ × ℕ → Bool, Computable R ∧ ∀ e, S e ↔ ∀ m, ∃ n, R (e, m, n) = true

/-- The promise problem `(V, Φ)` is `Σ⁰₁`-complete. -/
def PromiseSigma01Complete (V Φ : ℕ → Prop) : Prop :=
  (∃ R : ℕ × ℕ → Bool, Computable R ∧ ∀ I, V I → (Φ I ↔ ∃ n, R (I, n) = true)) ∧
  ∀ S : ℕ → Prop, IsSigma01 S →
    ∃ f : ℕ → ℕ, Computable f ∧ ∀ e, V (f e) ∧ (Φ (f e) ↔ S e)

/-- The promise problem `(V, Φ)` is `Π⁰₂`-complete. -/
def PromisePi02Complete (V Φ : ℕ → Prop) : Prop :=
  (∃ R : ℕ × ℕ × ℕ → Bool, Computable R ∧
    ∀ I, V I → (Φ I ↔ ∀ m, ∃ n, R (I, m, n) = true)) ∧
  ∀ S : ℕ → Prop, IsPi02 S →
    ∃ f : ℕ → ℕ, Computable f ∧ ∀ e, V (f e) ∧ (Φ (f e) ↔ S e)

/-- The promise problem `(V, Φ)` is **undecidable**: no computable `d` agrees with `Φ` on every
valid instance. -/
def PromiseUndecidable (V Φ : ℕ → Prop) : Prop :=
  ¬ ∃ d : ℕ → Bool, Computable d ∧ ∀ I, V I → (d I = true ↔ Φ I)

end NashOrTriangle.Supplement


