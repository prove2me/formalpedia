-- Prove2me | Definitions.Def_ScatCaps_LinearSets_Model
-- name    : ScatCaps_LinearSets_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:07.364972+00:00
-- url     : https://prove2.me/theorems/aa80a380-1b5b-4168-b87d-7135d3460b69
-- title:
--   §§1–3, pp. 1–17 — linear sets, rank, scatteredness, the field tower of §2, norms, traces, U_f, Q_f, binomials, adjoints
-- statement:
--   This definition file fixes the objects of the paper's §§1–3.
--
--   **Linear sets.** Let $k$ be a field, let $\mathbb F_q\subseteq K$ be subfields of $k$, and let $V$ be a $k$-vector space. An **$\mathbb F_q$-subspace** of $V$ is a subset $U$ containing $0$ and closed under addition and under multiplication by elements of $\mathbb F_q$. It defines the **$\mathbb F_q$-linear set** $L_U=\{\langle u\rangle_K : u\in U\setminus\{0\}\}$ of the projective space $\mathrm{PG}(V,K)$. Its **rank** is $\dim_{\mathbb F_q}U$; here rank $m$ is encoded as $|U|=|\mathbb F_q|^m$. The **weight** of a point $\langle u\rangle_K$ is $\dim_{\mathbb F_q}(\langle u\rangle_K\cap U)$, and $L_U$ is **scattered** when every point has weight $1$, i.e. when for every nonzero $u\in U$
--
--   $$
--   \lambda\in K,\quad \lambda u\in U\quad\Longrightarrow\quad \lambda\in\mathbb F_q .
--   $$
--
--   **The tower of §2.** For a finite field $E$ of characteristic $p$ and $q=p^h$, $\mathbb F_{q^m}$ is the fixed field of $x\mapsto x^{q^m}$ in $E$; when $|E|=q^{6n}$ and $m\mid 6n$ this is the unique subfield of order $q^m$. The predicate `Section2Setting` records $p$ prime, $h>0$, $q=p^h$, $n\ge2$, $|E|=q^{6n}$ (p. 4).
--
--   **Maps and sets of §2.** For $d\mid m$, the relative norm is $N_{q^m/q^d}(x)=\prod_{j<m/d}x^{q^{dj}}$ and the trace is $\mathrm{Tr}_{q^m/q}(x)=\sum_{j<m}x^{q^j}$; on $\mathbb F_{q^m}$ they are the field norm to $\mathbb F_{q^d}$ and the field trace to $\mathbb F_q$. For $f$ an $\mathbb F_q$-linear map of $\mathbb F_{q^{3n}}$ and $\omega\in E$,
--
--   $$
--   U_f=\{f(x)+x\omega : x\in\mathbb F_{q^{3n}}\},\qquad Q_f=\Big\{\tfrac{f(x)+x\omega}{f(y)+y\omega} : x,y\in\mathbb F_{q^{3n}},\ y\ne0\Big\}
--   $$
--
--   (equation (2) and Proposition 2.1). The monomial is $ax^{q^i}$ (p. 7), the binomial is $f_{i,a,b}(x)=ax^{q^i}+bx^{q^{2n+i}}$ (p. 12), a linearized polynomial is $\varphi(x)=\sum_{i=0}^{3n-1}a_ix^{q^i}$, and its adjoint for $\langle x,y\rangle=\mathrm{Tr}_{q^{3n}/q}(xy)$ is $\bar\varphi(x)=\sum_{i=0}^{3n-1}a_i^{q^{3n-i}}x^{q^{3n-i}}$ (pp. 10–11). Finally, for subsets $U_1,\dots,U_m$ of $V$, $U_1+\dots+U_m$ is the set of sums $u_1+\dots+u_m$ with $u_i\in U_i$ (equation (21)).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Subspaces are carrier sets with explicit closure conditions, so no restriction-of-scalars instance is needed. The field $K$ spanning the projective points is an explicit argument of the scattered predicate: in §2 it is $\mathbb F_{q^{2n}}$, in §3 and Theorem 1.2 it is the whole field $\mathbb F_{q^t}$. Choosing $K=E$ in §2 would make every nonzero $U$ non-scattered and $K=\mathbb F_q$ would make every $U$ scattered; neither is used. `IsLinearOn` asks that $f$ map $\mathbb F_{q^{3n}}$ into itself and be additive and $\mathbb F_q$-homogeneous there; its values outside $\mathbb F_{q^{3n}}$ are irrelevant.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, pp. 1–2 (linear sets, weight, scattered), p. 4 (§2 setting), pp. 5, 7, 10–12 (U_f, Q_f, monomial, binomial, trace form and adjoint), p. 16 (20)–(21)

import Mathlib

namespace ScatCaps.LinearSets

/-- A vector subspace over the indicated subfield, represented by its carrier set. -/
def IsFqSubspace {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (Fq : Subfield k) (U : Set V) : Prop :=
  (0 : V) ∈ U ∧
  (∀ u v : V, u ∈ U → v ∈ U → u + v ∈ U) ∧
  (∀ (a : Fq) (u : V), u ∈ U → ((a : k) • u) ∈ U)

/-- The cardinality version of dimension over the field of linearity. -/
def HasRank {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (Fq : Subfield k) (U : Set V) (m : ℕ) : Prop :=
  Nat.card U = (Nat.card Fq) ^ m

/-- The weight-one test for every point represented by a nonzero vector of `U`. -/
def IsScattered {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (Fq K : Subfield k) (U : Set V) : Prop :=
  ∀ (u : V), u ∈ U → u ≠ 0 → ∀ (c : K), ((c : k) • u) ∈ U → (c : k) ∈ Fq

/-- The subfield fixed by the `q^m` Frobenius, where `q = p^h`. -/
def subfieldOf (E : Type*) [Field E] (p h m : ℕ) [ExpChar E p] : Subfield E :=
  (iterateFrobenius E p (h * m)).eqLocusField (RingHom.id E)

/-- The finite field and prime-power parameters standing throughout §2. -/
def Section2Setting (E : Type*) [Field E] [Fintype E]
    (p h q n : ℕ) : Prop :=
  Nat.Prime p ∧ 0 < h ∧ q = p ^ h ∧ 2 ≤ n ∧ Fintype.card E = q ^ (6 * n)

/-- `f` is a map of `F3n` which is linear over `Fq`. -/
def IsLinearOn {E : Type*} [Field E] (Fq F3n : Subfield E) (f : E → E) : Prop :=
  f 0 = 0 ∧
  (∀ x : E, x ∈ F3n → f x ∈ F3n) ∧
  (∀ x y : E, x ∈ F3n → y ∈ F3n → f (x + y) = f x + f y) ∧
  (∀ (a : Fq) (x : E), x ∈ F3n → f ((a : E) * x) = (a : E) * f x)

/-- Relative norm from the field of order `q^m` to that of order `q^d`. -/
def relNorm {E : Type*} [Field E] (q m d : ℕ) (x : E) : E :=
  ∏ j ∈ Finset.range (m / d), x ^ (q ^ (d * j))

/-- Relative trace from the field of order `q^m` to that of order `q`. -/
def relTrace {E : Type*} [Field E] (q m : ℕ) (x : E) : E :=
  ∑ j ∈ Finset.range m, x ^ (q ^ j)

/-- The set `U_f = {f(x) + xω : x ∈ 𝔽_{q^{3n}}}` in the sixfold extension. -/
def sec2Set {E : Type*} [Field E] (F3n : Subfield E) (f : E → E) (ω : E) : Set E :=
  {u | ∃ x : E, x ∈ F3n ∧ u = f x + x * ω}

/-- The quotient set `Q_f` of Proposition 2.1. -/
def quotientSet {E : Type*} [Field E] (F3n : Subfield E) (f : E → E) (ω : E) : Set E :=
  {z | ∃ x y : E, x ∈ F3n ∧ y ∈ F3n ∧ y ≠ 0 ∧
      z = (f x + x * ω) / (f y + y * ω)}

/-- The monomial map used in Theorems 2.3 and 2.4. -/
def monom {E : Type*} [Field E] (q i : ℕ) (a : E) (x : E) : E :=
  a * x ^ (q ^ i)

/-- The binomial map `f_{i,a,b}` of Proposition 2.7. -/
def binom {E : Type*} [Field E] (q n i : ℕ) (a b : E) (x : E) : E :=
  a * x ^ (q ^ i) + b * x ^ (q ^ (2 * n + i))

/-- The linearized polynomial of degree less than `q^(3n)`. -/
def linearized {E : Type*} [Field E] (q n : ℕ) (a : Fin (3 * n) → E) (x : E) : E :=
  ∑ i : Fin (3 * n), a i * x ^ (q ^ (i : ℕ))

/-- The trace adjoint of a linearized polynomial. -/
def adjoint {E : Type*} [Field E] (q n : ℕ) (a : Fin (3 * n) → E) (x : E) : E :=
  ∑ i : Fin (3 * n), (a i) ^ (q ^ (3 * n - (i : ℕ))) *
    x ^ (q ^ (3 * n - (i : ℕ)))

/-- The carrier of the sum of a finite family of subspaces. -/
def directSumSet {V : Type*} [AddCommMonoid V] (m : ℕ)
    (U : Fin m → Set V) : Set V :=
  {w | ∃ u : Fin m → V, (∀ i, u i ∈ U i) ∧ w = ∑ i, u i}

end ScatCaps.LinearSets


