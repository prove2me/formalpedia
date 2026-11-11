-- Prove2me | Definitions.Def_ConstrainedDirSep_STSep_BinaryCSP
-- name    : ConstrainedDirSep_STSep_BinaryCSP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:07:44.188072+00:00
-- url     : https://prove2.me/theorems/89d9c0bf-e5a4-46aa-95d5-74719c7d2dff
-- title:
--   Binary CSPs over ordered domains, arc consistency and encodings
-- statement:
--   A **binary CSP over ordered domains** has variables $X_1,\dots,X_r$ with domains $[d_i]$ (a finite linear order of size $d_i$), arbitrary unary allowed sets $U_i\subseteq[d_i]$, and for every ordered pair $i\ne j$ a relation $R_{ij}\subseteq[d_i]\times[d_j]$. An assignment $x$ **satisfies** it if $x_i\in U_i$ and $(x_i,x_j)\in R_{ij}$ for all $i\ne j$.
--
--   A family of current domains $D_i\subseteq U_i$ is **arc consistent** if for every $i\ne j$ each $p\in D_i$ has some $q\in D_j$ with $(p,q)\in R_{ij}$, and each $q\in D_j$ has some $p\in D_i$ with $(p,q)\in R_{ij}$. Enforcing arc consistency (repeatedly deleting unsupported values) leaves the **greatest** arc-consistent family, `acClosure`: a value survives iff it lies in some arc-consistent family.
--
--   The instance is encoded by $r$, the $d_i$, and the membership bits of every $U_i$ over $[d_i]$ and of every $R_{ij}$ over $[d_i]\times[d_j]$; with unary costs, $\mathrm{enc}(\omega_i(p))$ for every $i$ and $p\in[d_i]$ follows.
--
--   **Formalization Note.** Several constraints on one ordered pair are a single relation (their intersection), a constraint on $(X_j,X_i)$ is the transposed relation, an absent constraint is the full relation, and a constraint on $(X_i,X_i)$ is a unary one; $R_{ii}=\emptyset$ is required.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), pp. 16–17 (PDF 19–20), Lemmas 4.6 and 4.7; p. 42 (PDF 45), App. A.1 (arc consistency)

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Encoding
import Definitions.Def_ConstrainedDirSep_STSep_ChainCSP

set_option autoImplicit false

namespace ConstrainedDirSep.STSep

/-- **A binary CSP over ordered domains** (data). Olkowski, Ramanujan, *Constrained Directed
Separation*, STOC 2027 submission (manuscript sha256 4dd06c29…), §4.2, pp. 16–17 (PDF 19–20),
Lemmas 4.6 and 4.7: variables `X_1, …, X_r` (indexed by `Fin r`) with finite linearly ordered
domains `[d_i] = {1, …, d_i}`, arbitrary unary allowed sets `U_i ⊆ [d_i]`, and for every ordered
pair `i ≠ j` a binary relation `R_ij ⊆ [d_i] × [d_j]` constraining `(X_i, X_j)`.

**Formalization Note.** A finite linear order of size `d` is identified with `[d]`. Several
constraints on the same ordered pair are one relation (their intersection), a constraint on
`(X_j, X_i)` is the transposed relation, an absent constraint is the full relation `[d_i] × [d_j]`,
and a binary constraint on `(X_i, X_i)` is a unary one (`U_i`); `R i i` is required empty. -/
structure BinaryCSP where
  /-- the number of variables -/
  r : ℕ
  /-- the domain sizes -/
  d : Fin r → ℕ
  /-- the unary allowed sets -/
  U : Fin r → Finset ℕ
  /-- the binary relations -/
  R : Fin r → Fin r → Finset (ℕ × ℕ)

/-- **Well-formed binary CSP**: `U_i ⊆ [d_i]`, `R_ij ⊆ [d_i] × [d_j]`, `R_ii = ∅`. -/
def BinaryCSP.WF (I : BinaryCSP) : Prop :=
  (∀ i, ∀ p ∈ I.U i, 1 ≤ p ∧ p ≤ I.d i) ∧
  (∀ i j, ∀ pq ∈ I.R i j, 1 ≤ pq.1 ∧ pq.1 ≤ I.d i ∧ 1 ≤ pq.2 ∧ pq.2 ≤ I.d j) ∧
  (∀ i, I.R i i = ∅)

/-- **Satisfying assignment** of a binary CSP: `x_i ∈ U_i` for all `i` and `(x_i, x_j) ∈ R_ij` for
all `i ≠ j`. -/
def BinaryCSP.Satisfies (I : BinaryCSP) (x : Fin I.r → ℕ) : Prop :=
  (∀ i, x i ∈ I.U i) ∧ ∀ i j, i ≠ j → (x i, x j) ∈ I.R i j

/-- **Arc-consistent family of domains.** App. A.1, p. 42 (PDF 45): arc consistency deletes a
value of one variable "if some binary constraint involving that variable gives it no compatible
value in the other variable's current domain". A family `Dm` of current domains (`Dm i ⊆ U_i`) is
arc consistent if no such deletion applies: for every `i ≠ j`, every `p ∈ Dm i` has some `q ∈ Dm j`
with `(p, q) ∈ R_ij`, and every `q ∈ Dm j` has some `p ∈ Dm i` with `(p, q) ∈ R_ij`. -/
def BinaryCSP.IsArcConsistent (I : BinaryCSP) (Dm : Fin I.r → Finset ℕ) : Prop :=
  (∀ i, Dm i ⊆ I.U i) ∧
  ∀ i j, i ≠ j →
    (∀ p ∈ Dm i, ∃ q ∈ Dm j, (p, q) ∈ I.R i j) ∧ (∀ q ∈ Dm j, ∃ p ∈ Dm i, (p, q) ∈ I.R i j)

/-- **The domains left by arc consistency.** The result of enforcing arc consistency (App. A.1,
p. 42, PDF 45) is the greatest arc-consistent family: a value `p` of `X_i` survives iff it lies in
some arc-consistent family. -/
def BinaryCSP.acClosure (I : BinaryCSP) (i : Fin I.r) : Set ℕ :=
  {p | ∃ Dm : Fin I.r → Finset ℕ, I.IsArcConsistent Dm ∧ p ∈ Dm i}

/-- **Input word of a binary CSP**: `r`, the domain sizes, the allowed sets as membership bits over
`[d_i]`, and every relation `R_ij` (`i ≠ j`, lexicographic order) as membership bits over
`[d_i] × [d_j]`. Domains are written out explicitly, as is usual for CSP instances. -/
noncomputable def encBinaryCSP (I : BinaryCSP) : List Bool :=
  encNat I.r ++ (List.finRange I.r).flatMap (fun i => encNat (I.d i)) ++
    (List.finRange I.r).flatMap (fun i => charBits (· ∈ I.U i) (rangeOne (I.d i))) ++
    (List.finRange I.r).flatMap fun i => (List.finRange I.r).flatMap fun j =>
      if i ≠ j then charBits (· ∈ I.R i j) (gridPairs (I.d i) (I.d j)) else []

/-- **Input word of a binary CSP with unary costs**: the instance, then the binary cost
`ω_i(p)` for every `i` and `p ∈ [d_i]`. -/
noncomputable def encWBinaryCSP (I : BinaryCSP) (ω : Fin I.r → ℕ → ℕ) : List Bool :=
  encBinaryCSP I ++ (List.finRange I.r).flatMap fun i => (rangeOne (I.d i)).flatMap fun p =>
    encNat (ω i p)

end ConstrainedDirSep.STSep


