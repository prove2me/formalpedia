-- Prove2me | Definitions.Def_FOMCMonDep_tp
-- name    : FOMCMonDep_tp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:20.403087+00:00
-- url     : https://prove2.me/theorems/2e360099-2597-4363-9632-00ad749dc756
-- title:
--   Types $\mathrm{tp}^A_q(\bar v/W)$ over parameters and their number $|\mathrm{Types}^A_{k,q}(X/W)|$
-- statement:
--   Let $A$ be a structure and $W$ a set of its elements. A formula $\varphi(x_1,\dots,x_k)$ **with parameters from $W$** may mention elements of $W$ as constants. For $k,q\in\mathbb N$ and a tuple $\bar v\in V(A)^k$, the **type of $\bar v$ of quantifier rank $q$ over $W$** is
--   $$\mathrm{tp}^A_q(\bar v/W)=\{\varphi(x_1,\dots,x_k):\ \varphi \text{ has parameters from } W,\ \mathrm{qr}(\varphi)\le q,\ A\models\varphi(\bar v)\}.$$
--   For sets $X,W\subseteq V(A)$ the realized types of $k$-tuples from $X$ form $\mathrm{Types}^A_{k,q}(X/W)=\{\mathrm{tp}^A_q(\bar v/W):\bar v\in X^k\}$; $/W$ is omitted when $W=\emptyset$. The **atomic type** is $\mathrm{atp}^A(\bar v/W)=\mathrm{tp}^A_0(\bar v/W)$ and $\mathrm{ATypes}^A(X/W)=\mathrm{Types}^A_{1,0}(X/W)$.
--
--   This item defines the type, the parameter-free type $\mathrm{tp}^A_q(\bar v)$, and the number $|\mathrm{Types}^A_{k,q}(X/W)|$ of distinct types, which is what the main type bound (Theorem 4.4) and the width of Definition 4.1 count.
--
--   **Formalization Note** The structure on the carrier is an explicit argument. A parameter $w\in W$ is a free variable assigned $w$ itself instead of a constant symbol; this changes neither the tuples satisfying a formula nor its quantifier rank, so it gives the same types up to renaming and the same numbers of types. The number of types is a `Set.encard` in $\mathbb N\cup\{\infty\}$, the true cardinality also for infinite structures (Part I allows infinite graphs); distinct types are counted, not formulas.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §3, pp.11–12 (PDF 13–14)

import Mathlib
import Definitions.Def_FOMCMonDep_qrank

set_option autoImplicit false

open FirstOrder FirstOrder.Language

namespace FOMCMonDep

/-- **Types over parameters.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §3, pp.11–12 (PDF 13–14): "For a structure A and a set
W of its elements, let A_W denote the structure obtained by expanding A with constants representing each element of W.
A formula φ(x1, . . . , xk) with parameters from W is a formula in the signature of the structure A_W. […] For k, q ∈ N
and a tuple v̄ ∈ V(A)^k, define the type of v̄ of quantifier rank q over W, denoted tp^A_q(v̄/W), as the set of all
formulas φ(x1, . . . , xk) with parameters from W and of quantifier rank at most q such that A |= φ(v̄)."

**Formalization Note.** The structure `S` on `M` is an explicit argument, so that one carrier can carry several
structures in one statement. A parameter `w ∈ W` is a free variable `Sum.inr w`, always assigned `w` itself, instead
of a constant symbol: a formula of `A_W` with the constants `c_w` and the same formula with the variables `Sum.inr w`
hold of the same tuples and have the same quantifier rank, so the two readings give the same types up to this
renaming, and the same numbers of types. -/
def tp {L : Language} {M : Type*} (S : L.Structure M) (q : ℕ) {k : ℕ} (v : Fin k → M) (W : Set M) :
    Set (L.Formula (Fin k ⊕ W)) :=
  {φ | qrank φ ≤ q ∧ @Formula.Realize L M S _ φ (Sum.elim v Subtype.val)}

/-- **Parameter-free types** `tp^A_q(v̄)` (`W = ∅` in `tp`, written with the variables `Fin k` alone). Used where
the types of tuples in two different structures are compared (Lemma 4.9). -/
def tp0 {L : Language} {M : Type*} (S : L.Structure M) (q : ℕ) {k : ℕ} (v : Fin k → M) :
    Set (L.Formula (Fin k)) :=
  {φ | qrank φ ≤ q ∧ @Formula.Realize L M S _ φ v}

/-- **The number of types** `|Types^A_{k,q}(X/Y)|`. Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §3, p.12 (PDF 14): "For two sets
X, Y ⊆ V(A), denote Types^A_{k,q}(X/Y) := {tp^A_q(v̄/Y) : v̄ ∈ X^k}. We omit /Y from the notation if Y = ∅. The atomic
type of v̄ over Y is defined as atp^A(v̄/Y) := tp^A_0(v̄/Y) and we set ATypes^A(X/Y) := Types^A_{1,0}(X/Y)."

**Formalization Note.** The count is `Set.encard`, in `ℕ∞`: it is the true cardinality also when `X` is infinite
(Part I allows infinite graphs), whereas `Set.ncard` would be `0` on an infinite set. A bound `typeCount … ≤ T`
with `T` finite therefore also asserts that there are finitely many types. Distinct types are counted, not formulas.
`|ATypes^A(X/Y)|` is `typeCount S 1 0 X Y`. -/
noncomputable def typeCount {L : Language} {M : Type*} (S : L.Structure M) (k q : ℕ) (X W : Set M) : ℕ∞ :=
  ((fun v : Fin k → M => tp S q v W) '' {v | ∀ i, v i ∈ X}).encard

end FOMCMonDep


