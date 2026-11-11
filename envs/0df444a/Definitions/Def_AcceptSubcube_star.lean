-- Prove2me | Definitions.Def_AcceptSubcube_star
-- name    : AcceptSubcube_star
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:31.124228+00:00
-- url     : https://prove2.me/theorems/a614cf41-5979-472e-b678-6da4589e52b7
-- title:
--   Star instances $\mathcal I_{S,a}$ and the incidence $d_S(x)$
-- statement:
--   For a $t$-set $S\subseteq[n]$ and a pattern $a\in\{0,1\}^S$, the **star instance** $\mathcal I_{S,a}$ lives on $[n]\setminus S$. For each original scope $E\supseteq S$ with $T=E\setminus S$ it has the predicate
--   $$Q^{S,a}_T(z)=P_{S\cup T}(a,z);$$
--   original scopes not containing all of $S$ are dropped. For an assignment $x$, $d_S(x)=|\{E\supseteq S:P_E(x_E)=0\}|$.
--
--   The file also defines $x_{-S}$, the restriction of $x$ to $[n]\setminus S$, and the operation of appending $a$ to a star assignment.
--
--   Stars carry the pinning step of the algorithm: Lemma 2.4 shows that under $\mathsf P_t$ they are complete instances of arity $k-t$ whose predicates reject some pattern.
--
--   **Formalization Note** The variables of $[n]\setminus S$ are renumbered $0,\dots,n-|S|-1$ in increasing order, so a star is an instance on $n-|S|$ variables; the pattern $a$ is given by the set of coordinates of $S$ where it is $1$.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), §2.2, p.11 (I_{S,a}, d_S); Lemma 5.3, p.26 (appending a)

import Mathlib
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost

namespace AcceptSubcube

/-- The variables of `[n] ∖ S` in increasing order; the star instance numbers them `0, 1, …`. -/
def restVars (n : ℕ) (S : Finset ℕ) : List ℕ :=
  (List.range n).filter (fun v => decide (v ∉ S))

/-- The constraint `Q^{S,a}_T` of the star built from an original constraint `c` whose scope
contains `S`: scope `T = scope ∖ S` (renumbered by `restVars`), table `z ↦ P(a, z)`. The pattern
`a` on `S` is given by the set `A ⊆ S` of its ones. -/
def starCons (n : ℕ) (S A : Finset ℕ) (c : List ℕ × List Bool) : List ℕ × List Bool :=
  let free := c.1.filter (fun v => decide (v ∉ S))
  (free.map (fun v => (restVars n S).idxOf v),
    (List.range (2 ^ free.length)).map (fun j =>
      evalTab c (fun v => if v ∈ S then decide (v ∈ A) else Nat.testBit j (free.idxOf v))))

/-- **Star instance** `I_{S,a}`.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), §2.2, p.11: "For S ∈ ([n] choose t) and
a ∈ {0,1}^S, the star instance I_{S,a} on [n]∖S has, for each T ∈ ([n]∖S choose ℓ) with ℓ = k − t,
the predicate Q^{S,a}_T(z) = P_{S∪T}(a, z). Only original scopes containing all of S are kept."

**Formalization Note.** The pattern `a ∈ {0,1}^S` is the set `A ⊆ S` of coordinates where it is
`1`. The variables of `[n]∖S` are renumbered `0, …, n − |S| − 1` in increasing order
(`restVars`), so the star is an instance on `n − |S|` variables. -/
def star (I : GInst) (S A : Finset ℕ) : GInst :=
  ⟨I.n - S.card, (I.cons.filter (fun c => decide (S ⊆ c.1.toFinset))).map (starCons I.n S A)⟩

/-- `x_{−S}`: the restriction of `x` to `[n]∖S`, as an assignment of the star (renumbered). -/
def restrictTo (I : GInst) (S : Finset ℕ) (x : Fin I.n → Bool) : Fin (I.n - S.card) → Bool :=
  fun j => extA x ((restVars I.n S).getD j 0)

/-- `x_S` as the set of coordinates of `S` where `x` is `1`. -/
def onesOn {n : ℕ} (S : Finset ℕ) (x : Fin n → Bool) : Finset ℕ :=
  S.filter (fun v => extA x v)

/-- `d_S(x) = |{E ⊇ S : P_E(x_E) = 0}|` (p.11). -/
def dS (I : GInst) (S : Finset ℕ) (x : Fin I.n → Bool) : ℕ :=
  I.cons.countP (fun c => decide (S ⊆ c.1.toFinset) && !evalTab c (extA x))

/-- A star assignment `τ'` with `a` (the set `A ⊆ S` of ones) appended: the assignment of the
original instance equal to `a` on `S` and to `τ'` (renumbered back) off `S` (p.26, "appends a to
every candidate"). -/
def extendStar {m : ℕ} (n : ℕ) (S A : Finset ℕ) (τ' : Fin m → Bool) : Fin n → Bool :=
  fun v => if (v : ℕ) ∈ S then decide ((v : ℕ) ∈ A) else extA τ' ((restVars n S).idxOf (v : ℕ))

end AcceptSubcube


