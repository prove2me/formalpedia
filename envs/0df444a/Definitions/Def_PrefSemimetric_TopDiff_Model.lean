-- Prove2me | Definitions.Def_PrefSemimetric_TopDiff_Model
-- name    : PrefSemimetric_TopDiff_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:46.317749+00:00
-- url     : https://prove2.me/theorems/becc0070-4731-450c-9d72-9aadf2220948
-- title:
--   §2.1–§3.2, pp. 7–15 — acyclic orders, maximal sets, ⊕/⊖ perturbations, in-between, µ-top-difference semimetric, Axioms 1, 3, 4
-- statement:
--   Let $X$ be a finite set of alternatives. A binary relation $R$ on $X$ has **asymmetric part** $R^>$ ($x\,R^>\,y$ iff $x\,R\,y$ and not $y\,R\,x$) and **symmetric part** $R\setminus R^>$. $R$ is an **acyclic order** if it is reflexive and there are no pairwise distinct $z_1,\dots,z_k$ with $z_1\,R^>\,z_2\,R^>\cdots z_k\,R^>\,z_1$. The set of acyclic orders is $\mathcal A(X)$; a generic one is written $\succsim$ (strict part $\succ$, symmetric part $\sim$) or $\trianglerighteq$ (strict part $\vartriangleright$). For $S\subseteq X$, the set of $R$-maximal elements is
--   $$M(S,R)=\{x\in S : y\,R^>\,x \text{ for no } y\in S\}.$$
--
--   The definitions in this file are:
--
--   1. **Single addition and deletion** (§2.3, pp. 8–9). For distinct $a,b$ that are not $\succ$-comparable, $\succsim\oplus(a,b)$ is $\succsim\sqcup\{(a,b)\}$ if $a,b$ are incomparable and $\succsim\setminus\{(b,a)\}$ if $b\sim a$; it counts only when it is acyclic. For $a\succ b$, $\succsim\ominus(a,b)=\succsim\setminus\{(a,b)\}$.
--   2. **One-step perturbation toward $\trianglerighteq$** (pp. 9–10), written $\succsim\to\succsim_0\twoheadrightarrow\trianglerighteq$. $\succsim_0$ is acyclic and either (i) $\succsim_0=\succsim\ominus(a,b)$ for some $a\succ b$ with not $a\vartriangleright b$, and $x\succ b$ for every $x$ with $x\vartriangleright b$; or (ii) $\succsim_0=\succsim\oplus(a,b)$ for some $a,b$ not $\succ$-comparable with $a\vartriangleright b$.
--   3. **In-between** (p. 10). $\succsim^*$ is in-between $\succsim$ and $\trianglerighteq$ if it is reached from $\succsim$ by a finite nonempty chain of one-step perturbations toward $\trianglerighteq$.
--   4. **The $\mu$-top-difference semimetric** (§3.1, p. 12). For a positive measure $\mu$ on $2^X$,
--   $$D^\mu(\succsim,\trianglerighteq)=\sum_{S\subseteq X}\mu\big(M(S,\succsim)\,\triangle\,M(S,\trianglerighteq)\big).$$
--   5. **The test orders and the count $N$** (§3.2, p. 14). For distinct $a,b$, $\succsim_{ab}$ and $\succsim^+_{ab}$ are the partial orders with strict parts $(X\setminus\{a,b\})\times\{a,b\}$ and $(X\setminus\{a,b\})\times\{a,b\}\sqcup\{(a,b)\}$. $N(b,\succsim)=|\{x\in X\setminus\{b\}:\text{not } x\succ b\}|$.
--   6. **The axioms** for a semimetric $d$ on $\mathcal A(X)$ (pp. 13–15). Axiom 1: if $\succsim_0$ is in-between $\succsim$ and $\trianglerighteq$, then $d(\succsim,\trianglerighteq)=d(\succsim,\succsim_0)+d(\succsim_0,\trianglerighteq)$. Axiom 3: if $a,b$ are not $\succ$-comparable, $d(\succsim,\succsim\oplus(a,b))=2^{N(b,\succsim)-1}d(\succsim_{ab},\succsim^+_{ab})$, and if $a\succ b$, $d(\succsim,\succsim\ominus(a,b))=2^{N(b,\succsim)}d(\succsim_{ab},\succsim^+_{ab})$. Axiom 4: if $\succ=\vartriangleright$ then $d(\succsim,\trianglerighteq)=0$.
--
--   These objects are the vocabulary of the characterization theorem (Theorem 3.1) and of every milestone of the mission.
--
--   **Formalization Note** Relations are `X → X → Prop`. $\mathcal A(X)$ is not a subtype: `d` is a real function on all relations, and every axiom, semimetric property and conclusion quantifies only over relations satisfying `IsAcyclicOrder` (values off $\mathcal A(X)$ never enter). Acyclicity is stated as irreflexivity of the transitive closure of $R^>$, which is equivalent to the absence of a cycle of pairwise distinct elements. `asymmPart`/`symmPart` are $R^>$ and $R\setminus R^>$. The measure $\mu$ is given by point weights `w`, $\mu(T)=\sum_{x\in T}w(x)$; every positive measure on the power set has this form (the zero measure included). The sum over $S\subseteq X$ runs over all finite subsets; sets with $|S|\le 1$ contribute $0$. `oplus R a b` is the single formula "add $(a,b)$, remove $(b,a)$", which agrees with both cases of p. 8; Axiom 3's $\oplus$ clause and condition (ii) apply only when it is an acyclic order, as on the page. `IsSemimetric d` reads the undefined word "semimetric" as a pseudometric on $\mathcal A(X)$ with values in $[0,\infty)$: $d\ge0$, $d(R,R)=0$, symmetry and the triangle inequality. In Axiom 3 `Nb b R - 1` is natural-number subtraction; in the $\oplus$ clause $a$ is not strictly above $b$, so $N(b,\succsim)\ge1$ and the subtraction is exact.
-- source:
--   Nishimura & Ok, A Class of Dissimilarity Semimetrics for Preference Relations, arXiv:2203.04418v1, pp. 7–15, §2.1 (p. 7), §2.3 (pp. 8–10, (1)–(3)), §3.1 (p. 12), §3.2 (pp. 13–15, Axioms 1, 3, 4, N(b,≿), ≿ab, ≿+ab)

import Mathlib

namespace PrefSemimetric.TopDiff
open Classical

variable {X : Type*}

/-- The asymmetric (strict) part `R>` of a binary relation `R` (§2.1, p. 7):
`x R> y` iff `x R y` and not `y R x`. -/
def asymmPart (R : X → X → Prop) (x y : X) : Prop := R x y ∧ ¬ R y x

/-- The symmetric part `R \ R>` of a binary relation `R` (§2.1, p. 7). -/
def symmPart (R : X → X → Prop) (x y : X) : Prop := R x y ∧ R y x

/-- `R` is an acyclic order (§2.1, p. 7): `R` is reflexive, and there is no cycle
`z₁ R> z₂ R> ⋯ R> z_k R> z₁`, expressed as irreflexivity of the transitive closure of `R>`. -/
def IsAcyclicOrder (R : X → X → Prop) : Prop :=
  (∀ x, R x x) ∧ ∀ x, ¬ Relation.TransGen (asymmPart R) x x

/-- The set `M(S, R) = {x ∈ S : y R> x for no y ∈ S}` of `R`-maximal elements of `S` (§2.1, p. 7). -/
noncomputable def maxSet (S : Finset X) (R : X → X → Prop) : Finset X :=
  S.filter (fun x => ∀ y ∈ S, ¬ asymmPart R y x)

/-- The `µ`-top-difference semimetric (§3.1, p. 12), for the measure `µ(T) = ∑_{x ∈ T} w x`:
`D^µ(R, T) = ∑_{S ⊆ X} µ(M(S, R) △ M(S, T))`. -/
noncomputable def Dmu [Fintype X] [DecidableEq X] (w : X → ℝ) (R T : X → X → Prop) : ℝ :=
  ∑ S : Finset X, ∑ x ∈ symmDiff (maxSet S R) (maxSet S T), w x

/-- Single addition `R ⊕ (a, b)` (§2.3, pp. 8–9): add `(a, b)` and remove `(b, a)`. For distinct
`a, b` that are not `R>`-comparable this is `R ⊔ {(a, b)}` if `(a, b) ∈ Inc(R)` and `R \ {(b, a)}`
if `b ∼ a`, the two cases of p. 8. -/
def oplus (R : X → X → Prop) (a b : X) : X → X → Prop :=
  fun x y => (R x y ∨ (x = a ∧ y = b)) ∧ ¬ (x = b ∧ y = a)

/-- Single deletion `R ⊖ (a, b) = R \ {(a, b)}` (§2.3, p. 9). -/
def ominus (R : X → X → Prop) (a b : X) : X → X → Prop :=
  fun x y => R x y ∧ ¬ (x = a ∧ y = b)

/-- `R → R0 ↠ T`: `R0` is an acyclic order and a one-step perturbation of `R` toward `T`
(§2.3, pp. 9–10, conditions (1)–(3)). -/
def OneStepToward (R R0 T : X → X → Prop) : Prop :=
  IsAcyclicOrder R0 ∧
  ((∃ a b, asymmPart R a b ∧ R0 = ominus R a b ∧ ¬ asymmPart T a b ∧
      ∀ x, asymmPart T x b → asymmPart R x b) ∨
   (∃ a b, ¬ asymmPart R a b ∧ ¬ asymmPart R b a ∧ R0 = oplus R a b ∧ asymmPart T a b))

/-- `R0` is in-between `R` and `T` (§2.3, p. 10): `R0` is an `n`-step perturbation of `R` toward
`T` for some `n ≥ 1`, i.e. reachable from `R` by a chain of one-step perturbations toward `T`. -/
def InBetween (R R0 T : X → X → Prop) : Prop :=
  Relation.TransGen (fun P Q => OneStepToward P Q T) R R0

/-- `≿_ab` (§3.2, p. 14): the partial order whose asymmetric part is `(X \ {a, b}) × {a, b}`. -/
def prefAB (a b : X) : X → X → Prop :=
  fun x y => x = y ∨ (x ≠ a ∧ x ≠ b ∧ (y = a ∨ y = b))

/-- `≿⁺_ab` (§3.2, p. 14): the partial order whose asymmetric part is
`(X \ {a, b}) × {a, b} ⊔ {(a, b)}`. -/
def prefABplus (a b : X) : X → X → Prop :=
  fun x y => prefAB a b x y ∨ (x = a ∧ y = b)

/-- `N(b, R) = |{x ∈ X \ {b} : not x R> b}|` (§3.2, p. 14). -/
noncomputable def Nb [Fintype X] (b : X) (R : X → X → Prop) : ℕ :=
  (Finset.univ.filter (fun x => x ≠ b ∧ ¬ asymmPart R x b)).card

/-- `d` is a semimetric on `A(X)` with values in `[0, ∞)`: on acyclic orders it is nonnegative,
vanishes on the diagonal, is symmetric and satisfies the triangle inequality. -/
def IsSemimetric (d : (X → X → Prop) → (X → X → Prop) → ℝ) : Prop :=
  ∀ R T U, IsAcyclicOrder R → IsAcyclicOrder T → IsAcyclicOrder U →
    0 ≤ d R T ∧ d R R = 0 ∧ d R T = d T R ∧ d R U ≤ d R T + d T U

/-- Axiom 1 (§3.2, p. 13). -/
def Axiom1 (d : (X → X → Prop) → (X → X → Prop) → ℝ) : Prop :=
  ∀ R R0 T, IsAcyclicOrder R → IsAcyclicOrder T → InBetween R R0 T →
    d R T = d R R0 + d R0 T

/-- Axiom 3 (§3.2, p. 15); the `⊕` clause applies when `R ⊕ (a, b)` is an acyclic order. -/
def Axiom3 [Fintype X] (d : (X → X → Prop) → (X → X → Prop) → ℝ) : Prop :=
  ∀ R a b, IsAcyclicOrder R → a ≠ b →
    ((¬ asymmPart R a b → ¬ asymmPart R b a → IsAcyclicOrder (oplus R a b) →
        d R (oplus R a b) = 2 ^ (Nb b R - 1) * d (prefAB a b) (prefABplus a b)) ∧
     (asymmPart R a b →
        d R (ominus R a b) = 2 ^ (Nb b R) * d (prefAB a b) (prefABplus a b)))

/-- Axiom 4 (§3.2, p. 15). -/
def Axiom4 (d : (X → X → Prop) → (X → X → Prop) → ℝ) : Prop :=
  ∀ R T, IsAcyclicOrder R → IsAcyclicOrder T → (∀ x y, asymmPart R x y ↔ asymmPart T x y) →
    d R T = 0

end PrefSemimetric.TopDiff


