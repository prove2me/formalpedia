-- Prove2me | Definitions.Def_MinCostMaj_BinPol
-- name    : MinCostMaj_BinPol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:14:14.350284+00:00
-- url     : https://prove2.me/theorems/46744fd1-9ffc-4903-958b-f17dad8c5c4a
-- title:
--   Conservative commutative binary instance polymorphisms, 2-absorption, the digraph $G(I)$, linked relations
-- statement:
--   Let $I$ be a binary instance with potatoes $A_x$.
--
--   1. A **binary instance polymorphism** is a family $\{f_x:A_x^2\to A_x\}_x$ such that for all $x,y$, every $R\in\mathcal R_{xy}$ and all $(a,b),(a',b')\in R$ one has $(f_x(a,a'),f_y(b,b'))\in R$. It is **conservative** if $f_x(a,b)\in\{a,b\}$ and **commutative** if $f_x(a,b)=f_x(b,a)$, for all $x$ and $a,b\in A_x$.
--   2. A nonempty $B\subseteq A_x$ **2-absorbs** $A_x$ if $f_x(B,A_x)\cup f_x(A_x,B)\subseteq B$.
--   3. The digraph $G(I)$ has the vertices $(a,b;x)$ with $a\ne b\in A_x$ and an arc $(a,b;x)\to(c,d;y)$ iff some $R\in\mathcal R_{xy}$ has $(a,c),(b,d)\in R$ and $(a,d)\notin R$. The vertices $(a,b;x)$ and $(b,a;x)$ are **dual**.
--   4. A relation $R\subseteq B\times C$ is **proper** if $\emptyset\ne R\ne B\times C$, and **linked** if it is subdirect ($\mathrm{proj}_1R=B$, $\mathrm{proj}_2R=C$) and the transitive closure of $R'(x,y)\iff\exists v\,(R(x,v)\wedge R(y,v))$ is $B^2$.
--
--   These notions drive Appendix A: the existence of a conservative commutative binary polymorphism is read off $G(I)$, and 2-absorption turns a linked pattern into a proper arc-consistent subinstance.
--
--   **Formalization Note** The family is a function $f$ of the variable and two values; only its values on $A_x\times A_x$ matter. Two vertices lie in the same strongly connected component when each is reachable from the other.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Definitions A.2 and A.5, pp.13–14; Appendix A, p.12 (PDF pp.13–15)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst
import Definitions.Def_MinCostMaj_Pattern

namespace MinCostMaj

namespace BinInst

variable {V D : Type*}

/-- **Conservative commutative binary instance polymorphism** (Definition A.2, p.13).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Definition A.2, p.13: "A binary instance polymorphism … is a
family of operations {fx : A²x → Ax}x such that, for every x and y and every R ∈ Rxy, whenever
(a, b), (a′, b′) ∈ R, one has (fx(a, a′), fy(b, b′)) ∈ R. The polymorphism is conservative if every
fx is conservative, and commutative if every fx is commutative."

**Formalization Note.** The family is `f : V → D → D → D`; only its values on `Aₓ × Aₓ` matter
(conservativity and commutativity are required there, and on binary instances every pair in a
constraint lies in the potatoes). Conservativity puts `fₓ(a, b) ∈ {a, b} ⊆ Aₓ`. -/
def IsConsCommBinPol (I : BinInst V D) (f : V → D → D → D) : Prop :=
  (∀ x, ∀ a ∈ I.pot x, ∀ b ∈ I.pot x, (f x a b = a ∨ f x a b = b) ∧ f x a b = f x b a) ∧
    ∀ x y, ∀ R ∈ I.rels x y, ∀ a b a' b' : D, (a, b) ∈ R → (a', b') ∈ R →
      (f x a a', f y b b') ∈ R

/-- **2-absorption** (Definition A.2, p.13): "a nonempty subset B ⊆ Ax 2-absorbs Ax if
fx(B, Ax) ∪ fx(Ax, B) ⊆ B." -/
def TwoAbsorbs (I : BinInst V D) (f : V → D → D → D) (x : V) (B : Set D) : Prop :=
  B.Nonempty ∧ B ⊆ I.pot x ∧ ∀ b ∈ B, ∀ a ∈ I.pot x, f x b a ∈ B ∧ f x a b ∈ B

/-- **Arcs of the digraph G(I)** (Definition A.5, pp.13–14): the vertices are triples `(a, b; x)`
with `a ≠ b ∈ Aₓ`; "there is an arc (a, b; x) −→ (c, d; y) if and only if there exists R ∈ Rxy such
that (a, c), (b, d) ∈ R and (a, d) ∉ R." A triple is `(a, b, x) : D × D × V`. -/
def GArc (I : BinInst V D) (s t : D × D × V) : Prop :=
  s.1 ≠ s.2.1 ∧ s.1 ∈ I.pot s.2.2 ∧ s.2.1 ∈ I.pot s.2.2 ∧
    t.1 ≠ t.2.1 ∧ t.1 ∈ I.pot t.2.2 ∧ t.2.1 ∈ I.pot t.2.2 ∧
    ∃ R ∈ I.rels s.2.2 t.2.2, (s.1, t.1) ∈ R ∧ (s.2.1, t.2.1) ∈ R ∧ (s.1, t.2.1) ∉ R

/-- **No dual vertices of G(I) belong to the same strongly connected component** (Theorem A.6,
p.14): for no vertex `(a, b; x)` are `(a, b; x)` and its dual `(b, a; x)` mutually reachable. -/
def NoDualSameSCC (I : BinInst V D) : Prop :=
  ∀ x, ∀ a ∈ I.pot x, ∀ b ∈ I.pot x, a ≠ b →
    ¬ (Relation.ReflTransGen I.GArc (a, b, x) (b, a, x) ∧
        Relation.ReflTransGen I.GArc (b, a, x) (a, b, x))

end BinInst

/-- **Proper relation** (Appendix A, p.12): `R ⊆ B × C` is proper if `∅ ≠ R ≠ B × C`. -/
def IsProperRel {D : Type*} (B C : Set D) (R : Set (D × D)) : Prop :=
  R.Nonempty ∧ R ≠ B ×ˢ C

/-- **Linked relation** (Appendix A, p.12): `R ⊆ B × C` is linked "if it is subdirect
(proj1(R) = B while proj2(R) = C) and the transitive closure of R′ is B² where
R′(x, y) = ∃v R(x, v) ∧ R(y, v)." -/
def IsLinked {D : Type*} (B C : Set D) (R : Set (D × D)) : Prop :=
  Prod.fst '' R = B ∧ Prod.snd '' R = C ∧
    {xy : D × D | Relation.TransGen (fun x y => ∃ v, (x, v) ∈ R ∧ (y, v) ∈ R) xy.1 xy.2} =
      B ×ˢ B

end MinCostMaj


