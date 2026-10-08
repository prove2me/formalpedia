-- Prove2me | Definitions.Def_KarpPapadimitriou_Generator_COP
-- name    : KarpPapadimitriou_Generator_COP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:16:00.93298+00:00
-- url     : https://prove2.me/theorems/6a9e6965-e2f2-4d0a-9699-4fa60ebaf473
-- title:
--   Definition 1 — combinatorial optimization problems and their decision language
-- statement:
--   Fix the four-symbol alphabet $\Sigma=\{0,1,-,\#\}$ and binary codes for integers. A **combinatorial optimization problem** $C=(L,n,S)$ has a language $L\subseteq\{0,1\}^*$, a dimension $n(z)\in\mathbb N$ for each $z\in L$, and feasible nonnegative integer vectors $S(z)\subseteq\mathbb Z_+^{n(z)}$. The languages of valid $z$, of pairs $\langle z,y\rangle$ with $|y|=n(z)$, and of pairs $\langle z,x\rangle$ with $x\in S(z)$ all belong to Cook's class $\mathrm P$.
--
--   The decision language and rational convex hull are
--   $$D(C)=\{\langle z,c,k\rangle:z\in L,\ c\in\mathbb Z^{n(z)},\ k\in\mathbb Z,\ \exists x\in S(z),\ c\cdot x\ge k\},\qquad \mathrm{CH}(S(z))=\operatorname{conv}_{\mathbb Q} S(z).$$
--
--   A **facial description** is a family of integer inequalities whose common rational solution set is exactly $\mathrm{CH}(S(z))$ for every $z\in L$. It is **small** if one polynomial $p$ bounds the absolute value of every coefficient and right-hand side by $2^{p(|z|+n(z))}$.
--
--   These definitions supply the input problem and the inequalities used in Theorem 2.
--
--   **Formalization Note** The report uses $R$ for the rationals, so the convex hull is over $\mathbb Q$. The code of each integer vector carries its dimension, and malformed strings are outside $D(C)$. The polynomial in the smallness condition is written $p(m)=m^a+a$ for a single $a\in\mathbb N$ before all instances. The report's displayed instance program (3) says “min”, whereas its decision language and Theorem 2 use $c\cdot x\ge k$; the latter is followed here.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), pp. 3–5, Definition 1, decision problem D(C), facial and small facial descriptions

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace KarpPapadimitriou.Generator

abbrev Sym := ProjSchedTW.Complexity.BSym

/-- A binary string followed by a separator. -/
def encZ (z : List Bool) : List Sym :=
  z.map (fun b => if b then ProjSchedTW.Complexity.BSym.one else ProjSchedTW.Complexity.BSym.zero) ++
    [ProjSchedTW.Complexity.BSym.sep]

/-- A dimension-check input consists of `z` and a bit string `y`. -/
def encZY (z y : List Bool) : List Sym := encZ z ++ encZ y

/-- A point with integer coordinates, in binary. -/
def encZX {n : ℕ} (z : List Bool) (x : Fin n → ℤ) : List Sym :=
  encZ z ++ ProjSchedTW.Complexity.encNat n ++
    ProjSchedTW.Complexity.encInts (List.ofFn x)

/-- A threshold instance `⟨z,c,k⟩`. -/
def encDInput {n : ℕ} (z : List Bool) (c : Fin n → ℤ) (k : ℤ) : List Sym :=
  encZX z c ++ ProjSchedTW.Complexity.encInt k

/-- A triple `⟨z,f,g⟩` describing the inequality `f·x ≤ g`. -/
def encTriple {n : ℕ} (z : List Bool) (f : Fin n → ℤ) (g : ℤ) : List Sym :=
  encZX z f ++ ProjSchedTW.Complexity.encInt g

/-- Definition 1: the feasible integer vectors have nonnegative coordinates, and the three
languages displayed across pp. 3–4 are decidable in polynomial time. -/
structure COP where
  L : Set (List Bool)
  n : List Bool → ℕ
  S : (z : List Bool) → Set (Fin (n z) → ℤ)
  nonnegative : ∀ z ∈ L, ∀ x ∈ S z, ∀ j, 0 ≤ x j
  L_poly : {w : List Sym | ∃ z ∈ L, w = encZ z} ∈ CookPvsNP.P Sym
  dimension_poly :
    {w : List Sym | ∃ (z : List Bool) (y : List Bool),
      z ∈ L ∧ y.length = n z ∧ w = encZY z y} ∈ CookPvsNP.P Sym
  feasible_poly :
    {w : List Sym | ∃ (z : List Bool) (x : Fin (n z) → ℤ),
      z ∈ L ∧ x ∈ S z ∧ w = encZX z x} ∈ CookPvsNP.P Sym

/-- The paper's rational convex hull of feasible integer vectors. -/
def hull (C : COP) (z : List Bool) : Set (Fin (C.n z) → ℚ) :=
  convexHull ℚ ((fun x : Fin (C.n z) → ℤ => fun i => (x i : ℚ)) '' C.S z)

/-- Integer coefficient vector evaluated at a rational point. -/
def dotQ {n : ℕ} (f : Fin n → ℤ) (x : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, (f i : ℚ) * x i

/-- Integer coefficient vector evaluated at an integer point. -/
def dotZ {n : ℕ} (f x : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n, f i * x i

/-- The decision language `D(C)`, restricted to well-formed instance codes. -/
def DLang (C : COP) : CookPvsNP.Lang Sym :=
  {w | ∃ (z : List Bool) (c : Fin (C.n z) → ℤ) (k : ℤ),
    z ∈ C.L ∧ (∃ x ∈ C.S z, k ≤ dotZ c x) ∧ w = encDInput z c k}

/-- The dependent type of triples `⟨z,f,g⟩`. -/
abbrev Triple (C : COP) := Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ

/-- A facial description has only valid first components and characterizes the hull for every
valid instance and every rational test point. -/
def IsFacialDescription (C : COP) (F : Set (Triple C)) : Prop :=
  (∀ a ∈ F, a.1 ∈ C.L) ∧
  ∀ z ∈ C.L, ∀ x : Fin (C.n z) → ℚ,
    x ∈ hull C z ↔ ∀ f g, (⟨z, (f, g)⟩ : Triple C) ∈ F → dotQ f x ≤ (g : ℚ)

/-- A single exponent bounds every coefficient of every inequality in the family. -/
def IsSmall (C : COP) (F : Set (Triple C)) : Prop :=
  ∃ k : ℕ, ∀ a ∈ F,
    (∀ i, (a.2.1 i).natAbs ≤ 2 ^ ((a.1.length + C.n a.1) ^ k + k)) ∧
      a.2.2.natAbs ≤ 2 ^ ((a.1.length + C.n a.1) ^ k + k)

end KarpPapadimitriou.Generator


