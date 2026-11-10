-- Prove2me | Definitions.Def_ApproxCactus_Main_Crossing
-- name    : ApproxCactus_Main_Crossing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:01:06.968602+00:00
-- url     : https://prove2.me/theorems/8d7a04b3-a270-42a9-a786-345d25f8046d
-- title:
--   Centres and links of crossing separations, corners, equitable and criss-compatible sets, uniformly crossing and asteriskal sets
-- statement:
--   For separations $s=(A,B)$ and $t=(C,D)$: the **$st$-centre** is $(A\cap B)\cap(C\cap D)$, the **$sC$-link** is $(A\cap B)\cap(C\setminus D)$ and the **$sD$-link** is $(A\cap B)\cap(D\setminus C)$ (with the roles exchanged, the $tA$- and $tB$-links). The **corner separations** are $(A\cap C,B\cup D)$, $(A\cap D,B\cup C)$, $(B\cap C,A\cup D)$, $(B\cap D,A\cup C)$, and the **corners** are $(A\setminus B)\cap(C\setminus D)$, $(A\setminus B)\cap(D\setminus C)$, $(B\setminus A)\cap(C\setminus D)$, $(B\setminus A)\cap(D\setminus C)$.
--
--   Two $k$-separations **cross equitably** if all four corner separations have order exactly $k$; a set is **equitable** if any two crossing elements cross equitably. Two separations **$\varepsilon$-criss** if all four corners have more than $\varepsilon$ vertices; a set is **$\varepsilon$-criss-compatible** if any two crossing elements $\varepsilon$-criss.
--
--   A set $S$ is **uniformly $\gamma$-crossing** if for each $s=(A,B)\in S$ there is a tripartition $(X,\{P,Q\})$ of $A\cap B$ (parts may be empty, $\{P,Q\}$ unordered) such that every $t\in S$ that $\gamma$-crosses $s$ has $st$-centre $X$ and $\{sC\text{-link},sD\text{-link}\}=\{P,Q\}$; "uniformly crossing" is uniformly $0$-crossing. $S$ is **$\gamma$-crossing-connected** if $S\ne\emptyset$ and the reflexive–transitive closure of "$\gamma$-crosses" on $S$ together with the pairs $(s,s^*)$, $s\in S$, relates every two elements of $S$. $S$ is **$\gamma$-asteriskal** if it is uniformly $\gamma$-crossing, $\gamma$-crossing-connected and symmetric, and it is **trivial** if it equals $\{s,s^*\}$ for a single separation $s$.
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), pp. 36, 38, 41, 45 (PDF 39, 41, 44, 48), §4.2–4.5, §5.1, §6

import Definitions.Def_ApproxCactus_Main_Separations

namespace ApproxCactus.Main

/-- The **`st`-centre** of `s = (A, B)` and `t = (C, D)`: `(A ∩ B) ∩ (C ∩ D)` (p. 36). -/
def centre2 {V : Type*} [DecidableEq V] (s t : Finset V × Finset V) : Finset V :=
  (s.1 ∩ s.2) ∩ (t.1 ∩ t.2)

/-- The **`sC`-link** of `s = (A, B)` and `t = (C, D)`: `(A ∩ B) ∩ (C ∖ D)`; with the arguments
swapped, `linkFst t s = (C ∩ D) ∩ (A ∖ B)` is the `tA`-link (= the `At`-link) (p. 36). -/
def linkFst {V : Type*} [DecidableEq V] (s t : Finset V × Finset V) : Finset V :=
  (s.1 ∩ s.2) ∩ (t.1 \ t.2)

/-- The **`sD`-link** of `s = (A, B)` and `t = (C, D)`: `(A ∩ B) ∩ (D ∖ C)`; `linkSnd t s` is the
`tB`-link (= the `Bt`-link) (p. 36). -/
def linkSnd {V : Type*} [DecidableEq V] (s t : Finset V × Finset V) : Finset V :=
  (s.1 ∩ s.2) ∩ (t.2 \ t.1)

/-- The four **corner separations** of `s = (A, B)` and `t = (C, D)` (p. 36):
`AC = (A ∩ C, B ∪ D)`, `AD = (A ∩ D, B ∪ C)`, `BC = (B ∩ C, A ∪ D)`, `BD = (B ∩ D, A ∪ C)`. -/
def cornerSeps {V : Type*} [DecidableEq V] (s t : Finset V × Finset V) :
    List (Finset V × Finset V) :=
  [(s.1 ∩ t.1, s.2 ∪ t.2), (s.1 ∩ t.2, s.2 ∪ t.1),
   (s.2 ∩ t.1, s.1 ∪ t.2), (s.2 ∩ t.2, s.1 ∪ t.1)]

/-- The four **corners** of `s = (A, B)` and `t = (C, D)` (p. 41):
`(A ∖ B) ∩ (C ∖ D)`, `(A ∖ B) ∩ (D ∖ C)`, `(B ∖ A) ∩ (C ∖ D)`, `(B ∖ A) ∩ (D ∖ C)`. -/
def corners {V : Type*} [DecidableEq V] (s t : Finset V × Finset V) : List (Finset V) :=
  [(s.1 \ s.2) ∩ (t.1 \ t.2), (s.1 \ s.2) ∩ (t.2 \ t.1),
   (s.2 \ s.1) ∩ (t.1 \ t.2), (s.2 \ s.1) ∩ (t.2 \ t.1)]

/-- Two `k`-separations **cross equitably**: all four corner separators have size exactly `k`
(p. 38). -/
def CrossEquitably {V : Type*} [DecidableEq V] (k : ℕ) (s t : Finset V × Finset V) : Prop :=
  ∀ c ∈ cornerSeps s t, order c = k

/-- A set `S` of `k`-separations is **equitable**: whenever two elements of `S` cross, they cross
equitably (p. 38). -/
def IsEquitable {V : Type*} [DecidableEq V] (k : ℕ) (S : Set (Finset V × Finset V)) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, Crosses s t → CrossEquitably k s t

/-- `s` and `t` **`ε`-criss**: all four corners have size `> ε` (p. 38). -/
def Criss {V : Type*} [DecidableEq V] (ε : ℕ) (s t : Finset V × Finset V) : Prop :=
  ∀ c ∈ corners s t, ε < c.card

/-- `S` is **`ε`-criss-compatible**: whenever two separations in `S` cross, they `ε`-criss
(p. 38). -/
def IsCrissCompatible {V : Type*} [DecidableEq V] (ε : ℕ) (S : Set (Finset V × Finset V)) :
    Prop :=
  ∀ s ∈ S, ∀ t ∈ S, Crosses s t → Criss ε s t

/-- `S` is **uniformly `γ`-crossing** (p. 38): for each `s = (A, B) ∈ S` there is a tripartition
`(X, {P, Q})` of `A ∩ B` (parts may be empty, `{P, Q}` unordered) such that every `t = (C, D) ∈ S`
that `γ`-crosses `s` induces it on `A ∩ B`: `X` is the `st`-centre and `{P, Q}` is
`{sC-link, sD-link}`. Uniformly crossing = uniformly `0`-crossing. -/
def IsUniformlyCrossing {V : Type*} [DecidableEq V] (γ : ℕ) (S : Set (Finset V × Finset V)) :
    Prop :=
  ∀ s ∈ S, ∃ X P Q : Finset V,
    (X ∪ P ∪ Q = s.1 ∩ s.2 ∧ Disjoint X P ∧ Disjoint X Q ∧ Disjoint P Q) ∧
    ∀ t ∈ S, CrossEps γ t s →
      centre2 s t = X ∧
        ((linkFst s t = P ∧ linkSnd s t = Q) ∨ (linkFst s t = Q ∧ linkSnd s t = P))

/-- `S` is **`γ`-crossing-connected** (p. 45): `S ≠ ∅` and the reflexive–transitive closure of the
union of the relation "`γ`-crosses" on `S` with `{(s, s∗) : s ∈ S}` has exactly one class. -/
def IsCrossingConnected {V : Type*} [DecidableEq V] (γ : ℕ) (S : Set (Finset V × Finset V)) :
    Prop :=
  S.Nonempty ∧ ∀ s ∈ S, ∀ t ∈ S,
    Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ (CrossEps γ a b ∨ b = a.swap)) s t

/-- `S` is **`γ`-asteriskal** (p. 45): uniformly `γ`-crossing, `γ`-crossing-connected and
symmetric. -/
def IsAsteriskal {V : Type*} [DecidableEq V] (γ : ℕ) (S : Set (Finset V × Finset V)) : Prop :=
  IsUniformlyCrossing γ S ∧ IsCrossingConnected γ S ∧ IsSymmetric S

/-- A (`γ`-asteriskal) set is **trivial** if it consists of a single separation and its inverse
(p. 45). -/
def IsTrivialSet {V : Type*} (S : Set (Finset V × Finset V)) : Prop :=
  ∃ s : Finset V × Finset V, S = {s, s.swap}

end ApproxCactus.Main


