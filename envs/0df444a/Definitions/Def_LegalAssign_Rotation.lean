-- Prove2me | Definitions.Def_LegalAssign_Rotation
-- name    : LegalAssign_Rotation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:51.328997+00:00
-- url     : https://prove2.me/theorems/5ed759cd-25a1-4df2-bf56-cdef973be67f
-- title:
--   Rotations exposed in a stable assignment, their elimination, and elimination sequences (corrected: s_M has a vacancy clause and a rotation follows next_M)
-- statement:
--   Let $X$ be one side of the bipartition and $Y$ the other, with $q$ extended to students by $q_a=1$. For an assignment $M$ and $x\in X$, $s_M(x)$ is the first agent $y\notin M(x)$ on the list of $x$ such that $x>_y x'$ for some $x'\in M(y)$ or $|M(y)|<q_y$. If $y:=s_M(x)$ exists and $|M(y)|=q_y$, then $\mathrm{next}_M(x)$ is the least preferred element of $M(y)$; if $|M(y)|<q_y$, then $\mathrm{next}_M(x)=\emptyset$.
--
--   Given distinct $x_0,\dots,x_{r-1}\in X$ and distinct $y_0,\dots,y_{r-1}\in Y$, the cycle $y_0,x_0,y_1,x_1,\dots,y_{r-1},x_{r-1}$ is an **$X$-rotation exposed in $M$** if, for all $i$ with indices taken modulo $r$,
--   $$x_iy_i\in M,\qquad s_M(x_i)=y_{i+1},\qquad \mathrm{next}_M(x_i)=x_{i+1}.$$
--   The **elimination** of $\rho$ maps $M$ to
--   $$M/\rho:=\bigl(M\setminus\{x_iy_i\}\bigr)\cup\{x_iy_{i+1}\}.$$
--   An **elimination sequence** from $M$ to $M'$ is a list of rotations, each exposed in the assignment produced by the preceding eliminations, ending at $M'$. Two rotations are the same when they have the same sets $\{(x_i,y_i)\}$ and $\{(x_i,y_{i+1})\}$, so a cyclic shift of the indices changes nothing.
--
--   Rotations describe how one stable assignment turns into another. Student-rotations move toward the school-optimal stable assignment and school-rotations toward the student-optimal one.
--
--   **Corrections to the source.** The source's definition (p.9) omits two clauses. Its $s_M$ has no vacancy clause, and its displayed condition for a rotation omits $\mathrm{next}_M(x_i)=x_{i+1}$, although the following sentences identify rotations with the directed cycles of the digraph with arcs $(x,s_M(x))$ and $(s_M(x),\mathrm{next}_M(x))$. With either clause missing, Lemma 4.2 is false; the docstrings of `IsEligible` and `IsExposed` give counterexamples. The elimination formula corrects the typo $M'(x_i)=(M'(x_i)\setminus\{y_i\})\cup\{y_{i+1}\}$.
--
--   **Formalization Note** `Side` packages the choice of $X$ and $Y$; `G.studentSide` takes $X=A$, and `G.schoolSide` takes $X=B$ with quotas $1$ on students. Assignments stay in `Finset (A × B)`, and `pair x y` writes the edge $xy$ there. `Rotation` has length $r=n+1$ and $i+1$ in `Fin (n + 1)` is the index modulo $r$. `IsNext` has no witness when $\mathrm{next}_M(x)=\emptyset$. `rotationKeys` is the set of rotations of a list.
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, §4, p.9 (s_M, next_M, X-rotations, digraph D_X, elimination)

import Mathlib
import Definitions.Def_LegalAssign_Instance

namespace LegalAssign

/-- One choice of the sides `X`, `Y` of the bipartition of an instance, as in "choosing `X` to be
one side of the bipartition and `Y` the other" (arXiv:1809.08506v2, §4, p.9). `pair x y` is the edge
`xy` written in `A × B`; `quotaY` is `q`, extended to students by `q_a = 1`. -/
structure Side (A B X Y : Type*) where
  /-- The edge set of the instance. -/
  edges : Finset (A × B)
  /-- The edge `xy` as an element of `A × B`. -/
  pair : X → Y → A × B
  /-- `prefX x y y'` is `y >_x y'`. -/
  prefX : X → Y → Y → Prop
  /-- `prefY y x x'` is `x >_y x'`. -/
  prefY : Y → X → X → Prop
  /-- The quota of `y`. -/
  quotaY : Y → ℕ

/-- A cycle `y_0, x_0, y_1, x_1, …, y_{r-1}, x_{r-1}` with distinct `x_i` and distinct `y_i`
(arXiv:1809.08506v2, §4, p.9). Here `r = n + 1`, so `i + 1` in `Fin (n + 1)` is the index modulo `r`.

**Formalization Note** The source gives no lower bound on `r`. The value `r = 1` needs no exclusion:
`y_1 = y_0 ∈ M(x_0)` contradicts `s_M(x_0) ∉ M(x_0)`. -/
structure Rotation (X Y : Type*) where
  /-- `r - 1`. -/
  n : ℕ
  /-- The `x_i`. -/
  x : Fin (n + 1) → X
  /-- The `y_i`. -/
  y : Fin (n + 1) → Y
  x_injective : Function.Injective x
  y_injective : Function.Injective y

/-- The identity of a rotation: the pair `({(x_i, y_i)}, {(x_i, y_{i+1})})`, which a cyclic shift of
the indices does not change. -/
def Rotation.key {X Y : Type*} (ρ : Rotation X Y) : Set (X × Y) × Set (X × Y) :=
  (Set.range fun i => (ρ.x i, ρ.y i), Set.range fun i => (ρ.x i, ρ.y (i + 1)))

/-- The set of rotations occurring in a list of rotations, compared through `Rotation.key`. -/
def rotationKeys {X Y : Type*} (l : List (Rotation X Y)) : Set (Set (X × Y) × Set (X × Y)) :=
  {k | ∃ ρ ∈ l, ρ.key = k}

namespace Side

variable {A B X Y : Type*} [DecidableEq A] [DecidableEq B] [Fintype X] [Fintype Y]

/-- `M(y) = {x : xy ∈ M}` (arXiv:1809.08506v2, §2.1, p.6). -/
def partnersY (V : Side A B X Y) (M : Finset (A × B)) (y : Y) : Finset X :=
  Finset.univ.filter fun x => V.pair x y ∈ M

/-- `y` is eligible for `s_M(x)`: `xy ∈ E`, `y ∉ M(x)`, and either `x >_y x'` for some `x' ∈ M(y)`
or `|M(y)| < q_y`.

**Formalization Note** (correction of arXiv:1809.08506v2, §4, p.9) The printed condition is only
"`x >_y x'` for some `x' ∈ M(y)`". The vacancy clause `|M(y)| < q_y` is added: the source's own
`next_M(x) = ∅` case and the seat reduction of §2.2 need it (an empty seat prefers every student),
and without it Lemma 4.2 is false. Counterexample: students `x₀, x₁, t`, schools `y₀, y₁` of quota
`1` and `z` of quota `2`; `x₀ : y₀ > z > y₁`, `x₁ : y₁ > y₀`, `t : z`; `y₀ : x₁ > x₀`, `y₁ : x₀ > x₁`,
`z : t > x₀`. Then `M = {x₀y₀, x₁y₁, tz}` is stable, the printed definition gives `s_M(x₀) = y₁`,
`s_M(x₁) = y₀`, and `M/ρ = {x₀y₁, x₁y₀, tz}` is blocked by `x₀z`, because `z` has a free seat. -/
def IsEligible (V : Side A B X Y) (M : Finset (A × B)) (x : X) (y : Y) : Prop :=
  V.pair x y ∈ V.edges ∧ V.pair x y ∉ M ∧
    ((∃ x' ∈ V.partnersY M y, V.prefY y x x') ∨ (V.partnersY M y).card < V.quotaY y)

/-- `y = s_M(x)`: `y` is the first eligible agent on `x`'s list (arXiv:1809.08506v2, §4, p.9, with
the vacancy clause of `IsEligible`). -/
def IsSucc (V : Side A B X Y) (M : Finset (A × B)) (x : X) (y : Y) : Prop :=
  V.IsEligible M x y ∧ ∀ y', V.IsEligible M x y' → y' ≠ y → V.prefX x y y'

/-- `x' = next_M(x)` (arXiv:1809.08506v2, §4, p.9): `y := s_M(x)` exists, `|M(y)| = q_y`, and `x'`
is the least preferred element of `M(y)`. When `|M(y)| < q_y` no `x'` satisfies this, which is the
source's `next_M(x) = ∅`. -/
def IsNext (V : Side A B X Y) (M : Finset (A × B)) (x x' : X) : Prop :=
  ∃ y, V.IsSucc M x y ∧ (V.partnersY M y).card = V.quotaY y ∧ x' ∈ V.partnersY M y ∧
    ∀ x'' ∈ V.partnersY M y, x'' ≠ x' → V.prefY y x'' x'

/-- `ρ` is an `X`-rotation exposed in `M` (arXiv:1809.08506v2, §4, p.9): `x_i y_i ∈ M`,
`s_M(x_i) = y_{i+1}` and `next_M(x_i) = x_{i+1}`.

**Formalization Note** (correction of arXiv:1809.08506v2, §4, p.9) The printed displayed condition
is only "`x_i y_i ∈ M` and `s_M(x_i) = y_{i+1}`". The clause `next_M(x_i) = x_{i+1}` comes from the
source's next sentences, which identify rotations with the directed cycles of the digraph `D_X` with
arcs `(x, s_M(x))` and `(s_M(x), next_M(x))`. Without it Lemma 4.2 is false for quotas `≥ 2`.
Counterexample: students `x₀, x₁, w₀, w₁`, schools `y₀, y₁` of quota `2`; `x₀ : y₀ > y₁`,
`x₁ : y₁ > y₀`, `w₀ : y₀`, `w₁ : y₁`; `y₀ : x₀ > x₁ > w₀`, `y₁ : x₁ > x₀ > w₁`. Then
`M = {x₀y₀, w₀y₀, x₁y₁, w₁y₁}` is stable and `y₀, x₀, y₁, x₁` meets the printed condition, but
`M/ρ = {x₀y₁, w₀y₀, x₁y₀, w₁y₁}` is blocked by `x₀y₀`. -/
def IsExposed (V : Side A B X Y) (M : Finset (A × B)) (ρ : Rotation X Y) : Prop :=
  ∀ i, V.pair (ρ.x i) (ρ.y i) ∈ M ∧ V.IsSucc M (ρ.x i) (ρ.y (i + 1)) ∧
    V.IsNext M (ρ.x i) (ρ.x (i + 1))

/-- The elimination `M/ρ := (M \ {x_i y_i}) ∪ {x_i y_{i+1}}` (arXiv:1809.08506v2, §4, p.9).

**Formalization Note** The source's formula `M'(x_i) = (M'(x_i) \ {y_i}) ∪ {y_{i+1}}` has `M'` on both
sides, a typo for `M(x_i)` on the right. -/
def eliminate (V : Side A B X Y) (M : Finset (A × B)) (ρ : Rotation X Y) : Finset (A × B) :=
  (M \ Finset.univ.image fun i => V.pair (ρ.x i) (ρ.y i)) ∪
    Finset.univ.image fun i => V.pair (ρ.x i) (ρ.y (i + 1))

/-- `IsEliminationPath M l M'`: starting from `M`, the rotations of `l` are eliminated in order, each
exposed in the current assignment, and the result is `M'` (arXiv:1809.08506v2, Lemma 4.2, p.9). -/
inductive IsEliminationPath (V : Side A B X Y) :
    Finset (A × B) → List (Rotation X Y) → Finset (A × B) → Prop
  | nil (M : Finset (A × B)) : IsEliminationPath V M [] M
  | cons (M : Finset (A × B)) (ρ : Rotation X Y) (l : List (Rotation X Y)) (M' : Finset (A × B)) :
      V.IsExposed M ρ → IsEliminationPath V (V.eliminate M ρ) l M' →
      IsEliminationPath V M (ρ :: l) M'

end Side

namespace Instance

variable {A B : Type*}

/-- The side `X = A` (students), `Y = B` (schools). -/
def studentSide (G : Instance A B) : Side A B A B where
  edges := G.E
  pair a b := (a, b)
  prefX := G.prefA
  prefY := G.prefB
  quotaY := G.q

/-- The side `X = B` (schools), `Y = A` (students), with `q` extended by `q_a = 1`
(arXiv:1809.08506v2, §4, p.9). -/
def schoolSide (G : Instance A B) : Side A B B A where
  edges := G.E
  pair b a := (a, b)
  prefX := G.prefB
  prefY := G.prefA
  quotaY _ := 1

end Instance

end LegalAssign


