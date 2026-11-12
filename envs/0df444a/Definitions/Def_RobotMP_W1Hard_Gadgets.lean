-- Prove2me | Definitions.Def_RobotMP_W1Hard_Gadgets
-- name    : RobotMP_W1Hard_Gadgets
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:41:44.868244+00:00
-- url     : https://prove2.me/theorems/07561e72-c556-46c2-a4fc-c5edbadb4dc0
-- title:
--   The synchronizer, odometer and tester constraint systems of the constraint gadget (§9.3)
-- statement:
--   A constraint system has named integer data variables and named $\{0,1\}$ control variables; a configuration assigns a value to each, and is allowed if it satisfies every constraint. A **move** changes a single variable between two allowed configurations; a configuration is **reachable** from another inside a set of allowed configurations if a finite sequence of moves through that set joins them.
--
--   Fix $n \in \mathbb N$. The **synchronizer** has data variables $y_1, y_2, y_3 \in \{0, \dots, n\}$, $z_1, z_2, z_3 \in \{0, \dots, n^2 - 1\}$, and controls $c, q, r_1, r_2, r_3$, with constraints
--   - $y_1 - y_2,\ y_1 - y_3,\ y_2 - y_3 \in \{0,1\}$ and $z_1 - z_2,\ z_1 - z_3,\ z_2 - z_3 \in \{0,1\}$;
--   - $c \Rightarrow y_1 \le y_2$, $c \Rightarrow y_2 \le y_3$, $c \Rightarrow z_1 \le z_2$, $c \Rightarrow z_2 \le z_3$;
--   - $q \Rightarrow z_1 \le z_2$, $q \Rightarrow z_2 \le z_3$;
--   - $\neg r_1 \Rightarrow y_1 \ge y_3 + 1$, $\neg r_2 \Rightarrow y_1 \le y_2$, $\neg r_3 \Rightarrow y_2 \le y_3$;
--   - $r_1 \wedge \neg q \Rightarrow z_2 \le z_3$, $r_2 \wedge \neg q \Rightarrow z_1 \ge z_3 + 1$, $r_3 \wedge \neg q \Rightarrow z_1 \le z_2$.
--
--   The **odometer** adds data variables $x_1, x_2, x_3 \in \{0, \dots, n-1\}$ and controls $p_1, p_2$, with constraints
--   - $x_1 - x_2,\ x_2 - x_3,\ x_1 - x_3 \in \{0, 1\}$;
--   - $c \Rightarrow x_1 \le x_2$, $c \Rightarrow x_2 \le x_3$; $c \Rightarrow y_1 \le n - 1$;
--   - $p_1 \Rightarrow y_i \ge n$ and $p_2 \Rightarrow y_i \le 0$ for $i = 1, 2, 3$;
--   - $\neg p_1 \Rightarrow x_1 \le x_2$; $\neg p_2 \wedge q \Rightarrow x_1 \ge x_3 + 1$; $\neg q \Rightarrow x_2 \le x_3$.
--
--   For $T \subseteq \{0, \dots, n^2 - 1\}$ the **tester set** is
--   $$T' = \{(z_1, w_1) \in \{0, \dots, n^2 - 1\} \times \{0, \dots, n^2\} : w_1 \ge z_1 \text{ and } (z_1 = w_1 \Rightarrow z_1 \in T)\},$$
--   and the **tester** adds the data variable $w_1$ with constraints $c \Rightarrow w_1 \le z_1$ and $(z_1, w_1) \in T'$.
--
--   Three systems are defined: the synchronizer alone; synchronizer and odometer together; and, for $S \subseteq \{0, \dots, n-1\}^2$, the **constraint gadget**: synchronizer, odometer and the tester with $T = \{n i + j : (i, j) \in S\}$. The gadget's data variables are $x_1, y_1$ and the eight internal $x_2, x_3, y_2, y_3, z_1, z_2, z_3, w_1$; its controls are $c$ and the six internal $q, r_1, r_2, r_3, p_1, p_2$.
--
--   **Formalization Note.** The constraints use the extended forms the paper allows "for convenience" on p. 44 (conjunctions of two control literals, $+1$ offsets, comparisons with the constants $n - 1$, $n$, $0$), imposed directly rather than through the auxiliary variables of p. 44 and the three constant-valued data variables of p. 50. The printed odometer constraint "$\{x_1 - x_3\} \in \{0, 1\}$" is read as $x_1 - x_3 \in \{0, 1\}$. Variables are inductive types of names; control value `true` is $1$.
-- source:
--   Agarwal, Holmgren, Stade, Near-Optimal Makespan and Parameterized Hardness for Multi-Robot Motion Planning, STOC 2027 submission (manuscript sha256 17b4fe59…), pp. 44–52, §9.3 (synchronizer p. 47, odometer p. 50, tester pp. 51–52)

import Mathlib

set_option autoImplicit false

namespace RobotMP.W1Hard

open Set

/-! Constraint systems over named variables, with the extended constraint forms of §9.3 (p. 44),
and the three components of the constraint gadget of §9.3 (pp. 46–52). -/

/-- A configuration of a constraint system with data variables `D` (integer values) and control
variables `C` (values `false = 0`, `true = 1`). -/
abbrev GConfig (D C : Type) := (D → ℤ) × (C → Bool)

/-- `a` and `b` differ in at most one variable. -/
def SingleChange {D C : Type} (a b : GConfig D C) : Prop :=
  ((∃ d : D, ∀ d' : D, d' ≠ d → a.1 d' = b.1 d') ∧ a.2 = b.2) ∨
    (a.1 = b.1 ∧ ∃ c : C, ∀ c' : C, c' ≠ c → a.2 c' = b.2 c')

/-- One reconfiguration move inside the configurations allowed by `ok`. -/
def GStep {D C : Type} (ok : GConfig D C → Prop) (a b : GConfig D C) : Prop :=
  ok a ∧ ok b ∧ SingleChange a b

/-- `b` can be reached from `a` by moves through configurations allowed by `ok`. -/
def GReach {D C : Type} (ok : GConfig D C → Prop) (a b : GConfig D C) : Prop :=
  Relation.ReflTransGen (GStep ok) a b

/-- The synchronizer constraints (p. 47) with parameter `n`: `y₁, y₂, y₃ ∈ {0, …, n}`,
`z₁, z₂, z₃ ∈ {0, …, n² − 1}`, and
* `y₁ − y₂, y₁ − y₃, y₂ − y₃ ∈ {0, 1}`;
* `z₁ − z₂, z₁ − z₃, z₂ − z₃ ∈ {0, 1}`;
* `c ⇒ y₁ ≤ y₂`, `c ⇒ y₂ ≤ y₃`, `c ⇒ z₁ ≤ z₂`, `c ⇒ z₂ ≤ z₃`;
* `q ⇒ z₁ ≤ z₂`, `q ⇒ z₂ ≤ z₃`;
* `¬r₁ ⇒ y₁ ≥ y₃ + 1`, `¬r₂ ⇒ y₁ ≤ y₂`, `¬r₃ ⇒ y₂ ≤ y₃`;
* `r₁ ∧ ¬q ⇒ z₂ ≤ z₃`, `r₂ ∧ ¬q ⇒ z₁ ≥ z₃ + 1`, `r₃ ∧ ¬q ⇒ z₁ ≤ z₂`. -/
def syncConstraints (n : ℕ) (y₁ y₂ y₃ z₁ z₂ z₃ : ℤ) (c q r₁ r₂ r₃ : Bool) : Prop :=
  (y₁ ∈ Icc (0 : ℤ) n ∧ y₂ ∈ Icc (0 : ℤ) n ∧ y₃ ∈ Icc (0 : ℤ) n) ∧
  (z₁ ∈ Icc (0 : ℤ) ((n : ℤ) ^ 2 - 1) ∧ z₂ ∈ Icc (0 : ℤ) ((n : ℤ) ^ 2 - 1) ∧
    z₃ ∈ Icc (0 : ℤ) ((n : ℤ) ^ 2 - 1)) ∧
  (y₁ - y₂ ∈ ({0, 1} : Set ℤ) ∧ y₁ - y₃ ∈ ({0, 1} : Set ℤ) ∧ y₂ - y₃ ∈ ({0, 1} : Set ℤ)) ∧
  (z₁ - z₂ ∈ ({0, 1} : Set ℤ) ∧ z₁ - z₃ ∈ ({0, 1} : Set ℤ) ∧ z₂ - z₃ ∈ ({0, 1} : Set ℤ)) ∧
  ((c = true → y₁ ≤ y₂) ∧ (c = true → y₂ ≤ y₃) ∧ (c = true → z₁ ≤ z₂) ∧
    (c = true → z₂ ≤ z₃)) ∧
  ((q = true → z₁ ≤ z₂) ∧ (q = true → z₂ ≤ z₃)) ∧
  ((r₁ = false → y₁ ≥ y₃ + 1) ∧ (r₂ = false → y₁ ≤ y₂) ∧ (r₃ = false → y₂ ≤ y₃)) ∧
  ((r₁ = true ∧ q = false → z₂ ≤ z₃) ∧ (r₂ = true ∧ q = false → z₁ ≥ z₃ + 1) ∧
    (r₃ = true ∧ q = false → z₁ ≤ z₂))

/-- The odometer constraints (p. 50) with parameter `n`: `x₁, x₂, x₃ ∈ {0, …, n − 1}`, and
* `x₁ − x₂, x₂ − x₃, x₁ − x₃ ∈ {0, 1}`;
* `c ⇒ x₁ ≤ x₂`, `c ⇒ x₂ ≤ x₃`;
* `c ⇒ y₁ ≤ n − 1`;
* `p₁ ⇒ yᵢ ≥ n` for `i = 1, 2, 3`;
* `p₂ ⇒ yᵢ ≤ 0` for `i = 1, 2, 3`;
* `¬p₁ ⇒ x₁ ≤ x₂`;
* `¬p₂ ∧ q ⇒ x₁ ≥ x₃ + 1`;
* `¬q ⇒ x₂ ≤ x₃`. -/
def odometerConstraints (n : ℕ) (x₁ x₂ x₃ y₁ y₂ y₃ : ℤ) (c q p₁ p₂ : Bool) : Prop :=
  (x₁ ∈ Icc (0 : ℤ) ((n : ℤ) - 1) ∧ x₂ ∈ Icc (0 : ℤ) ((n : ℤ) - 1) ∧
    x₃ ∈ Icc (0 : ℤ) ((n : ℤ) - 1)) ∧
  (x₁ - x₂ ∈ ({0, 1} : Set ℤ) ∧ x₂ - x₃ ∈ ({0, 1} : Set ℤ) ∧ x₁ - x₃ ∈ ({0, 1} : Set ℤ)) ∧
  ((c = true → x₁ ≤ x₂) ∧ (c = true → x₂ ≤ x₃)) ∧
  (c = true → y₁ ≤ (n : ℤ) - 1) ∧
  (p₁ = true → y₁ ≥ n ∧ y₂ ≥ n ∧ y₃ ≥ n) ∧
  (p₂ = true → y₁ ≤ 0 ∧ y₂ ≤ 0 ∧ y₃ ≤ 0) ∧
  (p₁ = false → x₁ ≤ x₂) ∧
  (p₂ = false ∧ q = true → x₁ ≥ x₃ + 1) ∧
  (q = false → x₂ ≤ x₃)

/-- The tester set (p. 52) for `S ⊆ {0, …, n² − 1}`:
`S' = {(z₁, w₁) ∈ {0, …, n² − 1} × {0, …, n²} : w₁ ≥ z₁ and (z₁ = w₁ ⇒ z₁ ∈ S)}`. -/
def testerSet (n : ℕ) (S : Set ℤ) : Set (ℤ × ℤ) :=
  {p | p.1 ∈ Icc (0 : ℤ) ((n : ℤ) ^ 2 - 1) ∧ p.2 ∈ Icc (0 : ℤ) ((n : ℤ) ^ 2) ∧
    p.1 ≤ p.2 ∧ (p.1 = p.2 → p.1 ∈ S)}

/-- The tester constraints (pp. 51–52): `c ⇒ w₁ ≤ z₁` and `(z₁, w₁) ∈ S'` (this also puts
`w₁ ∈ {0, …, n²}`). -/
def testerConstraints (n : ℕ) (S : Set ℤ) (z₁ w₁ : ℤ) (c : Bool) : Prop :=
  (c = true → w₁ ≤ z₁) ∧ (z₁, w₁) ∈ testerSet n S

/-- Data variables of the synchronizer. -/
inductive SyncData
  | y1 | y2 | y3 | z1 | z2 | z3
  deriving DecidableEq

/-- Control variables seen by the synchronizer: the gadget's control `c`, and `q, r₁, r₂, r₃`. -/
inductive SyncCtrl
  | c | q | r1 | r2 | r3
  deriving DecidableEq

/-- The synchronizer as a constraint system on its own variables. -/
def SyncSystem (n : ℕ) (a : GConfig SyncData SyncCtrl) : Prop :=
  syncConstraints n (a.1 .y1) (a.1 .y2) (a.1 .y3) (a.1 .z1) (a.1 .z2) (a.1 .z3)
    (a.2 .c) (a.2 .q) (a.2 .r1) (a.2 .r2) (a.2 .r3)

/-- Data variables of the synchronizer together with the odometer. -/
inductive OdoData
  | x1 | x2 | x3 | y1 | y2 | y3 | z1 | z2 | z3
  deriving DecidableEq

/-- Control variables of the synchronizer together with the odometer. -/
inductive OdoCtrl
  | c | q | r1 | r2 | r3 | p1 | p2
  deriving DecidableEq

/-- The synchronizer and the odometer together, as one constraint system. -/
def SyncOdoSystem (n : ℕ) (a : GConfig OdoData OdoCtrl) : Prop :=
  syncConstraints n (a.1 .y1) (a.1 .y2) (a.1 .y3) (a.1 .z1) (a.1 .z2) (a.1 .z3)
      (a.2 .c) (a.2 .q) (a.2 .r1) (a.2 .r2) (a.2 .r3) ∧
    odometerConstraints n (a.1 .x1) (a.1 .x2) (a.1 .x3) (a.1 .y1) (a.1 .y2) (a.1 .y3)
      (a.2 .c) (a.2 .q) (a.2 .p1) (a.2 .p2)

/-- Data variables of the constraint gadget: the exposed `x₁, y₁` and the eight internal
`x₂, x₃, y₂, y₃, z₁, z₂, z₃, w₁`. -/
inductive GadgetData
  | x1 | x2 | x3 | y1 | y2 | y3 | z1 | z2 | z3 | w1
  deriving DecidableEq

/-- Control variables of the constraint gadget: the exposed `c` and the six internal
`q, r₁, r₂, r₃, p₁, p₂`. -/
inductive GadgetCtrl
  | c | q | r1 | r2 | r3 | p1 | p2
  deriving DecidableEq

/-- The constraint gadget for `S ⊆ {0, …, n − 1}²` (p. 52): synchronizer, odometer, and the
tester defined by the set `{n·i + j : (i, j) ∈ S}`. -/
def ConstraintGadget (n : ℕ) (S : Set (ℤ × ℤ)) (a : GConfig GadgetData GadgetCtrl) : Prop :=
  syncConstraints n (a.1 .y1) (a.1 .y2) (a.1 .y3) (a.1 .z1) (a.1 .z2) (a.1 .z3)
      (a.2 .c) (a.2 .q) (a.2 .r1) (a.2 .r2) (a.2 .r3) ∧
    odometerConstraints n (a.1 .x1) (a.1 .x2) (a.1 .x3) (a.1 .y1) (a.1 .y2) (a.1 .y3)
      (a.2 .c) (a.2 .q) (a.2 .p1) (a.2 .p2) ∧
    testerConstraints n {z | ∃ p ∈ S, z = (n : ℤ) * p.1 + p.2} (a.1 .z1) (a.1 .w1) (a.2 .c)

end RobotMP.W1Hard


