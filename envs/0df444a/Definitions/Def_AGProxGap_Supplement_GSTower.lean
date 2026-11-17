-- Prove2me | Definitions.Def_AGProxGap_Supplement_GSTower
-- name    : AGProxGap_Supplement_GSTower
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:15:53.481909+00:00
-- url     : https://prove2.me/theorems/c44efa4d-4de7-47fa-8376-919585d2dc17
-- title:
--   The Garcia–Stichtenoth tower $F_0\subseteq F_1\subseteq\cdots$
-- statement:
--   Let $q=s^2$ with $s$ a prime power and let $x_0$ be transcendental over $\mathbb F_q$. The **Garcia–Stichtenoth tower** is
--   $$F_0=\mathbb F_q(x_0),\qquad F_{j+1}=F_j(y_{j+1}),\quad\text{where } y_{j+1}^s+y_{j+1}=x_j^{s+1},\quad x_{j+1}=\frac{y_{j+1}}{x_j}.$$
--   The datum consists of an ambient field $\Omega\supseteq\mathbb F_q$, the element $x_0$, and elements $x_j,y_{j+1}\in\Omega$ satisfying these relations; the fields $F_j$ are the intermediate fields they generate. Also defined: $x_0$ as an element of $F_j$, and $b_j=[F_j:F_0]$.
--
--   The tower is asymptotically optimal (its genus-to-points ratio attains the Drinfeld–Vlăduţ bound), and the paper's counterexamples (§5) are one-point AG codes at its levels.
--
--   **Formalization Note** Statements quantify over every datum, i.e. every ambient field and every choice of the roots $y_{j+1}$; since $Y^s+Y-x_j^{s+1}$ is irreducible over $F_j$, every choice gives the same tower up to isomorphism. $b_j$ is Mathlib's relative degree of $F_j$ over $F_0$.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.4, p.15

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

namespace AGProxGap.Supplement

/-- **The Garcia–Stichtenoth tower** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.4, p.15: "let q = s², where s is a prime power,
and let x_0 be an indeterminate over F_q. We use the Garcia-Stichtenoth tower [GS95], defined
recursively by F_0 = F_q(x_0), F_{j+1} = F_j(y_{j+1}), where y_{j+1}^s + y_{j+1} = x_j^{s+1} and
x_{j+1} = y_{j+1}/x_j").

A tower datum inside a field `Ω` containing `F_q` consists of:
1. an element `x_0 ∈ Ω` transcendental over `F_q` (the indeterminate);
2. elements `x_j, y_{j+1} ∈ Ω` (`j ≥ 0`) with `x 0 = x_0`,
   `y_{j+1}^s + y_{j+1} = x_j^{s+1}` and `x_{j+1} = y_{j+1}/x_j`.

The fields `F_j` are `GSTower.field`.

**Formalization Note** The tower is realized inside an ambient field `Ω`, and every statement
quantifies over every such datum (every `Ω` and every choice of roots `y_{j+1}`): this is not a
restriction, because by [GS95] the polynomial `Y^s + Y − x_j^{s+1}` is irreducible over `F_j`, so
every choice of root gives the same tower up to isomorphism. The relations `q = s²` and "`s` a
prime power" are hypotheses of the statements that use the tower. `x_j ≠ 0` is a consequence
(`x_0 ≠ 0` and `y_{j+1} ≠ 0` since `x_j^{s+1} ≠ 0`), so the division is a true quotient. -/
structure GSTower (Fq : Type u) (Ω : Type v) [Field Fq] [Field Ω] [Algebra Fq Ω] (s : ℕ) where
  /-- The indeterminate `x_0`. -/
  x0 : Ω
  /-- `x_0` is transcendental over `F_q`. -/
  transcendental : Transcendental Fq x0
  /-- The elements `x_j`. -/
  x : ℕ → Ω
  /-- The elements `y_j` (only `y_{j+1}`, `j ≥ 0`, are used). -/
  y : ℕ → Ω
  x_zero : x 0 = x0
  /-- `y_{j+1}^s + y_{j+1} = x_j^{s+1}`. -/
  eqn : ∀ j, y (j + 1) ^ s + y (j + 1) = x j ^ (s + 1)
  /-- `x_{j+1} = y_{j+1}/x_j`. -/
  x_succ : ∀ j, x (j + 1) = y (j + 1) / x j

namespace GSTower

variable {Fq : Type u} {Ω : Type v} [Field Fq] [Field Ω] [Algebra Fq Ω] {s : ℕ}

/-- The field `F_j` of the tower: `F_0 = F_q(x_0)`, `F_{j+1} = F_j(y_{j+1})`, as intermediate
fields of `Ω/F_q` (§2.4, p.15). -/
def field (T : GSTower Fq Ω s) : ℕ → IntermediateField Fq Ω
  | 0 => IntermediateField.adjoin Fq {T.x0}
  | j + 1 => IntermediateField.adjoin Fq (insert (T.y (j + 1)) (field T j : Set Ω))

theorem x0_mem_field (T : GSTower Fq Ω s) : ∀ j, T.x0 ∈ T.field j
  | 0 => IntermediateField.subset_adjoin Fq _ (Set.mem_singleton _)
  | j + 1 => IntermediateField.subset_adjoin Fq _ (Set.mem_insert_of_mem _ (x0_mem_field T j))

/-- The function `x = x_0` as an element of the function field `F_j` of level `j`. -/
def x0At (T : GSTower Fq Ω s) (j : ℕ) : T.field j :=
  ⟨T.x0, T.x0_mem_field j⟩

/-- `b_j = [F_j : F_0]` (§2.4, p.15), the degree of `F_j` over `F_0 = F_q(x_0)` (Mathlib's
`IntermediateField.relfinrank`, which is `[F_j : F_0]` since `F_0 ⊆ F_j`). -/
noncomputable def b (T : GSTower Fq Ω s) (j : ℕ) : ℕ :=
  IntermediateField.relfinrank (T.field 0) (T.field j)

end GSTower

end AGProxGap.Supplement


