-- Prove2me | Definitions.Def_AggCG_Gadget
-- name    : AggCG_Gadget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:07:13.665662+00:00
-- url     : https://prove2.me/theorems/17dff7f5-5c80-493d-bb5e-e8b77c3a39a5
-- title:
--   The gadgets $L(a,\beta;S)$ and $G(a,\beta;S)$ and the family $X_m$
-- statement:
--   For naturals $a,\beta$ and a set $S$ of rows, two programs on the variables $(x,y)$ with $x,y\le 1$ as structural bounds. Every row outside $S$ reads $y\le 0$, and
--   $$L(a,\beta;S):\ \max x\ \text{ with } ax\le\beta \text{ in each } t\in S;\qquad G(a,\beta;S):\ \max(-x)\ \text{ with } -ax\le-\beta \text{ in each } t\in S.$$
--   Write $\sigma=\sum_{t\in S}u_t$. A gadget is **admissible** when $a>\beta\ge 1$ and $S$ is nonempty with $S\subsetneq[m]$. It lies in the **family $X_m$** when moreover $a\le 8$ and $|S|\le 3$.
--
--   All hardness and capacity statements of the mission live on this family.
--
--   **Formalization Note** $a,\beta$ are natural numbers, the integral data of §I.1. The condition $S\subsetneq[m]$ is kept explicit in $X_m$: it comes from the definition of the gadgets and is automatic only at $m\ge 4$. The dummy rows force $y=0$, and the $y$ column of the cut is kept, since $\lfloor\sum_{t\notin S}u_t\rfloor$ may be positive.
-- source:
--   Sharma, Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms, STOC 2027 submission (manuscript sha256 f7ea0248…), §I.1, p.49 (PDF p.50); Proposition I.4, p.52 (PDF p.53)

import Mathlib
import Definitions.Def_AggCG_IP

namespace AggCG

/-- The two gadget types `L` and `G`. -/
inductive GKind where
  | L
  | G
  deriving DecidableEq

/-- The data `(a, β, S)` of a gadget and its type (Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), §I.1, p.49, PDF p.50). -/
structure Gadget (m : ℕ) where
  /-- `L` or `G`. -/
  kind : GKind
  /-- The coefficient `a`. -/
  a : ℕ
  /-- The right-hand side `β`. -/
  β : ℕ
  /-- The row set `S`. -/
  S : Finset (Fin m)

namespace Gadget

variable {m : ℕ}

/-- The programs of p.49 on binary variables `(x, y)` (`x` is index `0`, `y` is index `1`), "with box bounds structural rather than multiplier rows.
Every row outside S reads y ≤ 0":
`L(a, β; S) : max x with ax ≤ β in each t ∈ S`; `G(a, β; S) : max(−x) with −ax ≤ −β in each t ∈ S`.

**Formalization Note** `a, β` are naturals, the "integral data" of §I.1. -/
def toIP (G : Gadget m) : IP m 2 where
  A := fun t j =>
    if t ∈ G.S then
      (if j = 0 then (match G.kind with | .L => (G.a : ℚ) | .G => -(G.a : ℚ)) else 0)
    else
      (if j = 1 then 1 else 0)
  b := fun t =>
    if t ∈ G.S then (match G.kind with | .L => (G.β : ℚ) | .G => -(G.β : ℚ)) else 0
  c := fun j => if j = 0 then (match G.kind with | .L => 1 | .G => -1) else 0
  ub := fun _ => some 1

/-- `σ = Σ_{t ∈ S} u_t`, p.49. -/
noncomputable def sigma (G : Gadget m) (u : Fin m → ℝ) : ℝ := ∑ t ∈ G.S, u t

/-- The hypotheses of p.49: "any a > β ≥ 1 and nonempty S ⊊ [m]". -/
def Admissible (G : Gadget m) : Prop :=
  1 ≤ G.β ∧ G.β < G.a ∧ G.S.Nonempty ∧ G.S ≠ Finset.univ

/-- Membership in the family `X_m` of Proposition I.4, p.52 (PDF p.53): `1 ≤ β < a ≤ 8` and `1 ≤ |S| ≤ 3`.

**Formalization Note** `S ⊊ [m]` stays explicit, since it comes from the definition of the gadgets (p.49) and is automatic only at `m ≥ 4`. -/
def Valid (G : Gadget m) : Prop :=
  G.Admissible ∧ G.a ≤ 8 ∧ G.S.card ≤ 3

end Gadget

end AggCG


