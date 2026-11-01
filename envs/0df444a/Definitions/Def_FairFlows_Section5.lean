-- Prove2me | Definitions.Def_FairFlows_Section5
-- name    : FairFlows_Section5
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:26.240814+00:00
-- url     : https://prove2.me/theorems/c2eab6cc-2c71-4bd4-b2ea-67d80beace57
-- title:
--   The setting (5.1), pre-dec-min flows, dual optimal chains, the tightened bounds (5.2)–(5.3) and $L'$
-- statement:
--   Let $D=(V,A)$, $F\subseteq A$, bounds $f\le g$ and $m$ with $\widetilde m(V)=0$.
--
--   1. $\beta:=\max\{g(e):e\in F\}$, $L:=\{e\in F: g(e)=\beta\}$, $g^-:=g-\chi_L$.
--   2. The **setting (5.1)**: $f$ and $g$ finite on $F$; $F$ non-empty with no $(f,g)$-tight edges; Q⃛$=$Q⃛$(f,g;m)\neq\emptyset$; Q⃛$(f,g^-;m)=\emptyset$.
--   3. $z\in$ Q⃛ is **pre-dec-min on $F$** if the number $\mu$ of edges $e\in L$ with $z(e)=\beta$ is as small as possible.
--   4. For a chain $\mathcal C'$, the criteria (O1)–(O5) of Theorem 5.1 are those of Theorem 4.6 with $g(e)$ replaced by $\beta$ on $L$. A **dual optimal chain** is a chain $\mathcal C'$ of non-empty proper subsets of $V$ with $\varrho_g(V_i)-\delta_f(V_i)<+\infty$ such that a member of Q⃛ is pre-dec-min on $F$ if and only if it satisfies (O1)–(O5).
--   5. The **tightened bounds** $(f',g')$ of (5.2)–(5.3): for $e\in L$, $(\beta,\beta)$ if $e$ enters at least two members of $\mathcal C'$, $(\beta-1,\beta)$ if exactly one, $(f(e),f(e))$ if it leaves a member, $(f(e),\beta-1)$ otherwise; for $e\in A-L$, $(g(e),g(e))$ if $e$ enters a member, $(f(e),f(e))$ if it leaves one, $(f(e),g(e))$ otherwise.
--   6. $L'$ is the set of edges of $L$ entering at least one member of $\mathcal C'$.
--
--   These are the objects of the inductive step of the proof of Theorem 2.1.
--
--   **Formalization Note** The §5 assumption that the underlying undirected graph is connected is not part of the setting. In a chain no edge enters one member and leaves another, so the cases of (5.2)–(5.3) are exclusive. Finite values are read through `untopD 0`/`unbotD 0` only where (5.1) or the finite cuts of a dual optimal chain make them finite; $\max$ over $F$ is read on the non-empty $F$ of (5.1).
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, §5 p.13 (standing assumptions, (5.1), pre-dec-min), Theorem 5.1 pp.13–14 ((O1)–(O5)), p.14 (dual optimal chain, (5.2), (5.3), (5.4), L′)

import Mathlib
import Definitions.Def_FairFlows_Covering
import Definitions.Def_FairFlows_MaxMinimizer

set_option autoImplicit false

namespace FairFlows

open Finset

variable {V A : Type}

/-- `β := max{g(e) : e ∈ F}` of (5.1) (Frank, Murota, *Fair integral network flows*,
arXiv:1907.02673v5, §5, p.13).

**Formalization Note** Under (5.1) `g` is finite on the non-empty set `F`, so
`(g e).untopD 0` is the integer `g(e)` for `e ∈ F` and `beta` is the maximum. -/
def beta (g : A → WithTop ℤ) (F : Finset A) : ℤ :=
  maxOn F (fun e => (g e).untopD 0)

/-- `L := {e ∈ F : g(e) = β}` of (5.1) (arXiv:1907.02673v5, p.13). -/
def Lset [DecidableEq A] (g : A → WithTop ℤ) (F : Finset A) : Finset A :=
  F.filter (fun e => g e = ((beta g F : ℤ) : WithTop ℤ))

/-- The assumptions (5.1) together with the standing assumptions of §5 (arXiv:1907.02673v5,
§5, p.13):

1. `m̃(V) = 0` and `f ≤ g`;
2. `−∞ < f(e) ≤ g(e) < +∞` for every `e ∈ F`;
3. `F` is non-empty and contains no `(f, g)`-tight edges;
4. `Q⃛ = Q⃛(f, g; m)` is non-empty;
5. `Q⃛(f, g⁻; m)` is empty, where `β := max{g(e) : e ∈ F}`, `L := {e ∈ F : g(e) = β}` and
   `g⁻ := g − χ_L`.

**Formalization Note** The §5 assumption that the underlying undirected graph of `D` is
connected is not included: nothing in §§4–5 uses it, and Theorem 2.1 does not assume it. -/
def Setting51 [Fintype V] [Fintype A] [DecidableEq A] [DecidableEq V] (D : Digraph V A)
    (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (F : Finset A) : Prop :=
  demandSum m univ = 0 ∧ BoundsLE f g ∧
  (∀ e ∈ F, f e ≠ ⊥ ∧ g e ≠ ⊤) ∧
  F.Nonempty ∧ (∀ e ∈ F, ¬ IsTight f g e) ∧
  (intFlows D f g m).Nonempty ∧
  intFlows D f (shiftOn g (Lset g F) (-1)) m = ∅

/-- `z` is pre-decreasingly minimal (pre-dec-min) on `F`: `z ∈ Q⃛` and the number `µ` of edges
`e ∈ L` with `z(e) = β` is as small as possible over `Q⃛` (arXiv:1907.02673v5, p.13). -/
def IsPreDecMin [Fintype A] [DecidableEq A] [DecidableEq V] (D : Digraph V A)
    (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (F : Finset A) (z : A → ℤ) : Prop :=
  z ∈ intFlows D f g m ∧ ∀ y ∈ intFlows D f g m,
    ((Lset g F).filter (fun e => z e = beta g F)).card ≤
      ((Lset g F).filter (fun e => y e = beta g F)).card

/-- The optimality criteria (O1)–(O5) of Theorem 5.1 (arXiv:1907.02673v5, pp.13–14) for an
integral flow `z` and a chain `C′`, with `β` and `L` from (5.1):

* (O1) `z(e) = f(e)` for every edge `e ∈ A` leaving a member of `C′`;
* (O2) `z(e) = g(e)` for every edge `e ∈ A − L` entering a member of `C′`;
* (O3) `β − 1 ≤ z(e) ≤ β` for every edge `e ∈ L` entering exactly one member of `C′`;
* (O4) `z(e) = β` for every edge `e ∈ L` entering at least two members of `C′`;
* (O5) `f(e) ≤ z(e) ≤ β − 1` for every edge `e ∈ L` neither entering nor leaving any member of
  `C′`. -/
def PreDecMinCriteria [DecidableEq A] [DecidableEq V] (D : Digraph V A) (f : A → WithBot ℤ)
    (g : A → WithTop ℤ) (F : Finset A) (C : Finset (Finset V)) (z : A → ℤ) : Prop :=
  (∀ e : A, (∃ Z ∈ C, D.Leaves e Z) → ((z e : ℤ) : WithBot ℤ) = f e) ∧
  (∀ e : A, e ∉ Lset g F → (∃ Z ∈ C, D.Enters e Z) → ((z e : ℤ) : WithTop ℤ) = g e) ∧
  (∀ e ∈ Lset g F, enterCount D C e = 1 → beta g F - 1 ≤ z e ∧ z e ≤ beta g F) ∧
  (∀ e ∈ Lset g F, 2 ≤ enterCount D C e → z e = beta g F) ∧
  (∀ e ∈ Lset g F, (¬ ∃ Z ∈ C, D.Enters e Z) → (¬ ∃ Z ∈ C, D.Leaves e Z) →
      f e ≤ ((z e : ℤ) : WithBot ℤ) ∧ z e ≤ beta g F - 1)

/-- A dual optimal chain (arXiv:1907.02673v5, p.14: "a chain with the properties in the
theorem [5.1]"): a chain `C′ = {V₁ ⊃ V₂ ⊃ ⋯ ⊃ V_q}` of non-empty proper subsets of `V` with
`ϱ_g(Vᵢ) − δ_f(Vᵢ) < +∞` such that a member `z` of `Q⃛` is pre-dec-min on `F` if and only if
it satisfies (O1)–(O5).

**Formalization Note** The chain is a finite family of distinct sets, totally ordered by `⊆`;
the empty chain is allowed. -/
def IsDualOptimalChain [Fintype V] [Fintype A] [DecidableEq A] [DecidableEq V]
    (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (F : Finset A)
    (C : Finset (Finset V)) : Prop :=
  IsChain (· ⊆ ·) (C : Set (Finset V)) ∧
  (∀ Z ∈ C, Z.Nonempty ∧ Z ≠ univ ∧ FiniteCut D f g Z) ∧
  ∀ z ∈ intFlows D f g m, IsPreDecMin D f g m F z ↔ PreDecMinCriteria D f g F C z

/-- The tightened lower bound `f′` of (5.2)–(5.3) (arXiv:1907.02673v5, p.14). For `e ∈ L`:
`β` if `e` enters at least two members of `C′`; `β − 1` if it enters exactly one; `f(e)` if it
leaves a member or neither enters nor leaves any. For `e ∈ A − L`: `g(e)` if `e` enters a member
of `C′`, `f(e)` otherwise.

**Formalization Note** In a chain no edge both enters one member and leaves another, so the
cases of (5.2) and (5.3) are exclusive and the order of the `if`s is immaterial. For a dual
optimal chain every edge entering a member has `g(e)` finite (`FiniteCut`), so
`(g e).untopD 0` is the integer `g(e)` wherever it is used. -/
def fPrime [DecidableEq A] [DecidableEq V] (D : Digraph V A) (f : A → WithBot ℤ)
    (g : A → WithTop ℤ) (F : Finset A) (C : Finset (Finset V)) : A → WithBot ℤ :=
  fun e =>
    if e ∈ Lset g F then
      (if 2 ≤ enterCount D C e then ((beta g F : ℤ) : WithBot ℤ)
       else if enterCount D C e = 1 then ((beta g F - 1 : ℤ) : WithBot ℤ)
       else f e)
    else
      (if ∃ Z ∈ C, D.Enters e Z then (((g e).untopD 0 : ℤ) : WithBot ℤ) else f e)

/-- The tightened upper bound `g′` of (5.2)–(5.3) (arXiv:1907.02673v5, p.14). For `e ∈ L`:
`β` if `e` enters at least one member of `C′`; `f(e)` if it leaves a member; `β − 1` if it
neither enters nor leaves any. For `e ∈ A − L`: `g(e)` if `e` enters a member; `f(e)` if it
leaves a member; `g(e)` otherwise.

**Formalization Note** For a dual optimal chain every edge leaving a member has `f` finite and
`f` is finite on `L ⊆ F`, so `(f e).unbotD 0` is the integer `f(e)` wherever it is used. -/
def gPrime [DecidableEq A] [DecidableEq V] (D : Digraph V A) (f : A → WithBot ℤ)
    (g : A → WithTop ℤ) (F : Finset A) (C : Finset (Finset V)) : A → WithTop ℤ :=
  fun e =>
    if e ∈ Lset g F then
      (if 1 ≤ enterCount D C e then ((beta g F : ℤ) : WithTop ℤ)
       else if ∃ Z ∈ C, D.Leaves e Z then (((f e).unbotD 0 : ℤ) : WithTop ℤ)
       else ((beta g F - 1 : ℤ) : WithTop ℤ))
    else
      (if ∃ Z ∈ C, D.Enters e Z then g e
       else if ∃ Z ∈ C, D.Leaves e Z then (((f e).unbotD 0 : ℤ) : WithTop ℤ)
       else g e)

/-- `L′`: the edges of `L` entering at least one member of `C′` (arXiv:1907.02673v5, p.14). -/
def Lprime [DecidableEq A] [DecidableEq V] (D : Digraph V A) (g : A → WithTop ℤ) (F : Finset A)
    (C : Finset (Finset V)) : Finset A :=
  (Lset g F).filter (fun e => ∃ Z ∈ C, D.Enters e Z)

end FairFlows


