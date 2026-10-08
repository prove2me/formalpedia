-- Prove2me | Definitions.Def_SingleMachinePrec_ConvexBipartite_Realizer
-- name    : SingleMachinePrec_ConvexBipartite_Realizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:13:01.336934+00:00
-- url     : https://prove2.me/theorems/a84695ad-d576-4861-ba18-56bb4b5ab039
-- title:
--   Incomparable pairs, linear extensions and realizers of a poset (Section 2.1)
-- statement:
--   Let $P$ be a binary relation on a set $N$ of jobs (in the applications, a partial order). Following §2.1 of Ambühl, Mastrolilli, Mutsanas and Svensson, this file fixes four notions.
--
--   1. **Incomparability.** Two elements $x, y \in N$ are *incomparable*, written $x \parallel y$, when neither $(x,y) \in P$ nor $(y,x) \in P$. The set of incomparable pairs is $\mathrm{inc}(P)$.
--   2. **Linear extension.** A relation $L$ on $N$ is a *linear extension* of $P$ when $L$ is a linear order on $N$ (reflexive, antisymmetric, transitive and total) and $P \subseteq L$.
--   3. **Reversal.** A linear order $L$ *reverses* the pair $(x, y)$ when $y < x$ in $L$, that is, $(y,x) \in L$ and $y \neq x$.
--   4. **Realizer.** A family $L_1, \dots, L_t$ of linear extensions of $P$ is a *realizer of size $t$* (a $1$-fold realizer of size $t$, or $t$-realizer) when every incomparable pair is reversed by at least one member:
--   $$
--   \forall (x,y) \in \mathrm{inc}(P)\ \ \exists i \in \{1,\dots,t\}:\ y <_{L_i} x .
--   $$
--
--   The *dimension* $\dim(P)$ of a poset is the least $t$ for which a realizer of size $t$ exists; these notions are the language in which the dimension bound of Lemma 4.1 is stated.
--
--   **Formalization Note** Relations are predicates `N → N → Prop`; linear orders use Mathlib's unbundled class `IsLinearOrder`. A realizer of size $t$ is a function `Fin t → N → N → Prop`, so repeated members (a multiset, as in the paper) are allowed.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 655, Section 2.1

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_Poset

namespace SingleMachinePrec.ConvexBipartite

/-- `L` is a *linear extension* of `P`: `L` is a linear order (reflexive, antisymmetric,
transitive and total) on the same ground set and `P ⊆ L` (§2.1, p. 655). -/
def IsLinearExtension {N : Type*} (P L : N → N → Prop) : Prop :=
  IsLinearOrder N L ∧ ∀ x y, P x y → L x y

/-- The linear order `L` *reverses* the pair `(x, y)` when `y < x` in `L`, i.e. `(y, x) ∈ L` and
`y ≠ x` (§2.1, p. 655). -/
def Reverses {N : Type*} (L : N → N → Prop) (x y : N) : Prop :=
  L y x ∧ y ≠ x

/-- A *realizer of size `t`* (a 1-fold realizer of size `t`, §2.1, p. 655) of `P` is a family
`L_1, …, L_t` of linear extensions of `P` such that every incomparable pair `(x, y)` of `P` is
reversed by at least one `L_i`. -/
def IsRealizer {N : Type*} {t : ℕ} (P : N → N → Prop) (L : Fin t → N → N → Prop) : Prop :=
  (∀ i, IsLinearExtension P (L i)) ∧
    ∀ x y, SingleMachinePrec.Framework.Incomparable P x y → ∃ i, Reverses (L i) x y

end SingleMachinePrec.ConvexBipartite


