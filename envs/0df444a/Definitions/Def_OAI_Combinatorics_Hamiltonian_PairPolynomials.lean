-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
-- name    : OAI_Combinatorics_Hamiltonian_PairPolynomials
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:34:53.883995+00:00
-- url     : https://prove2.me/theorems/935fbd2d-b2cd-4e19-aab6-148f2c3b2a37
-- title:
--   Weight polynomials, orbit slopes and third-corner classes of paired triangle states
-- statement:
--   This file sets up the polynomial bookkeeping for sums over pairs of states of a triangle system.
--
--   **Setting.** A triangle system $T$ consists of a finite set $A$ of triangles and a set $V$ of points; each triangle $t\in A$ has three distinct corners $T(t,0),T(t,1),T(t,2)\in V$, indexed by $\mathbb{Z}/3$, and two distinct triangles never share two corners. Fix $X\subseteq V$. A *state* is a map $s:A\to\mathbb{Z}/3$ such that $t\mapsto T(t,s(t))$ is a bijection from $A$ onto $X$. Two states $r,s$ are *partners* if $r(t)\neq s(t)$ for every $t\in A$, and a *pair* $P=(\ell,\rho)$ is an ordered pair of partner states (the left and the right state). The *successor permutation* $\sigma_P$ of $A$ sends $t$ to the triangle whose left corner is the right corner of $t$, that is, $T(\sigma_P(t),\ell(\sigma_P(t)))=T(t,\rho(t))$; its orbits are called the orbits of $P$. The *third-corner function* of $P$ is $\theta_P(t)=-(\ell(t)+\rho(t))\in\mathbb{Z}/3$, the index of the corner of $t$ used by neither state. For $j,k\in\mathbb{Z}/3$ put $\delta(j,k)=0$ if $k=j$, $\delta(j,k)=1$ if $k=j+1$, and $\delta(j,k)=-1$ if $k=j-1$. For $n\in\mathbb{Z}$ put $\operatorname{ph}(n)=\mathrm{i}^{\lfloor n/3\rfloor}\in\mathbb{C}$. A *weight* $w$ assigns a real number $w_t(k)$ to each corner $k$ of each triangle $t$, and $z$ denotes the polynomial indeterminate.
--
--   1. **Linear products.** For a commutative ring $R$, a finite set $s\subseteq A$ and $a:A\to R$,
--   $$
--   L_s(a)=\prod_{t\in s}\bigl(1+a_t\,z\bigr)\in R[z],
--   $$
--   and the constant coefficient of $L_s(a)$ equals $1$.
--   2. **Two phase values.** $\operatorname{ph}(3)=\mathrm{i}$ and $\operatorname{ph}(-3)=-\mathrm{i}$.
--   3. **Orbit faces and orbit index sums.** For an orbit $c$ of $P$, $A_c\subseteq A$ is the set of triangles lying in $c$, and
--   $$
--   \Delta_P(c)=\sum_{t\in A_c}\delta\bigl(\ell(t),\rho(t)\bigr)\in\mathbb{Z}.
--   $$
--   4. **Reorientation along orbits.** For a choice $b$ of a truth value for every orbit of $P$, the reoriented pair $P^b=(\ell^b,\rho^b)$ exchanges left and right on the orbits marked true. The file records the formulas $\ell^b(t)=\rho(t)$ and $\rho^b(t)=\ell(t)$ if the orbit of $t$ is marked true, and $\ell^b(t)=\ell(t)$, $\rho^b(t)=\rho(t)$ otherwise.
--   5. **Weight polynomials.** For a state $s$ and an orbit $c$ of $P$, the state weight and the left and right orbit weights are
--   $$
--   W_w(s)=\prod_{t\in A}\bigl(1+w_t(s(t))\,z\bigr),\qquad W^{\ell}_w(P,c)=\prod_{t\in A_c}\bigl(1+w_t(\ell(t))\,z\bigr),\qquad W^{\rho}_w(P,c)=\prod_{t\in A_c}\bigl(1+w_t(\rho(t))\,z\bigr),
--   $$
--   all in $\mathbb{C}[z]$.
--   6. **The signed term of a pair.**
--   $$
--   \operatorname{term}_w(P)=\operatorname{ph}\Bigl(\sum_{t\in A}\delta\bigl(\ell(t),\rho(t)\bigr)\Bigr)\,W_w(\rho)\in\mathbb{C}[z].
--   $$
--   7. **Orbit slopes.** $\operatorname{slope}_w(P,c)=\sum_{t\in A_c}w_t(\rho(t))-\sum_{t\in A_c}w_t(\ell(t))\in\mathbb{R}$, the difference of the coefficients of $z$ in $W^{\rho}_w(P,c)$ and $W^{\ell}_w(P,c)$.
--   8. **Third-corner classes.** $\mathcal{G}$ is the finite set of all functions $A\to\mathbb{Z}/3$ of the form $\theta_P$, and the class of a pair $P$ is $\theta_P\in\mathcal{G}$. Each $\tau\in\mathcal{G}$ has a chosen representative pair $P_\tau$ with $\theta_{P_\tau}=\tau$, and the pairs of class $\tau$ are identified with the group of $P_\tau$, namely the set of pairs $Q$ with $\theta_Q=\theta_{P_\tau}$.
--   9. **Pairs with a given right state.** For a state $s$, the map $r\mapsto(r,s)$ is a bijection from the set of partners of $s$ onto the set of pairs whose right state is $s$.
--
--   The polynomial $\sum_P\operatorname{term}_w(P)$, summed over all pairs, can be expanded class by class (item 8), where the pairs of one class differ from each other by exchanging left and right along whole orbits, or according to the right state (item 9). Orbit index sums and orbit slopes measure how such an exchange along one orbit changes the phase and the weights; they are the data used to locate the first nonzero coefficient of this polynomial and to prove its nonvanishing under sign conditions on the orbits.
--
--   **Formalization Note** The point set and the indeterminate are both called `X` in Lean (`ℂ[X]` is `Polynomial ℂ`). The phase is `phase n = Complex.I ^ (n / 3)` with Lean's integer division, which for the divisor $3$ is the floor. Orbits are elements of `CycleClass P.next`, the quotient of $A$ by the same-cycle relation of $\sigma_P$. The Lean names are `linearProduct`, `cycleFaces`, `cycleDelta`, `stateWeight`, `cycleLeftWeight`, `cycleRightWeight`, `term`, `cycleSlope`, `GroupIndex` (with `groupIndex` and a representative chosen by `Classical.choose`); items 8 and 9 are the equivalences `GroupIndex.fiberEquivGroup` and `secondFiberEquiv`, and the remaining members are simp lemmas. Real weights are cast to complex numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/PairPolynomials.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/PairPolynomials.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BarnetteHamiltonian mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases

namespace OAI

/-! First nonzero coefficients of paired-state polynomials. -/

namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

noncomputable def linearProduct {A R : Type*} [CommRing R] (s : Finset A) (a : A → R) : R[X] :=
  ∏ t ∈ s, (1 + C (a t) * X)

@[simp] theorem linearProduct_coeff_zero {A R : Type*} [CommRing R]
    (s : Finset A) (a : A → R) : (linearProduct s a).coeff 0 = 1 := by
  simp [linearProduct, coeff_zero_prod]

end Barnette

namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

@[simp] theorem phase_three : phase 3 = Complex.I := by norm_num [phase]
@[simp] theorem phase_neg_three : phase (-3) = -Complex.I := by norm_num [phase, Complex.inv_I]

namespace TriangleSystem.Pair

variable {A V : Type*} [Fintype A] {T : TriangleSystem A V} {X : Set V}

noncomputable def cycleFaces (P : @Pair A V T X) (c : CycleClass P.next) : Finset A := by
  classical
  exact Finset.univ.filter (fun t => classOf P.next t = c)

@[simp] theorem mem_cycleFaces (P : @Pair A V T X) (c : CycleClass P.next) (t : A) :
    t ∈ P.cycleFaces c ↔ classOf P.next t = c := by
  classical
  simp [cycleFaces]

noncomputable def cycleDelta (P : @Pair A V T X) (c : CycleClass P.next) : ℤ :=
  ∑ t ∈ P.cycleFaces c, indexDelta (P.left.val t) (P.right.val t)

omit [Fintype A] in
@[simp] theorem orient_left_val (P : @Pair A V T X) (b : CycleClass P.next → Bool) (t : A) :
    (P.orient b).val.left.val t =
      if b (classOf P.next t) then P.right.val t else P.left.val t := rfl

omit [Fintype A] in
@[simp] theorem orient_right_val (P : @Pair A V T X) (b : CycleClass P.next → Bool) (t : A) :
    (P.orient b).val.right.val t =
      if b (classOf P.next t) then P.left.val t else P.right.val t := rfl

noncomputable def stateWeight (w : A → Fin 3 → ℝ) (s : T.State X) : ℂ[X] :=
  linearProduct Finset.univ (fun t => (w t (s.val t) : ℂ))

noncomputable def cycleLeftWeight (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next) : ℂ[X] :=
  linearProduct (P.cycleFaces c) (fun t => (w t (P.left.val t) : ℂ))

noncomputable def cycleRightWeight (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next) : ℂ[X] :=
  linearProduct (P.cycleFaces c) (fun t => (w t (P.right.val t) : ℂ))

noncomputable def term (w : A → Fin 3 → ℝ) (P : @Pair A V T X) : ℂ[X] :=
  C (phase (rawIndexSum P.left P.right)) * stateWeight w P.right

end TriangleSystem.Pair
end Barnette
namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

namespace TriangleSystem.Pair

variable {A V : Type*} [Fintype A] {T : TriangleSystem A V} {X : Set V}

noncomputable def cycleSlope (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next) : ℝ :=
  (∑ t ∈ P.cycleFaces c, w t (P.right.val t)) -
    ∑ t ∈ P.cycleFaces c, w t (P.left.val t)

def GroupIndex : Type _ := Set.range (@third A V T X)

noncomputable instance : Fintype (@GroupIndex A V T X) :=
  Fintype.ofFinite (Set.range (@third A V T X))

noncomputable def GroupIndex.representative (d : @GroupIndex A V T X) : @Pair A V T X :=
  Classical.choose d.property

omit [Fintype A] in
theorem GroupIndex.representative_third (d : @GroupIndex A V T X) : d.representative.third = d.val :=
  Classical.choose_spec d.property

def groupIndex (P : @Pair A V T X) : @GroupIndex A V T X := ⟨P.third, P, rfl⟩

noncomputable def GroupIndex.fiberEquivGroup (d : @GroupIndex A V T X) :
    {P : @Pair A V T X // P.groupIndex = d} ≃ d.representative.Group :=
  Equiv.subtypeEquivRight (fun P => by
    constructor
    · intro h
      have hh := congrArg Subtype.val h
      change P.third = d.val at hh
      exact hh.trans d.representative_third.symm
    · intro h
      apply Subtype.ext
      exact h.trans d.representative_third)

end TriangleSystem.Pair
end Barnette
namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

namespace TriangleSystem.Pair

variable {A V : Type*} [Fintype A] {T : TriangleSystem A V} {X : Set V}

noncomputable def secondFiberEquiv (s : T.State X) :
    {P : @Pair A V T X // P.right = s} ≃ T.Partners s where
  toFun P := ⟨P.val.left,
    Eq.mp (congrArg (fun z => T.Partner P.val.left z) P.property) P.val.partner⟩
  invFun r := ⟨⟨(r.val, s), r.property⟩, rfl⟩
  left_inv P := by
    apply Subtype.ext
    apply Pair.ext
    · rfl
    · exact P.property.symm
  right_inv _ := rfl

end TriangleSystem.Pair
end Barnette

end OAI


