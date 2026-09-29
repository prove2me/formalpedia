-- Prove2me | Definitions.Def_ModularCurve_LevelOneProlongationPairSplit
-- name    : ModularCurve_LevelOneProlongationPairSplit
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/285064d8-44a7-561b-b2c7-f774965bf92b
-- title:
--   Split data and split law for level-one prolongation pairs
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ with a ring map $\mathrm{red}\colon A\to k$, modular polynomial data with its Kronecker congruence and the two Hecke integrality hypotheses, a place specialisation $P$ at level one, and a prolongation pair $R=(R_1,R_2)$ for $P$, with residue maps $\mathrm{residue}_1,\mathrm{residue}_2$ into $k(\tilde\jmath)=$ `modularFunctionFieldC k 1`. Write $\varphi$ for the project's Frobenius map `frobOnPlacesGeomLevel` on places of $k(\tilde\jmath)$.
--
--   `SplitDatum` is a predicate on a finite set $S_0\subseteq k$, a divisor $E$ of the geometric level-$q$ function field, two divisors $D_1,D_2$ of $k(\tilde\jmath)$ and a function $\lambda\colon k\to k$; it is the conjunction of eight clauses. (i) At every $\varphi^2$-fixed place $v\neq \mathrm{red}_1(\bar\infty)$, both $D_1(v)$ and $D_2(\varphi v)$ lie between the $\mathrm{red}_1$-pushforward of the negative part of $E$ at $v$ and that of the positive part. (ii) $\deg D_1+\deg D_2=\deg E$. (iii) $\lambda(a)\neq0$ for $a\in S_0$. (iv) At places with $\varphi^2v\neq v$, $D_1$ and $D_2$ are the pushforwards along $\mathrm{red}_1$, $\mathrm{red}_2$ of the strict-type-one and strict-type-two parts `P.fstPart E`, `P.sndPart E`. (v) At $\varphi^2$-fixed $v\neq\mathrm{red}_1(\bar\infty)$, $D_1(v)+D_2(\varphi v)$ equals the full $\mathrm{red}_1$-pushforward of $E$ at $v$. (vi) At $\mathrm{red}_1(\bar\infty)$ and $\mathrm{red}_2(\bar 0)$, $D_1$ and $D_2$ agree with the pushforwards of the $\infty$-side and $0$-side parts of $E$ (as cut out by `P.IsInftySide`, `P.IsZeroSide`). (vii) Every $f\in L(E)$ lying in the integers of both $R_1$ and $R_2$ has $\mathrm{residue}_i f\in L(D_i)$, and (viii) for each $a\in S_0$ with $a^{q^2}=a$ there is $c\in k$ such that the place attached to $a$ takes the value $\lambda(a)\,c$ on $(\tilde\jmath-a)^{D_1}\,\mathrm{residue}_1 f$ while the place attached to $a^q$ takes the value $c$ on $(\tilde\jmath-a^q)^{D_2}\,\mathrm{residue}_2 f$; so $\lambda(a)$ is the prescribed ratio at the crossing.
--
--   `SplitLaw S₀` asserts: every divisor $E$ fixed by the inertia subgroup of $A$ in $\mathbb Q$ (acting through `arithmeticGalois` on the full level-$q$ function field) whose support avoids the places reducing to the node attached to $a\in S_0$ with $a^{q^2}=a$ and $a\in\{0,1728\}$ admits some $D_1,D_2,\lambda$ forming a split datum. Both declarations are `Prop`-valued; no data or instances are produced.
--
--   **Relation to Mathlib.** Places, divisors, degrees and Riemann–Roch spaces here are the project's own constructions in the `AlgebraicCurve` namespace (`Place`, `Divisor`, `riemannRochSpace` defined via valuation subrings and `Finsupp`s); Mathlib has no notion of split data for a pair of prolongations, nor of the modular objects involved.
--
--   **Where it is used.** These predicates package the two-sided reduction of Riemann–Roch spaces along the two Gauss prolongations attached to the two copies of the $\tilde\jmath$-line in the reduction of $X_0(q)$ at $q$, with $\lambda$ recording the gluing ratio at the supersingular crossings. They are consumed by the lifting statements for functions with prescribed reduction and by the assembly of the glued specialisation of $J_0(q)$ at $q$, which feeds the Eichler–Shimura and component-group input of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LevelOneProlongationPairSplit.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_SupersingularNodes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve

namespace PlaceSpecialization

namespace LevelOneProlongationPair

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : LevelOneProlongationPair P)

open Classical in

def SplitDatum (S₀ : Finset k)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k) : Prop :=

  (∀ v : Place k (modularFunctionFieldC k 1),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
      v ≠ P.redFst (cuspInftyBar (1 * q)) →
      Finsupp.mapDomain P.redFst (E.filter fun W => E W < 0) v ≤ D₁ v ∧
      D₁ v ≤ Finsupp.mapDomain P.redFst (E.filter fun W => 0 < E W) v ∧
      Finsupp.mapDomain P.redFst (E.filter fun W => E W < 0) v ≤ D₂ (frobOnPlacesGeomLevel k 1 data hKr v) ∧
      D₂ (frobOnPlacesGeomLevel k 1 data hKr v) ≤ Finsupp.mapDomain P.redFst (E.filter fun W => 0 < E W) v) ∧

  D₁.degree + D₂.degree = E.degree ∧

  (∀ a ∈ S₀, lam a ≠ 0) ∧

  (∀ v : Place k (modularFunctionFieldC k 1),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v →
      D₁ v = Finsupp.mapDomain P.redFst (P.fstPart E) v ∧
      D₂ v = Finsupp.mapDomain P.redSnd (P.sndPart E) v) ∧

  (∀ v : Place k (modularFunctionFieldC k 1),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
      v ≠ P.redFst (cuspInftyBar (1 * q)) →
      D₁ v + D₂ (frobOnPlacesGeomLevel k 1 data hKr v) = Finsupp.mapDomain P.redFst E v) ∧

  D₁ (P.redFst (cuspInftyBar (1 * q))) =
      Finsupp.mapDomain P.redFst (E.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q))) ∧
  D₂ (P.redSnd (cuspZeroBar (1 * q))) =
      Finsupp.mapDomain P.redSnd (E.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))) ∧

  ∀ (f : modularFunctionFieldBar (1 * q)), f ∈ riemannRochSpace E →
    ∀ (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k 1) ∈ riemannRochSpace D₁ ∧
      (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k 1) ∈ riemannRochSpace D₂ ∧
      ∀ a ∈ S₀, a ^ (q ^ 2) = a →
        ∃ c : k,
          (frobNodePair q a).1.HasValue
            (((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)
                - algebraMap k (modularFunctionFieldC k 1) a) ^ (D₁ (frobNodePair q a).1)
              * (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k 1)) (lam a * c) ∧
          (frobNodePair q a).2.HasValue
            (((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)
                - algebraMap k (modularFunctionFieldC k 1) (a ^ q)) ^ (D₂ (frobNodePair q a).2)
              * (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k 1)) c

open Classical in

def SplitLaw (S₀ : Finset k) : Prop :=
  ∀ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))),
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E = E) →
    (∀ W ∈ E.support, ∀ a ∈ S₀, a ^ (q ^ 2) = a → (a = 0 ∨ a = 1728) →
        P.redFst W ≠ (frobNodePair q a).1) →
    ∃ (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k), R.SplitDatum S₀ E D₁ D₂ lam

end LevelOneProlongationPair

end PlaceSpecialization

end ModularCurve

end


