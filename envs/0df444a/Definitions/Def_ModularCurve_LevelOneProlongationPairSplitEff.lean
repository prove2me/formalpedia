-- Prove2me | Definitions.Def_ModularCurve_LevelOneProlongationPairSplitEff
-- name    : ModularCurve_LevelOneProlongationPairSplitEff
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/1ee6d81c-ccf4-5ec3-ac57-7413bd65ca12
-- title:
--   Effective split law for level-one prolongation pairs
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ with a ring homomorphism $red : A \to k$, modular polynomial data $data$ satisfying the Kronecker congruence, integrality hypotheses $h\alpha, h\beta$ for the two Hecke branches in level $1$ at $q$, a place specialisation $P$ for these data, and a level-one prolongation pair $R = (R_1, R_2)$ over $P$ (a pair of regular prolongations of the geometric function field of $X_0(q)$ over $A$, exchanged by the Fricke involution, together with the residue maps $R.\mathrm{residue}_1, R.\mathrm{residue}_2$ into the level-one function field $\mathrm{modularFunctionFieldC}\ k\ 1$). For a finite set $S_0 \subseteq k$ of moduli, `SplitLawEff S₀` asserts: for every divisor $E$ on $\mathrm{modularFunctionFieldBar}(1\cdot q)$ which is effective ($0 \le E W$ for all places $W$), which is invariant under the arithmetic Galois action of every element of the inertia subgroup of $A$ over $\mathbb{Q}$, and whose support avoids the first component of $\mathrm{frobNodePair}\ q\ a$ after reduction along $P.\mathrm{redFst}$ for every $a \in S_0$ with $a^{q^2} = a$ and $a \in \{0, 1728\}$, there exist divisors $D_1, D_2$ on $\mathrm{modularFunctionFieldC}\ k\ 1$ and a function $\mathrm{lam} : k \to k$ with $R.\mathrm{SplitDatum}\ S_0\ E\ D_1\ D_2\ \mathrm{lam}$.
--
--   The predicate `SplitDatum` packages: a sandwiching of $D_1$ and of $D_2 \circ \mathrm{Frob}$ between the pushforwards of the negative and positive parts of $E$ at Frobenius-fixed non-cuspidal places, the degree identity $\deg D_1 + \deg D_2 = \deg E$, nonvanishing of $\mathrm{lam}$ on $S_0$, agreement of $D_1, D_2$ with the pushforwards of $P.\mathrm{fstPart}\,E$, $P.\mathrm{sndPart}\,E$ away from the Frobenius-fixed places, the balance $D_1 v + D_2(\mathrm{Frob}\,v) = (P.\mathrm{redFst})_* E\,v$ at Frobenius-fixed non-cuspidal $v$, the two cusp conditions at $\infty$ and $0$, and, for each $f$ in the Riemann–Roch space of $E$ lying in both prolongation rings, membership of the two residues in the Riemann–Roch spaces of $D_1$, $D_2$ together with matching values at the two branches of each node $\mathrm{frobNodePair}\ q\ a$, $a \in S_0$ with $a^{q^2} = a$, up to the factor $\mathrm{lam}\,a$.
--
--   Thus `SplitLawEff` is the restriction of the split law of the preceding module to effective divisors $E$: it is implied by `SplitLaw` and is weaker than it.
--
--   **Relation to Mathlib.** Mathlib has no counterpart: this is a project predicate about the project's notions of modular function fields, place specialisations and regular prolongations.
--
--   **Where it is used.** The effective split law is the form of the splitting statement that is actually established for the integral model at $q$, and it is the input to the moving lemma for inertia-invariant divisor classes on $J_0(q)$ at $q$, where a given class is first replaced by an effective representative using the units $j - j(W)$ and a multiple of the cuspidal divisor. That moving lemma feeds the description of the reduction of $J_0(q)$ needed for the level-lowering step in the Frey–Serre–Ribet part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LevelOneProlongationPairSplitEff.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairSplit

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

def SplitLawEff (S₀ : Finset k) : Prop :=
  ∀ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))),
    (∀ W, 0 ≤ E W) →
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E = E) →
    (∀ W ∈ E.support, ∀ a ∈ S₀, a ^ (q ^ 2) = a → (a = 0 ∨ a = 1728) →
        P.redFst W ≠ (frobNodePair q a).1) →
    ∃ (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k), R.SplitDatum S₀ E D₁ D₂ lam

end LevelOneProlongationPair

end PlaceSpecialization

end ModularCurve

end


