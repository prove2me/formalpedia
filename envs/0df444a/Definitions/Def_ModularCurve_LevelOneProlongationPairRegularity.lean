-- Prove2me | Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
-- name    : ModularCurve_LevelOneProlongationPairRegularity
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/be6b7bd6-6b3e-5b3b-a2b9-a42376303a2a
-- title:
--   Regularity law for a level-one prolongation pair
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ with a ring map $\mathrm{red}\colon A\to k$, modular polynomial data for $q$ with its Kronecker congruence, the two Hecke integrality hypotheses at level one, a place specialisation $P$ over these data, and a level-one prolongation pair $R$ for $P$; write $\rho_1,\rho_2$ for the two residue maps $R.\mathrm{residue}_1,R.\mathrm{residue}_2$, which send the valuation rings `R.R₁.integers`, `R.R₂.integers` inside the geometric level-$q$ modular function field `modularFunctionFieldBar (1 * q)` into `modularFunctionFieldC k 1`, and $\varphi$ for `frobOnPlacesGeomLevel k 1 data hKr` acting on the places of `modularFunctionFieldC k 1` over $k$.
--
--   For a finite set $S_0\subseteq k$, the predicate `RegularityLaw S₀` is the conjunction of two clauses, both quantified over every $f$ in the level-$q$ field lying in both valuation rings. First: for every place $v$ with $\varphi(\varphi v)=v$ and $v\neq P.\mathrm{redFst}$ of the cusp $\infty$ at level $q$, if $\operatorname{ord}_W f\ge 0$ for every place $W$ of the level-$q$ field with $P.\mathrm{redFst}\,W=v$, then $\operatorname{ord}_v(\rho_1 f)\ge 0$ whenever $\rho_1 f\neq 0$, and $\operatorname{ord}_{\varphi v}(\rho_2 f)\ge 0$ whenever $\rho_2 f\neq 0$. Second: for every $a\in S_0$ with $a^{q^2}=a$, if $\operatorname{ord}_W f\ge 0$ for every $W$ with $P.\mathrm{redFst}\,W$ equal to the place $j=a$ (the first component of `frobNodePair q a`), then there is a single $c\in k$ such that $\rho_1 f$ has value $c$ at the place $j=a$ and $\rho_2 f$ has value $c$ at the place $j=a^q$. No non-vanishing of $c$ is demanded, in contrast with `LevelOneProlongationPair.NodeValueLaw`, where $c\neq 0$ is required and the admissible $j$-invariants are those in `ssJSet q k`. The module asserts nothing; it only names this proposition.
--
--   **Relation to Mathlib.** The places, order functions, value predicate and prolongation structures involved are the project's own constructions ([`AlgebraicCurve.RegularProlongation`](../def/AlgebraicCurve_RegularProlongation.html#L16) and the modular function fields built from Laurent-series $q$-expansions); Mathlib has no counterpart.
--
--   **Where it is used.** The proposition packages the regularity input on the image side of the reduction of the modular curve of level $q$ in characteristic $q$: the first clause places the residues of a function integral for both branches into the expected Riemann–Roch spaces at the places fixed by $\varphi^2$, and the second makes the resulting pair of residues agree at the crossing points indexed by $S_0$, so that pairs of functions on the two components glue. It is used as a hypothesis in the construction of functions on the glued special fibre, which feeds the analysis of the component group and the Eichler–Shimura relation at $q$ in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LevelOneProlongationPairRegularity.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve

namespace PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

namespace LevelOneProlongationPair

variable {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : LevelOneProlongationPair P)

open Classical in

def RegularityLaw (S₀ : Finset k) : Prop :=
  (∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
      (v : Place k (modularFunctionFieldC k 1)),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
      v ≠ P.redFst (cuspInftyBar (1 * q)) →
      (∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), P.redFst W = v → 0 ≤ W.ord f) →
      (R.residue₁ ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (R.residue₂ ⟨f, h₂⟩ ≠ 0 → 0 ≤ (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨f, h₂⟩))) ∧
  (∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      ∀ a ∈ S₀, a ^ (q ^ 2) = a →
      (∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
          P.redFst W = (frobNodePair q a).1 → 0 ≤ W.ord f) →
      ∃ c : k, (frobNodePair q a).1.HasValue (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k 1) c ∧
               (frobNodePair q a).2.HasValue (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k 1) c)

end LevelOneProlongationPair

end PlaceSpecialization

end ModularCurve

end


