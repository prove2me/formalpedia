-- Prove2me | Definitions.Def_ModularCurve_ProlongationTuple_JumpLaw
-- name    : ModularCurve_ProlongationTuple_JumpLaw
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/b1d838e6-88b5-5251-bc8f-cf5618b73712
-- title:
--   Jump law and one-sided regularity law for prolongation tuples
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \neq 0$, a field $k$ of characteristic $q$ with a ring homomorphism $\mathrm{red} \colon A \to k$, modular polynomial data satisfying the Kronecker congruence, the two integrality hypotheses for the Hecke correspondence branches, and a place specialisation $P$ attached to these data. For a prolongation tuple $R$ over $P$ — a pair of regular prolongations $R_1, R_2$ of $A$ from the geometric modular function field of level $Nq$ to the level-$N$ function field over the residue field of $A$, together with the compatibilities recorded in `ProlongationTuple` — two predicates are defined.
--
--   First, [`GaussJump.JumpLaw R`](../def/ModularCurve_ProlongationTuple_JumpLaw.html#L20) asserts: for every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$, every $f$ lying in both valuation rings `R.R₁.integers` and `R.R₂.integers`, and all divisors $D, E$ of the level-$Nq$ geometric function field such that every place in the support of $D$ satisfies `P.IsStrictFst` or `P.IsStrictSnd` (i.e. Frobenius carries its first reduction to its second, respectively conversely, with the Frobenius square moving the relevant place) and $D + (\sigma \cdot E - E) = \operatorname{div} f$ pointwise, one has: if the $R_1$-residue of $f$ is non-zero while its $R_2$-residue vanishes, then the part of $D$ supported on `P.IsStrictSnd` places has positive degree; and symmetrically with the two prolongations and the two strictness predicates exchanged.
--
--   Second, `ProlongationTuple.OneSidedRegularityLaw R W`, for $k$ perfect and $W$ a finite set of places of the level-$N$ function field over $k$, quantifies over the same $f$, $\sigma$, $D$, $E$ under the same two premises and asserts two clauses about the residues $\bar f_1, \bar f_2$ pushed to `modularFunctionFieldC k N`: at every affine geometric place $v$ fixed by the square of the Frobenius on places, $\bar f_1$ has non-negative order at $v$ if it is non-zero, and $\bar f_2$ has non-negative order at the Frobenius image of $v$ if it is non-zero; and at every node pair $(s_1, s_2) = (w, \mathrm{Frob} \cdot w)$ with $w \in W$, if $\bar f_1 \neq 0$ and $\bar f_2 = 0$ then $\bar f_1$ has positive order at $s_1$, while if $\bar f_2 \neq 0$ and $\bar f_1 = 0$ then $\bar f_2$ has positive order at $s_2$. Both are predicates only: nothing is asserted here about which tuples satisfy them.
--
--   **Relation to Mathlib.** Mathlib has no notion of place specialisation, regular prolongation or prolongation tuple; these, together with the divisor and place formalism (`Divisor`, `Place`, `Divisor.degree`) on which the two laws are stated, are the project's own.
--
--   **Where it is used.** The two laws belong to the axiomatic description of the reduction at $q$ of the modular curve of level $Nq$ as two copies of the level-$N$ curve glued along supersingular points, with the node pairs indexed by a finite set of places and the Frobenius twist. They are used, together with the divisor, cusp and splitting laws of the prolongation tuple, in the analysis of the specialisation of $J_0(Nq)$ and its component group that underlies the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ProlongationTuple_JumpLaw.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

noncomputable section

namespace GaussJump

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

open Classical in

def JumpLaw (R : ProlongationTuple P) : Prop :=
  ∀ σ ∈ A.inertiaSubgroupIn ℚ,
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    ∀ D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V) →
      (∀ V, D V + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) V = V.ord f) →
      (R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ = 0 →
          0 < Divisor.degree (D.filter P.IsStrictSnd)) ∧
        (R.R₂.residue ⟨f, h₂⟩ ≠ 0 → R.R₁.residue ⟨f, h₁⟩ = 0 →
          0 < Divisor.degree (D.filter P.IsStrictFst))

end GaussJump

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

namespace ProlongationTuple

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

open Classical in

def OneSidedRegularityLaw [PerfectField k] (W : Finset (Place k (modularFunctionFieldC k N))) : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    ∀ σ ∈ A.inertiaSubgroupIn ℚ,
    ∀ D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V) →
      (∀ V, D V + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) V = V.ord f) →
      (∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        IsAffineGeomPlace k N v →
      (R.residue₁ ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (R.residue₂ ⟨f, h₂⟩ ≠ 0 →
        0 ≤ (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩))) ∧
      (∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
        (R.residue₁ ⟨f, h₁⟩ ≠ 0 → R.residue₂ ⟨f, h₂⟩ = 0 →
          0 < (s.1).ord (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N)) ∧
        (R.residue₂ ⟨f, h₂⟩ ≠ 0 → R.residue₁ ⟨f, h₁⟩ = 0 →
          0 < (s.2).ord (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k N)))

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end


