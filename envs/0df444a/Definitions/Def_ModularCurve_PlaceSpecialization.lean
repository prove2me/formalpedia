-- Prove2me | Definitions.Def_ModularCurve_PlaceSpecialization
-- name    : ModularCurve_PlaceSpecialization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/1e1a3723-d7b2-5c71-9735-af55824c8d55
-- title:
--   Place-specialisation data for modular function fields mod ℓ
-- statement:
--   For a valuation subring $A$ of $\overline{\mathbb{Q}}$, a prime $\ell$, a nonzero level $N$, a `ModularPolynomialData ℓ` together with the predicate `KroneckerCongruence ℓ data`, a field $k$ of characteristic $\ell$, a ring homomorphism $\mathrm{red} : A \to k$, and integrality hypotheses `hα`, `hβ` for the two degeneracy maps $\alpha$ (the inclusion $\overline{\mathbb{Q}}\cdot F^{\mathrm{full}}_N \hookrightarrow \overline{\mathbb{Q}}\cdot F^{\mathrm{full}}_{N\ell}$) and $\beta$ (substitution $q \mapsto q^{\ell}$ on Laurent expansions), this structure bundles the data of a reduction of the places and of the degree-zero divisor class group of the modular function field, together with the properties such a reduction is required to have. Its two data fields are a map `sp` from the places of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ to the places of `modularFunctionFieldC k N` $=k(\tilde j,\tilde j_N)$, and an additive map `spPic0` from `JZero N` to $\mathrm{Pic}^0$ of the characteristic-$\ell$ field. The remaining fields are axioms. Four clauses (`d0_j`, `d0_j_pole`, `d0_jN`, `d0_jN_pole`) say that `sp` respects the coordinates $j$ and $j_N$ at the level of orders: if $j-a$ has positive order at $w$ for some $a \in A$ then $\tilde j-\mathrm{red}\,a$ has positive order at $\mathrm{sp}\,w$, and if $j-a$ has non-positive order at $w$ for every $a \in A$ then $\tilde j$ has a pole at $\mathrm{sp}\,w$; likewise for $j_N$ and $\tilde j_N$. Clause `d1` asserts, for every place $W$ of the level-$N\ell$ field, that the images under `sp` of the $\alpha$- and $\beta$-restrictions of $W$ agree after one application of the Frobenius operator `frobOnPlacesGeomLevel k N data hKr`, in one direction or the other. Clause `d2` is a guarded unit-multiplicity clause: whenever $\varphi^2(\mathrm{sp}\,v)\neq \mathrm{sp}\,v$, there is exactly one place $W_0$ of the level-$N\ell$ field restricting to $v$ along $\beta$ with $\mathrm{sp}$ of its $\alpha$-restriction equal to $\varphi(\mathrm{sp}\,v)$, and that $W_0$ has $\beta$-ramification index $1$ (uniqueness being stated as: any such $W$ equals $W_0$). Clause `d4` asserts surjectivity of `sp`, and `d5` that the image under `Finsupp.mapDomain sp` of the divisor of a nonzero $f$ is the divisor of some nonzero $g$. The clauses `d6_inertia` and `d6_frobenius` concern the Galois action on places through `arithmeticGalois`: elements of the inertia subgroup of $A$ over $\mathbb{Q}$ act trivially after applying `sp`, while a Frobenius at $A$ over $\ell$ acts through `sp` as $\varphi$. The clauses `d7_dictInfty` and `d7_dictZero` transport residues of the Tate-type parameters $j_N/j^N$ and $j/j_N^N$: if such a quotient lies in the valuation ring of $w$, the relevant coordinate has no value in $A$ at $w$, and the residue equals the image of $\tau \in A$, then the corresponding quotient $\tilde j_N/\tilde j^N$ (resp. $\tilde j/\tilde j_N^N$) minus $\mathrm{red}\,\tau$ either vanishes identically or has positive order at $\mathrm{sp}\,w$. Finally `spPic0_compat` requires that for every degree-zero divisor $D$ upstairs there is a degree-zero divisor $D'$ downstairs whose underlying divisor is $\mathrm{mapDomain}\,\mathrm{sp}\,D$ and with `spPic0 (Pic0.mk D) = Pic0.mk D'`. The structure makes no existence assertion; it is the datum a construction of the reduction must supply.
--
--   **Relation to Mathlib.** Mathlib supplies the valuation-theoretic ingredients used here (`ValuationSubring`, decomposition and inertia subgroups, `IsLocalRing.residue`) and the `Finsupp` machinery for divisors, but has no places/divisors/$\mathrm{Pic}^0$ framework for function fields, no modular function fields and no specialisation packet; those are the project's own.
--
--   **Where it is used.** The packet is the interface through which the reduction of $X_0(N)$ and of $J_0(N)$ modulo $\ell$ enters the argument: its Frobenius and inertia clauses, together with the unit-multiplicity clause on the level-$N\ell$ fibre, are what yields the Eichler–Shimura congruence relation $T_\ell = F + \ell F'$ on the special fibre. That relation supplies the local conditions (unramified outside $Np$, quadratic relation for Frobenius) on the mod-$p$ Galois representations attached to Hecke eigensystems which are used in level lowering for the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_PlaceSpecialization.lean

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModularCurve

open AlgebraicCurve

set_option maxHeartbeats 800000 in

structure PlaceSpecialization
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ) where

  sp : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
    Place k (modularFunctionFieldC k N)

  spPic0 : JZero N →+ Pic0 k (modularFunctionFieldC k N)

  d0_j : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ a : A,
    0 < w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) →
    0 < (sp w).ord
        (⟨jqModC k, jqModC_mem k N⟩ - algebraMap k (modularFunctionFieldC k N) (red a))

  d0_j_pole : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    (sp w).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0

  d0_jN : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ a : A,
    0 < w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) →
    0 < (sp w).ord
        (⟨jqNModC k N, jqNModC_mem k N⟩
          - algebraMap k (modularFunctionFieldC k N) (red a))

  d0_jN_pole : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    (sp w).ord (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) < 0

  d1 : ∀ W : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))),
    sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα)
        = frobOnPlacesGeomLevel k N data hKr
            (sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ))
      ∨ frobOnPlacesGeomLevel k N data hKr
            (sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα))
        = sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ)

  d2 : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    frobOnPlacesGeomLevel k N data hKr
        (frobOnPlacesGeomLevel k N data hKr (sp v)) ≠ sp v →
    ∃ W₀ : Place (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))),
      W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ = v
        ∧ sp (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα)
            = frobOnPlacesGeomLevel k N data hKr (sp v)
        ∧ W₀.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) = 1
        ∧ ∀ W : Place (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))),
            W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ = v →
            sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα)
                = frobOnPlacesGeomLevel k N data hKr (sp v) →
              W = W₀

  d4 : Function.Surjective sp

  d5 : ∀ f : modularFunctionFieldBar N, f ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ v, D v = v.ord f) →
      ∃ g : modularFunctionFieldC k N, g ≠ 0 ∧
        ∀ v' : Place k (modularFunctionFieldC k N),
          Finsupp.mapDomain sp D v' = v'.ord g

  d6_inertia : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    σ ∈ A.inertiaSubgroupIn ℚ →
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      sp (arithmeticGalois (modularFunctionFieldFull N) σ • w) = sp w

  d6_frobenius : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    A.IsFrobeniusAt σ ℓ →
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      sp (arithmeticGalois (modularFunctionFieldFull N) σ • w)
        = frobOnPlacesGeomLevel k N data hKr (sp w)

  d7_dictInfty : ∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (τ : A)
      (ht : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
          / (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ^ N ∈ w.toValuationSubring),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
        = algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ) →
      ⟨jqNModC k N, jqNModC_mem k N⟩ / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < (sp w).ord
        (⟨jqNModC k N, jqNModC_mem k N⟩ / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ))

  d7_dictZero : ∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (τ : A)
      (ht : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          / (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N) ^ N ∈ w.toValuationSubring),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
        = algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ) →
      ⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < (sp w).ord
        (⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ))

  spPic0_compat :
    ∀ D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)),
      ∃ D' : Divisor.degZero (K := k) (F := ↥(modularFunctionFieldC k N)),
        (D' : Divisor k (modularFunctionFieldC k N))
            = Finsupp.mapDomain sp
                (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
          ∧ spPic0 (Pic0.mk D) = Pic0.mk D'

end ModularCurve


