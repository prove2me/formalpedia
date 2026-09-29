-- Prove2me | Definitions.Def_ModularCurve_ModularEquationQ
-- name    : ModularCurve_ModularEquationQ
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/f6f8c159-e5b9-5f20-a6ed-31fa9b2ba909
-- title:
--   The j-line, the modular equation over it, and its root field
-- statement:
--   Fix a field $K$ and $M \ge 1$, and work inside the Laurent series field $\mathrm{LaurentSeries}\,K = K((Q))$, where $Q$ is to be thought of as $q^{1/M}$. The element `jqNModC K M` is `qExpand K M (jqModC K)`, that is the integral $q$-expansion $j = Q^{-1}\prod\text{-type series}$ of the modular invariant, with coefficients read in $K$ and with $Q$ replaced by $Q^{M}$; so it represents $j(q)$. The intermediate field `jqNField K M` is $K\big(j(Q^{M})\big) \subseteq K((Q))$, the $j$-line, obtained as `IntermediateField.adjoin` of the singleton $\{$`jqNModC K M`$\}$, and `jqNGen K M` is that generator viewed as an element of this subfield (its image in $K((Q))$ being `jqNModC K M` on the nose).
--
--   Given a term `data : ModularPolynomialData M` — a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree `dedekindPsi M` $=\psi(M)$ in $Y$ together with, as a field of the structure, the vanishing identity $\Phi(j(Q), j(Q^{M})) = 0$ in $\mathbb{Q}((Q))$ — the polynomial `data.toJqNField K` is the one-variable polynomial over the $j$-line obtained from $\Phi$ by reducing its integer coefficients into `jqNField K M` and specialising the inner variable $X$ to the generator: $P_K(Y) = \Phi\big(j(Q^{M}), Y\big)$. It is monic, and pushing it forward along $K(j(Q^M)) \hookrightarrow K((Q))$ gives $\Phi$ with inner variable at `qExpand K M (jqModC K)`.
--
--   Finally `data.rootField K` is the intermediate field of $K((Q))$ generated over $K$ by `jqNModC K M` together with the whole root set of $P_K$ in $K((Q))$; two monotonicity lemmas record that it contains the $j$-line and contains those roots.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used (`LaurentSeries`, `IntermediateField.adjoin`, `Polynomial.rootSet`, `Polynomial.Monic`); the modular invariant's $q$-expansion, the variable rescaling `qExpand`, the structure `ModularPolynomialData` packaging a modular polynomial with its defining identity, and the fields constructed here are the project's own.
--
--   **Where it is used.** These definitions fix a concrete model, inside a Laurent series field, of the $j$-line and of the splitting data of the modular equation of level $M$ over it; statements built on them concern the roots of the modular equation, its irreducibility over the $j$-line, and the resulting Galois action, which is the function-field input to the theory of modular curves used on the modularity side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ModularEquationQ.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section JLine

variable (K : Type*) [Field K] (M : ℕ) [NeZero M]

def jqNField : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K {jqNModC K M}

theorem jqNModC_mem_jqNField : jqNModC K M ∈ jqNField K M :=
  IntermediateField.subset_adjoin K _ (Set.mem_singleton _)

def jqNGen : jqNField K M :=
  ⟨jqNModC K M, jqNModC_mem_jqNField K M⟩

@[simp]
theorem coe_jqNGen : (jqNGen K M : LaurentSeries K) = jqNModC K M := rfl

end JLine

namespace ModularPolynomialData

variable {M : ℕ} [NeZero M] (data : ModularPolynomialData M) (K : Type*) [Field K]

def toJqNField : Polynomial (jqNField K M) :=
  data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (jqNField K M)) (jqNGen K M))

theorem toJqNField_monic : (data.toJqNField K).Monic :=
  data.monic.map _

theorem toJqNField_map :
    (data.toJqNField K).map (algebraMap (jqNField K M) (LaurentSeries K)) =
      data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K M (jqModC K))) := by
  rw [toJqNField, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X, Polynomial.eval₂_X]
  rfl

def rootField : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K (insert (jqNModC K M) ((data.toJqNField K).rootSet (LaurentSeries K)))

theorem jqNField_le_rootField : jqNField K M ≤ data.rootField K :=
  IntermediateField.adjoin.mono K _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem rootSet_subset_rootField :
    (data.toJqNField K).rootSet (LaurentSeries K) ⊆ (data.rootField K : Set (LaurentSeries K)) :=
  (Set.subset_insert _ _).trans (IntermediateField.subset_adjoin K _)

end ModularPolynomialData

end ModularCurve

end


