-- Prove2me | Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
-- name    : ModularCurve_FullLevelSemistableCoveringGuards
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/ac8b2af7-383a-502e-8aed-b40b16249cac
-- title:
--   Guard clauses for full-level semistable coverings
-- statement:
--   Fix a prime $q$, an integer $M' \ge 1$, a valuation subring $A \subseteq \overline{\mathbb{Q}}$ with residue field $\kappa =$ `ResidueField A`, and a finite set $SS$ of places of `modularFunctionFieldC κ M'` over $\kappa$. For a `SemistableCovering q M' A SS` $\mathcal{C}$ — a family of component charts $C^{\mathrm{Ig}}_\ell = \mathcal{C}.\mathtt{CIg}\ \ell$ indexed by $\ell \in \mathbb{P}^1(\mathbb{F}_q)$ with reduced fields $\mathcal{C}.\mathtt{FIg}\ \ell$, charts $C^{\mathrm{SS}}_s = \mathcal{C}.\mathtt{CSS}\ s$ with reduced fields $\mathcal{C}.\mathtt{FSS}\ s$ for $s \in SS$, and annuli joining them — three predicates are defined.
--
--   `GenusClause` is the numerical identity
--   $$g(\mathtt{fieldBar}\ q\ M') + \bigl(\#\mathbb{P}^1(\mathbb{F}_q) + \#SS\bigr) = \sum_{\ell}^{\mathrm{f}} g(\mathcal{C}.\mathtt{FIg}\ \ell) + \sum_{s \in SS} g(\mathcal{C}.\mathtt{FSS}\ s) + \#\mathbb{P}^1(\mathbb{F}_q)\cdot\#SS + 1,$$
--   the genus of `fieldBar q M'` being taken over $\overline{\mathbb{Q}}$ and those of the reduced fields over $\kappa$, each $g = \mathtt{genusFF}$ defined as the dimension over the base field of the repartition quotient $\mathbb{A}/(\mathbb{A}(0) + F)$; the first sum is a finite-support sum over the index type.
--
--   `HasDiscFibres C`, for a component chart $C$ of `fieldBar q M'` with reduced field $\bar{F}$, asserts that for every place $Q$ of $\bar{F}$ over $\kappa$ not among $C.\mathtt{nodes}$ there is a $C$-integral function $T$ whose residue is non-zero with $\mathrm{ord}_Q = 1$, such that every place $P \in C.\mathtt{dom}$ reducing to $Q$ has $T$ in its valuation subring with value $P(T) \in \mathfrak{m}_A$, and such that each $c \in \mathfrak{m}_A$ is $P(T)$ for exactly one place $P \in C.\mathtt{dom}$ reducing to $Q$: the fibre over $Q$ is the open unit disc parametrised by $T$. `DiscFibreClause` imposes this on all Igusa and all supersingular charts.
--
--   `CurveClause` asserts that each reduced field is `IsCurveOver κ` — principal divisors of degree zero exist, all place residue fields are finite over $\kappa$, and the module of Kähler differentials is free of rank one — and is essentially of finite type over $\kappa$.
--
--   **Relation to Mathlib.** Component charts, annuli, semistable coverings, the repartition genus `genusFF` and `IsCurveOver` are the project's own function-field notions; Mathlib contributes the ambient valuation-theoretic and Kähler-differential machinery, and `Algebra.EssFiniteType` is Mathlib's.
--
--   **Where it is used.** These clauses are the non-degeneracy conditions attached to a semistable covering of the full-level modular function field at $q$: they pin down that the charts are the genuine components of the special fibre (genus count over the complete bipartite dual graph), that the reduction of places off the nodes has open-disc fibres, and that the reduced fields are function fields of curves over the residue field. They are exported by the existence theorem for such coverings and assumed by its consumers in the analysis of the semistable special fibre used for level lowering at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_FullLevelSemistableCoveringGuards.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel

open AlgebraicCurve IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {SS : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}

namespace SemistableCovering

def GenusClause (𝒞 : SemistableCovering q M' A SS) : Prop :=
  AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(fieldBar q M') + (Nat.card (CuspidalType.ProjLine q) + SS.card) =
    ∑ᶠ ℓ : CuspidalType.ProjLine q, AlgebraicCurve.genusFF (ResidueField A) (𝒞.FIg ℓ) +
      ∑ s ∈ SS.attach, AlgebraicCurve.genusFF (ResidueField A) (𝒞.FSS s) +
        Nat.card (CuspidalType.ProjLine q) * SS.card + 1

def HasDiscFibres {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A (fieldBar q M') Fbar) : Prop :=
  ∀ Q : Place (IsLocalRing.ResidueField A) Fbar, Q ∉ C.nodes →
    ∃ (T : ↥(fieldBar q M')) (hT : T ∈ C.integers), C.residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord (C.residue ⟨T, hT⟩) = 1 ∧
      (∀ P ∈ C.dom, C.placeMap P = Q → T ∈ P.toValuationSubring ∧
        ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
      ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
        ∃! P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ C.dom ∧ C.placeMap P = Q ∧ P.evalAt T = c

def DiscFibreClause (𝒞 : SemistableCovering q M' A SS) : Prop :=
  (∀ ℓ, HasDiscFibres (𝒞.CIg ℓ)) ∧ ∀ s, HasDiscFibres (𝒞.CSS s)

def CurveClause (𝒞 : SemistableCovering q M' A SS) : Prop :=
  (∀ ℓ, IsCurveOver (ResidueField A) (𝒞.FIg ℓ) ∧ Algebra.EssFiniteType (ResidueField A) (𝒞.FIg ℓ)) ∧
    ∀ s, IsCurveOver (ResidueField A) (𝒞.FSS s) ∧ Algebra.EssFiniteType (ResidueField A) (𝒞.FSS s)

end SemistableCovering

end ModularCurve.FullLevel

end


