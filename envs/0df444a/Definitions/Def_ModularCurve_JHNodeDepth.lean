-- Prove2me | Definitions.Def_ModularCurve_JHNodeDepth
-- name    : ModularCurve_JHNodeDepth
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/4558e260-6df1-5e23-9f61-66d37d99232c
-- title:
--   Node rings, depths and component-group laws for XH​(M)
-- statement:
--   The standing context is a prime $p$, a level $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field $\kappa$ has characteristic $p$ and is algebraically closed; $FM$ is the geometric function field of $X_H(M)$, $FMp$ that of the level $M/p$ curve for `infSubgroup p M H hpM`, and $Fb$ the characteristic-$p$ function field attached to the Néron object at $p$. Fix a place specialisation $P$ (with its map $\mathrm{sp}$ on places and on $\mathrm{Pic}^0$), a prolongation datum $R$ relative to an automorphism $\theta$ of $FM$, and integral $\overline{\mathbb{Q}}$-algebra maps $\alpha,\beta : FMp \to FM$, so that $\mathrm{reduceFst}\,V = \mathrm{sp}(V|_{\alpha})$ and $\mathrm{reduceSnd}\,V = \delta(\mathrm{sp}(V|_{\beta}))$.
--
--   For a place $w$ of $Fb/\kappa$, `nodeIntegers` is the subring of $FM$ of those $f$ lying in the integers of both charts $R_1$, $R_2$ and in the valuation ring of every place $V$ of $FM/\overline{\mathbb{Q}}$ with $\mathrm{reduceFst}\,V = w$; the accompanying lemmas record the defining membership criterion, that $\mathrm{ord}_V f \ge 0$ for such $V$, the two inclusions into the chart integers, the two induced residue maps `nodeResidue₁`, `nodeResidue₂` to $Fb$, and that constants from $A$ lie in the node ring. `ValueIntegralityLaw` is the predicate that for $f$ in the node ring at $w$ every value $V(f)$ lies in $A$. `AnnulusDepthLaw` asserts, for an annulus $An$ in $FM$ over $A$ and a function $\mathrm{depth}$ on places, that $v_A(V(\mathrm{param}\,An)) = v_A(p)^{\mathrm{depth}(V)}$ for every inertia-invariant $V$ above the first coordinate of the node $s$.
--
--   For a divisor $D$ on $FM$, `depthDiv` is the pushforward $\sum_V D(V)\,\mathrm{depth}(V)\,[\mathrm{reduceFst}\,V]$, and `depthDual` the functional $\sum_{s \in SS} \mathrm{depthDiv}(D)(s_1)\,\mathrm{crossingCoord}\,s$ on the character lattice of the finite set $SS$ of node pairs. `DepthCompLaw` is the predicate on a homomorphism $\mathrm{comp}$ from the inertia invariants of $JH$ to the component group $\mathrm{Dual}_{\mathbb{Z}}(\mathrm{characterLattice}\,SS)/\mathrm{range}(\mathrm{gramMap}\,e)$: whenever $D$ has degree zero, its class is inertia-invariant, and every place in its support is inertia-fixed and is either strict of the first or second kind or reduces (first reading) to some $s_1$ with $s \in SS$, then for each $s_0 \in SS$ the value $\mathrm{comp}[D]$ equals the class of $\mathrm{depthDual}(D) + \deg(\mathrm{sndDiv}\,D)\cdot e(s_0)\,\mathrm{crossingCoord}\,s_0$ — so in particular the right-hand class is asserted to be independent of $s_0$.
--
--   **Relation to Mathlib.** Mathlib provides only the ambient algebra used here (`Subring`, `Finsupp`, `Module.Dual` and quotients of modules); places and divisors of function fields, prolongation data, annuli, the character lattice with its width pairing and the resulting component group, and the specialisation maps are all the project's own notions.
--
--   **Where it is used.** These predicates package the depth bookkeeping for the special fibre of the Jacobian of $X_H(M)$ at $p \mid M$: the node rings and annulus depths express the local structure of the semistable model at a supersingular node, and `DepthCompLaw` describes the induced map from inertia-invariant divisor classes to the component group in terms of those depths. They are the hypotheses consumed when the component group of the Néron model is computed, as needed in the level-lowering step of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JHNodeDepth.lean

import Mathlib
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option quotPrecheck false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

namespace ModularCurve
namespace JHPlaceSpecialization

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
variable (A : ValuationSubring (AlgebraicClosure ℚ))
variable [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

local notation "κ" => ResidueField ↥A
local notation "FM" => ↥(xHFunctionFieldBar M H)
local notation "FMp" => ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))
local notation "Fb" => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)

variable {p M H hpM A}

namespace ProlongationDatum

variable {P : JHPlaceSpecialization p M H hpM A}
variable {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}

def nodeIntegers (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : Subring FM where
  carrier := {f | f ∈ R.R₁.integers ∧ f ∈ R.R₂.integers ∧
    ∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = w → f ∈ V.toValuationSubring}
  zero_mem' := ⟨zero_mem _, zero_mem _, fun V _ => zero_mem _⟩
  one_mem' := ⟨one_mem _, one_mem _, fun V _ => one_mem _⟩
  add_mem' := by
    rintro f g ⟨hf₁, hf₂, hf⟩ ⟨hg₁, hg₂, hg⟩
    exact ⟨add_mem hf₁ hg₁, add_mem hf₂ hg₂, fun V hV => add_mem (hf V hV) (hg V hV)⟩
  neg_mem' := by
    rintro f ⟨hf₁, hf₂, hf⟩
    exact ⟨neg_mem hf₁, neg_mem hf₂, fun V hV => neg_mem (hf V hV)⟩
  mul_mem' := by
    rintro f g ⟨hf₁, hf₂, hf⟩ ⟨hg₁, hg₂, hg⟩
    exact ⟨mul_mem hf₁ hg₁, mul_mem hf₂ hg₂, fun V hV => mul_mem (hf V hV) (hg V hV)⟩

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem mem_nodeIntegers_iff (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) (f : FM) :
    f ∈ R.nodeIntegers α hα w ↔ f ∈ R.R₁.integers ∧ f ∈ R.R₂.integers ∧
      ∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = w → f ∈ V.toValuationSubring :=
  Iff.rfl

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem mem_toValuationSubring_of_mem_nodeIntegers (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    {w : Place κ Fb} {f : FM} (hf : f ∈ R.nodeIntegers α hα w)
    {V : Place (AlgebraicClosure ℚ) FM} (hV : P.reduceFst α hα V = w) :
    f ∈ V.toValuationSubring :=
  hf.2.2 V hV

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in

theorem ord_nonneg_of_mem_nodeIntegers (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    {w : Place κ Fb} {f : FM} (hf : f ∈ R.nodeIntegers α hα w)
    {V : Place (AlgebraicClosure ℚ) FM} (hV : P.reduceFst α hα V = w) :
    0 ≤ V.ord f :=
  V.ord_nonneg_of_mem (hf.2.2 V hV)

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem nodeIntegers_le_integersFst (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : R.nodeIntegers α hα w ≤ R.R₁.integers.toSubring :=
  fun _ hf => hf.1

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem nodeIntegers_le_integersSnd (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : R.nodeIntegers α hα w ≤ R.R₂.integers.toSubring :=
  fun _ hf => hf.2.1

def nodeResidue₁ (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : ↥(R.nodeIntegers α hα w) →+* Fb :=
  R.R₁.residue.comp (Subring.inclusion (R.nodeIntegers_le_integersFst α hα w))

def nodeResidue₂ (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : ↥(R.nodeIntegers α hα w) →+* Fb :=
  R.R₂.residue.comp (Subring.inclusion (R.nodeIntegers_le_integersSnd α hα w))

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem nodeResidue₁_apply (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) (f : ↥(R.nodeIntegers α hα w)) :
    R.nodeResidue₁ α hα w f = R.R₁.residue ⟨f, f.2.1⟩ := rfl

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem nodeResidue₂_apply (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) (f : ↥(R.nodeIntegers α hα w)) :
    R.nodeResidue₂ α hα w f = R.R₂.residue ⟨f, f.2.2.1⟩ := rfl

omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem algebraMap_mem_nodeIntegers (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) (c : A) :
    algebraMap (AlgebraicClosure ℚ) FM (c : AlgebraicClosure ℚ) ∈ R.nodeIntegers α hα w :=
  ⟨(R.R₁.algebraMap_mem_iff (c : AlgebraicClosure ℚ)).mpr c.2, (R.R₂.algebraMap_mem_iff (c : AlgebraicClosure ℚ)).mpr c.2,
    fun V _ => V.algebraMap_mem' _⟩

def ValueIntegralityLaw (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : Prop :=
  ∀ f : FM, f ∈ R.nodeIntegers α hα w →
    ∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = w → V.evalAt f ∈ A

end ProlongationDatum

def AnnulusDepthLaw (P : JHPlaceSpecialization p M H hpM A) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (s : Place κ Fb × Place κ Fb) (An : AlgebraicCurve.Annulus A FM)
    (depth : Place (AlgebraicClosure ℚ) FM → ℕ) : Prop :=
  ∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = s.1 →
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) →
    A.valuation (V.evalAt An.param) = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ depth V

def depthDiv (P : JHPlaceSpecialization p M H hpM A) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (depth : Place (AlgebraicClosure ℚ) FM → ℕ) (D : Divisor (AlgebraicClosure ℚ) FM) : Divisor κ Fb :=
  D.sum fun V n => Finsupp.single (P.reduceFst α hα V) (n * (depth V : ℤ))

def depthDual (P : JHPlaceSpecialization p M H hpM A) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (SS : Finset (Place κ Fb × Place κ Fb))
    (depth : Place (AlgebraicClosure ℚ) FM → ℕ) (D : Divisor (AlgebraicClosure ℚ) FM) :
    Module.Dual ℤ (characterLattice ↥SS) :=
  ∑ s : ↥SS, P.depthDiv α hα depth D (s : Place κ Fb × Place κ Fb).1 • crossingCoord s

def DepthCompLaw (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (SS : Finset (Place κ Fb × Place κ Fb))
    (e : ↥SS → ℕ) (depth : Place (AlgebraicClosure ℚ) FM → ℕ)
    (comp : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ componentGroup e) : Prop :=
  ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := FM)))
    (hH : Pic0.mk D ∈ JHPlaceSpecialization.inertiaInvariants M H A),
    (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) FM).support,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ,
          arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) ∧
        (P.IsStrictFst α β hα hβ δ V ∨ P.IsStrictSnd α β hα hβ δ V ∨ ∃ s ∈ SS, P.reduceFst α hα V = s.1)) →
    ∀ s₀ : ↥SS,
      comp ⟨Pic0.mk D, hH⟩ =
        componentGroupProj e
          (P.depthDual α hα SS depth (D : Divisor (AlgebraicClosure ℚ) FM) +
            Divisor.degree (P.sndDiv α β hα hβ δ (D : Divisor (AlgebraicClosure ℚ) FM)) •
              ((e s₀ : ℤ) • crossingCoord s₀))

end JHPlaceSpecialization
end ModularCurve

end


