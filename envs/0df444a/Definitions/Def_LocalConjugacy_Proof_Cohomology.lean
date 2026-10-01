-- Prove2me | Definitions.Def_LocalConjugacy_Proof_Cohomology
-- name    : LocalConjugacy_Proof_Cohomology
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T14:30:30.679332+00:00
-- url     : https://prove2.me/theorems/f448d2f6-7ff9-44b6-915f-42fa117e8147
-- title:
--   Auxiliary continuous cohomology quotient maps
-- statement:
--   The pointed quotient of continuous cocycles by global coboundaries, restriction maps, and the subtype of stable classes. The cocycle type is shared with the canonical mission interface.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
  [TopologicalSpace N] [MulDistribMulAction J N] {K : Subgroup J}

theorem cohomologous_refl (f : Cocycle (N := N) K) : Cohomologous f f := by
  exact ⟨1, by simp⟩

theorem cohomologous_symm {f g : Cocycle (N := N) K}
    (h : Cohomologous f g) : Cohomologous g f := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n⁻¹, fun x => ?_⟩
  rw [hn x]
  simp [mul_assoc, smul_inv']

theorem cohomologous_trans {f g h : Cocycle (N := N) K}
    (hfg : Cohomologous f g) (hgh : Cohomologous g h) : Cohomologous f h := by
  obtain ⟨n, hn⟩ := hfg
  obtain ⟨m, hm⟩ := hgh
  refine ⟨n * m, fun x => ?_⟩
  rw [hm x, hn x]
  simp [mul_assoc, smul_mul']

/-- The setoid defining continuous nonabelian first cohomology. -/
def cohomologySetoid (K : Subgroup J) : Setoid (Cocycle (N := N) K) where
  r := Cohomologous
  iseqv := ⟨cohomologous_refl, cohomologous_symm, cohomologous_trans⟩

/-- The actual quotient of continuous cocycles by coboundaries. -/
def H1 (K : Subgroup J) := Quotient (cohomologySetoid (N := N) K)

/-- Distinguished cocycle, whose class points `H1`. -/
def trivialCocycle (K : Subgroup J) : Cocycle (N := N) K where
  toFun := fun _ => 1
  continuous_toFun := continuous_const
  map_mul := by simp

instance (K : Subgroup J) : Inhabited (H1 (N := N) K) :=
  ⟨Quotient.mk _ (trivialCocycle K)⟩

theorem restrict_cohomologous {K L : Subgroup J} (hKL : K ≤ L)
    {f g : Cocycle (N := N) L} (h : Cohomologous f g) :
    Cohomologous (restrictCocycle hKL f) (restrictCocycle hKL g) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun x => hn ⟨x, hKL x.property⟩⟩

/-- The restriction map on cohomology, with no choices of representatives. -/
def restrictH1 {K L : Subgroup J} (hKL : K ≤ L) : H1 (N := N) L → H1 (N := N) K :=
  Quotient.map (restrictCocycle hKL) (fun _ _ => restrict_cohomologous hKL)

/-- A restricted global cocycle is stable on every intersection with a
conjugate subgroup; normality of that subgroup is unnecessary. -/
theorem invariant_restriction (K : Subgroup J)
    (f : Cocycle (N := N) (⊤ : Subgroup J)) :
    InvariantUnder ⊤ K (restrictCocycle le_top f) := by
  intro j _
  refine ⟨f.toFun ⟨j, trivial⟩, fun x hx hjx => ?_⟩
  let t : (⊤ : Subgroup J) := ⟨j⁻¹ * x * j, trivial⟩
  have hh : (⟨j, trivial⟩ : (⊤ : Subgroup J)) * t =
      ⟨x, trivial⟩ * ⟨j, trivial⟩ := by apply Subtype.ext; dsimp [t]; group
  have h := congrArg f.toFun hh
  rw [f.map_mul, f.map_mul] at h
  change j • f.toFun t = (f.toFun ⟨j, trivial⟩)⁻¹ *
    f.toFun ⟨x, trivial⟩ * (x • f.toFun ⟨j, trivial⟩)
  have h' := congrArg (fun n => (f.toFun ⟨j, trivial⟩)⁻¹ * n) h
  simpa only [Subgroup.coe_mk, inv_mul_cancel_left, mul_assoc] using h'

/-- The manuscript's `inv_L H¹(K,N)`: cohomology classes represented by
`L`-stable cocycles, using intersections when `K` is not normal. -/
def InvariantH1 (L K : Subgroup J) :=
  {a : H1 (N := N) K // ∃ f : Cocycle (N := N) K,
    Quotient.mk (cohomologySetoid K) f = a ∧ InvariantUnder L K f}

theorem trivialCocycle_invariant (L K : Subgroup J) :
    InvariantUnder L K (trivialCocycle (N := N) K) := by
  intro j _
  exact ⟨1, by intros; simp [trivialCocycle]⟩

/-- Stable cohomology classes have the same distinguished identity class. -/
instance invariantH1Inhabited (L K : Subgroup J) : Inhabited (InvariantH1 (N := N) L K) :=
  ⟨⟨default, trivialCocycle K, rfl, trivialCocycle_invariant L K⟩⟩

/-- Restriction `H¹(J,N) → inv_J H¹(K,N)`, with the actual quotient classes.
Here the ambient group `J` is represented by its top subgroup. -/
def stableRestriction (K : Subgroup J) : H1 (N := N) (⊤ : Subgroup J) →
    InvariantH1 (N := N) ⊤ K := fun a =>
  ⟨restrictH1 le_top a, Quotient.inductionOn a (fun f =>
    ⟨restrictCocycle le_top f, rfl, invariant_restriction K f⟩)⟩

/-- The map in Lemma 1.2: simultaneous restriction to chosen Sylow subgroups,
indexed by the prime divisors of the supernatural order of `J`. -/
def primaryRestriction (P : PrimeDivisor J → Subgroup J) :
    H1 (N := N) (⊤ : Subgroup J) →
      ((p : PrimeDivisor J) → InvariantH1 (N := N) ⊤ (P p)) :=
  fun a p => stableRestriction (P p) a







theorem cocycle_one (f : Cocycle (N := N) K) : f.toFun 1 = 1 := by
  have h := f.map_mul 1 1
  simpa using h

end LocalConjugacy

end LocalConjugacy.Proof

end


