-- Prove2me | Definitions.Def_LocalConjugacy_Cohomology
-- name    : LocalConjugacy_Cohomology
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T03:25:20.422131+00:00
-- url     : https://prove2.me/theorems/f8a3cec1-462b-46fd-b7b7-665856020d66
-- title:
--   Continuous nonabelian first cohomology and restriction
-- statement:
--   Continuous nonabelian cocycles and the actual quotient $H^1$ by global coboundaries, with distinguished identity class. Defines stable classes using intersections with conjugate subgroups, ordinary and stable restriction, and simultaneous restriction to Sylow subgroups indexed by the prime divisors of the profinite group. All structural proofs needed to define these maps are included.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1, https://arxiv.org/pdf/2609.37678v1, §§1–4, pp. 1–8. Adapted in part from the author’s local Apache-2.0 Lean development.

import Definitions.Def_LocalConjugacy_Groups

/-!
# Continuous nonabelian first cohomology

Mathlib's group-cohomology modules at this revision treat abelian/module
coefficients. Here coefficients may be nonabelian. We therefore construct the
actual quotient of continuous cocycles by a global coboundary relation, using
Mathlib's `Quotient`, `Continuous`, `MulDistribMulAction`, and semidirect product.
The left-action convention is `j • n = n^(j⁻¹)` in the paper's notation.
Stability on a nonnormal subgroup compares restrictions to its intersection
with each conjugate; it never presupposes a conjugation action on that subgroup.
Only elementary structural proofs needed to define the quotient maps occur here.
-/

namespace LocalConjugacy

/-- Continuous nonabelian 1-cocycles on a closed subgroup of `J`. -/
structure Cocycle {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
    [TopologicalSpace N] [MulDistribMulAction J N] (K : Subgroup J) where
  toFun : K → N
  continuous_toFun : Continuous toFun
  map_mul : ∀ x y : K, toFun (x * y) = toFun x * ((x : J) • toFun y)

/-- The usual equivalence of nonabelian cocycles, with one global conjugator. -/
def Cohomologous {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
    [TopologicalSpace N] [MulDistribMulAction J N] {K : Subgroup J}
    (f g : Cocycle (N := N) K) : Prop :=
  ∃ n : N, ∀ x : K, g.toFun x = n⁻¹ * f.toFun x * ((x : J) • n)

/-- Stable elements: equality up to a single coboundary on each intersection
`K ∩ j K j⁻¹`. This also makes sense for nonnormal `K`. -/
def InvariantUnder {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
    [TopologicalSpace N] [MulDistribMulAction J N]
    (L K : Subgroup J) (f : Cocycle (N := N) K) : Prop :=
  ∀ j ∈ L, ∃ n : N, ∀ (x : J) (hx : x ∈ K) (hjx : j⁻¹ * x * j ∈ K),
    j • f.toFun ⟨j⁻¹ * x * j, hjx⟩ = n⁻¹ * f.toFun ⟨x, hx⟩ * (x • n)

/-- The product topology on the semidirect product. -/
instance semidirectTopology {J N : Type*} [Group J] [Group N]
    [TopologicalSpace J] [TopologicalSpace N] (a : J →* MulAut N) :
    TopologicalSpace (N ⋊[a] J) :=
  TopologicalSpace.induced (fun x => (x.left, x.right)) inferInstance

/-- The semidirect product attached to the left action on the coefficient group. -/
abbrev ActionProduct (J N : Type*) [Group J] [Group N] [MulDistribMulAction J N] :=
  N ⋊[MulDistribMulAction.toMulAut J N] J

/-- Restriction of a continuous cocycle along subgroup inclusion. -/
def restrictCocycle {J N : Type*} [Group J] [Group N]
    [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]
    {K L : Subgroup J} (hKL : K ≤ L)
    (f : Cocycle (N := N) L) : Cocycle (N := N) K where
  toFun := fun x => f.toFun ⟨x, hKL x.property⟩
  continuous_toFun := f.continuous_toFun.comp
    (continuous_subtype_val.subtype_mk fun x => hKL x.property)
  map_mul := fun x y => f.map_mul ⟨x, hKL x.property⟩ ⟨y, hKL y.property⟩

/-- Prime divisors of the supernatural order of a profinite group: those
occurring in at least one continuous finite quotient. -/
def PrimeDivisor (J : Type*) [Group J] [TopologicalSpace J] :=
  {p : Nat.Primes // ∃ U : OpenNormalSubgroup J, p.val ∣ Nat.card (J ⧸ U.toSubgroup)}


variable {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
  [TopologicalSpace N] [MulDistribMulAction J N] {K : Subgroup J}

/-- The identity coefficient witnesses reflexivity of the coboundary relation. -/
theorem cohomologous_refl (f : Cocycle (N := N) K) : Cohomologous f f := by
  exact ⟨1, by simp⟩

/-- Invert the single coefficient that witnesses cohomology; no pointwise choices occur. -/
theorem cohomologous_symm {f g : Cocycle (N := N) K}
    (h : Cohomologous f g) : Cohomologous g f := by
  -- Retain the same coefficient throughout the whole domain.
  obtain ⟨n, hn⟩ := h
  refine ⟨n⁻¹, fun x => ?_⟩
  rw [hn x]
  simp [mul_assoc, smul_inv']

/-- Multiply the two global coboundary witnesses to obtain transitivity. -/
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

/-- The class of the constant identity cocycle is the distinguished point. -/
instance (K : Subgroup J) : Inhabited (H1 (N := N) K) :=
  ⟨Quotient.mk _ (trivialCocycle K)⟩

/-- A global coboundary witness still works after restricting the domain. -/
theorem restrict_cohomologous {K L : Subgroup J} (hKL : K ≤ L)
    {f g : Cocycle (N := N) L} (h : Cohomologous f g) :
    Cohomologous (restrictCocycle hKL f) (restrictCocycle hKL g) := by
  -- Retain the same coefficient throughout the whole domain.
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

/-- The identity cocycle is stable under every conjugation. -/
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

/-- Restriction preserves the distinguished class, as required for pointed sets. -/
theorem restrictH1_distinguished {K L : Subgroup J} (hKL : K ≤ L) :
    restrictH1 (N := N) hKL default = default := rfl

/-- The stable restriction map sends the identity class to the identity class. -/
theorem stableRestriction_distinguished (K : Subgroup J) :
    stableRestriction (N := N) K default = default := Subtype.ext rfl

/-- All components of simultaneous restriction preserve the identity class. -/
theorem primaryRestriction_distinguished (P : PrimeDivisor J → Subgroup J) :
    primaryRestriction (N := N) P default = default :=
  funext (fun p => stableRestriction_distinguished (P p))

/-- The cocycle equation at the identity forces the identity value. -/
theorem cocycle_one (f : Cocycle (N := N) K) : f.toFun 1 = 1 := by
  have h := f.map_mul 1 1
  simpa using h



end LocalConjugacy


