-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
-- name    : OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:41:19.699659+00:00
-- url     : https://prove2.me/theorems/d1fcccc7-6911-4180-9a98-6b069b47bc78
-- title:
--   Inflation of irreducible characters
-- statement:
--   For a surjective homomorphism $f:H\to G$, precomposition of class functions carries irreducible characters of $G$ to irreducible characters of $H$ and preserves degrees. For the quotient map $G\to G/N$ this is the classical inflation correspondence (Isaacs (2.22)): an irreducible character $\bar\chi$ of $G/N$ inflates to an irreducible character of $G$ whose kernel contains $N$.
--
--   Main definitions: `ofCompSurjective` and `comapComp` (push forward and pull back of subrepresentations along $f$), `compHomEquiv` (the lattice of subrepresentations of $\sigma\circ f$ versus $\sigma$), `inflate` (the inflation map), `sumInflatedDegreeSq` (Peterfalvi (6.6) degree-sum identity) and `sumInflatedDegreeSq_ntrivial` (the nontrivial version).
--
--   The bundle also proves 19 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/InflationCharacter.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/InflationCharacter.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IrrIndexing
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S03_PreliminaryCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SchurCenterBound
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LinearCharacter
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OddOrder.RepresentationTheory

namespace Subrepresentation

variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  {f : H →* G}

/-- Push a subrepresentation of `σ.comp f` forward to a subrepresentation of `σ`, when `f` is
surjective.  The underlying submodule is unchanged; invariance under every `σ g` follows from
invariance under every `σ (f h)` because `f` is onto. -/
def ofCompSurjective (σ : Representation ℂ G V) (hf : Function.Surjective f)
    (R : Subrepresentation (σ.comp f)) : Subrepresentation σ where
  toSubmodule := R.toSubmodule
  apply_mem_toSubmodule g v hv := by
    obtain ⟨h, rfl⟩ := hf g
    exact R.apply_mem_toSubmodule h hv

/-- Pull a subrepresentation of `σ` back to a subrepresentation of `σ.comp f`.  The underlying
submodule is unchanged; invariance under `σ (f h)` is a special case of invariance under all
`σ g`. -/
def comapComp (σ : Representation ℂ G V) (R : Subrepresentation σ) :
    Subrepresentation (σ.comp f) where
  toSubmodule := R.toSubmodule
  apply_mem_toSubmodule h _v hv := R.apply_mem_toSubmodule (f h) hv

/-- For a surjective `f : H →* G`, the lattice of subrepresentations of `σ.comp f` is order
isomorphic to that of `σ`, identically on the underlying submodule. -/
def compHomEquiv (σ : Representation ℂ G V) (hf : Function.Surjective f) :
    Subrepresentation (σ.comp f) ≃o Subrepresentation σ where
  toFun := ofCompSurjective σ hf
  invFun := comapComp σ
  left_inv R := by cases R; rfl
  right_inv R := by cases R; rfl
  map_rel_iff' := Iff.rfl

end Subrepresentation

namespace Representation

variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  {f : H →* G}

/-- **Irreducibility is preserved under surjective precomposition.** If `f : H →* G` is
surjective and `σ` is an irreducible representation of `G`, then `σ.comp f` is an irreducible
representation of `H`.

The proof transports `IsSimpleOrder (Subrepresentation σ)` (the definition of irreducibility)
along the order isomorphism `Subrepresentation.compHomEquiv`. -/
theorem isIrreducible_comp_of_surjective (σ : Representation ℂ G V)
    (hf : Function.Surjective f) (hσ : Representation.IsIrreducible σ) :
    Representation.IsIrreducible (σ.comp f) := by
  have : IsSimpleOrder (Subrepresentation σ) := hσ
  exact (Subrepresentation.compHomEquiv σ hf).isSimpleOrder

/-- **Irreducibility descends along a surjective precomposition.** If `f : H →* G` is surjective
and `σ.comp f` is an irreducible representation of `H`, then `σ` is an irreducible representation of
`G`.  This is the converse of `isIrreducible_comp_of_surjective`, transporting
`IsSimpleOrder (Subrepresentation (σ.comp f))` backwards along the order isomorphism
`Subrepresentation.compHomEquiv`.  It is the step that makes the *descended* representation
(`Representation.ofQuotient`) irreducible in the inflation-surjectivity argument. -/
theorem isIrreducible_of_isIrreducible_comp_of_surjective (σ : Representation ℂ G V)
    (hf : Function.Surjective f) (hσ : Representation.IsIrreducible (σ.comp f)) :
    Representation.IsIrreducible σ := by
  have : IsSimpleOrder (Subrepresentation (σ.comp f)) := hσ
  exact (Subrepresentation.compHomEquiv σ hf).symm.isSimpleOrder

end Representation

variable {G H : Type*} [Group G] [Group H]

/-- **Precomposition by a surjective homomorphism is injective on class functions.**
If `f : H →* G` is surjective then `ClassFunction.compHom f` is injective: two class functions
on `G` that agree after pulling back along `f` agree everywhere, because every `g : G` is `f h`
for some `h`.

This is the injectivity half of the inflation correspondence ([Isaacs] (2.22)): distinct
characters of the quotient inflate to distinct characters of `G`. -/
theorem ClassFunction.compHom_injective_of_surjective {f : H →* G}
    (hf : Function.Surjective f) :
    Function.Injective (ClassFunction.compHom f : ClassFunction G ℂ → ClassFunction H ℂ) := by
  intro φ ψ hφψ
  ext g
  obtain ⟨h, rfl⟩ := hf g
  exact congrFun (congrArg (fun (χ : ClassFunction H ℂ) => (χ : H → ℂ)) hφψ) h

/-- **Inflation along a surjective homomorphism preserves irreducible characters.**
If `f : H →* G` is surjective and `φ` is an irreducible character of `G`, then its pullback
`ClassFunction.compHom f φ` is an irreducible character of `H`.

This is the homomorphism-general form of [Isaacs] (2.22): the witnessing irreducible
representation `σ` of `G` (with `φ = χ_σ`) precomposes to `σ.comp f`, which is irreducible by
`Representation.isIrreducible_comp_of_surjective` and whose character is `χ_σ ∘ f`, i.e. exactly
`compHom f φ`. -/
theorem IsIrreducibleCharacter.compHom_of_surjective {f : H →* G}
    (hf : Function.Surjective f) {φ : ClassFunction G ℂ}
    (hφ : IsIrreducibleCharacter φ) :
    IsIrreducibleCharacter (ClassFunction.compHom f φ) := by
  obtain ⟨V, _, _, _, σ, hσ, hχ⟩ := hφ
  refine ⟨V, inferInstance, inferInstance, inferInstance, σ.comp f,
    Representation.isIrreducible_comp_of_surjective σ hf hσ, ?_⟩
  funext h
  change φ (f h) = Representation.character (σ.comp f) h
  rw [show Representation.character (σ.comp f) h = σ.character (f h) from rfl,
    show (φ : G → ℂ) (f h) = σ.character (f h) from congrFun hχ (f h)]

section Inflation

variable (N : Subgroup G) [N.Normal]

/-- **Inflation map** ([Isaacs] (2.22)).  An irreducible character of `G ⧸ N` inflates to the
irreducible character of `G` obtained by precomposing with the quotient map `QuotientGroup.mk' N`.

`QuotientGroup.mk' N` is surjective, so `IsIrreducibleCharacter.compHom_of_surjective` provides
the irreducibility of the inflated character. -/
def inflate (χbar : IrreducibleCharacter (G ⧸ N)) : IrreducibleCharacter G :=
  ⟨ClassFunction.compHom (QuotientGroup.mk' N) (χbar : ClassFunction (G ⧸ N) ℂ),
    IsIrreducibleCharacter.compHom_of_surjective (QuotientGroup.mk'_surjective N)
      χbar.isIrreducible⟩

@[simp] theorem inflate_coe (χbar : IrreducibleCharacter (G ⧸ N)) :
    ((inflate N χbar : IrreducibleCharacter G) : ClassFunction G ℂ) =
      ClassFunction.compHom (QuotientGroup.mk' N) (χbar : ClassFunction (G ⧸ N) ℂ) :=
  rfl

@[simp] theorem inflate_apply (χbar : IrreducibleCharacter (G ⧸ N)) (g : G) :
    ((inflate N χbar : IrreducibleCharacter G) : ClassFunction G ℂ) g =
      (χbar : ClassFunction (G ⧸ N) ℂ) (QuotientGroup.mk' N g) :=
  rfl

/-- **Inflation preserves degree.** The inflated character evaluated at `1` equals the original
character of `G ⧸ N` evaluated at `1`: the quotient map sends `1` to `1`. -/
@[simp] theorem inflate_apply_one (χbar : IrreducibleCharacter (G ⧸ N)) :
    ((inflate N χbar : IrreducibleCharacter G) : ClassFunction G ℂ) 1 =
      (χbar : ClassFunction (G ⧸ N) ℂ) 1 := by
  rw [inflate_apply, map_one]

/-- **Inflation is injective** ([Isaacs] (2.22)).  Distinct irreducible characters of `G ⧸ N`
inflate to distinct irreducible characters of `G`.  The quotient map `QuotientGroup.mk' N` is
surjective, so precomposition by it is injective on class functions
(`ClassFunction.compHom_injective_of_surjective`), and `inflate` is that precomposition packaged
on irreducible characters.

Together with `inflate_apply_one` (degree preservation) and `subset_characterKernel_inflate`
(image lands in `{χ ∈ Irr G | N ⊆ ker χ}`), this realizes the inflation map as a
degree-preserving injection `Irr(G ⧸ N) ↪ {χ ∈ Irr G | N ⊆ ker χ}`.  Surjectivity of this
injection (every irreducible character of `G` with `N ⊆ ker` arises by inflation) is the
remaining half of the bijection. -/
theorem inflate_injective : Function.Injective (inflate N) := by
  intro χbar ψbar h
  apply Subtype.ext
  exact ClassFunction.compHom_injective_of_surjective (QuotientGroup.mk'_surjective N)
    (congrArg (Subtype.val) h)

/-- **Inflation sends the trivial character to the trivial character.**  Both sides are the
constant class function `1`: `(inflate N 1_{G⧸N}) g = 1_{G⧸N} (mk g) = 1 = 1_G g`. -/
@[simp] theorem inflate_trivial :
    inflate N (trivialIrreducibleCharacter (G ⧸ N)) = trivialIrreducibleCharacter G := by
  apply Subtype.ext
  ext g
  simp

/-- **An inflated character is trivial iff the source character was trivial.**  The inflation
analogue of `linearIrreducibleCharacter_eq_trivial_iff`: combine `inflate_trivial` with the
injectivity of inflation (`inflate_injective`). -/
@[simp] theorem inflate_eq_trivial_iff {χbar : IrreducibleCharacter (G ⧸ N)} :
    inflate N χbar = trivialIrreducibleCharacter G ↔
      χbar = trivialIrreducibleCharacter (G ⧸ N) := by
  rw [← inflate_trivial N]
  exact (inflate_injective N).eq_iff

/-- **The kernel of an inflated character contains `N`** ([Isaacs] (2.22)).  Every `n ∈ N` maps
to `1` in `G ⧸ N`, so `(inflate N χbar) n = χbar 1 = (inflate N χbar) 1`, i.e. `n` lies in the
character kernel of `inflate N χbar`.

This places the image of the inflation map inside `{χ ∈ Irr G | N ⊆ ker χ}`, the set that the
Peterfalvi (6.6) degree-sum bookkeeping ranges over. -/
theorem subset_characterKernel_inflate (χbar : IrreducibleCharacter (G ⧸ N)) :
    (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel
      ((inflate N χbar : IrreducibleCharacter G) : ClassFunction G ℂ) := by
  intro n hn
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def, inflate_apply, inflate_apply_one,
    (QuotientGroup.mk'_apply N n).trans ((QuotientGroup.eq_one_iff n).mpr hn)]

variable [Finite G]

/-- **Character-kernel translation invariance.**  If `g` lies in the character kernel of an
irreducible character `χ` (`χ(g) = χ(1)`), then `χ(x·g) = χ(x)` for every `x : G`.  The
diagonalization keystone (`rep_eq_id_of_character_eq_one`) forces the witnessing representation
to satisfy `ρ g = id`, so `χ(x·g) = tr(ρ(x) ∘ ρ(g)) = tr(ρ(x)) = χ(x)`. -/
theorem apply_mul_eq_of_mem_characterKernel {χ : ClassFunction G ℂ}
    (hχ : IsIrreducibleCharacter χ) {g : G}
    (hg : g ∈ OddOrder.Peterfalvi.S03.characterKernel χ) (x : G) :
    χ (x * g) = χ x := by
  obtain ⟨V, _, _, _, ρ, _, hval⟩ := hχ
  have hker : ρ.character g = ρ.character 1 := by
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hg
    rw [← congrFun hval g, ← congrFun hval 1]
    exact hg
  have hid : ρ g = LinearMap.id := rep_eq_id_of_character_eq_one ρ hker
  have hrep : ρ (x * g) = ρ x := by
    rw [map_mul, hid, ← Module.End.one_eq_id, mul_one]
  rw [show χ (x * g) = ρ.character (x * g) from congrFun hval (x * g),
    show χ x = ρ.character x from congrFun hval x]
  exact congrArg (LinearMap.trace ℂ V) hrep

/-- **Inflation is surjective onto the kernel-containing irreducible characters** ([Isaacs] (2.22),
the reverse inclusion).  Every irreducible character `χ` of `G` whose character kernel contains the
normal subgroup `N` arises by inflation: there is an irreducible character `χbar` of `G ⧸ N` with
`inflate N χbar = χ`.

This is the half of the inflation bijection that the **diagonalization keystone**
(`rep_eq_id_of_character_eq_one`) unlocks.  Take a witnessing irreducible representation `ρ` of `G`
with `χ = χ_ρ`.  For `n ∈ N`, `N ⊆ ker χ` gives `χ_ρ(n) = χ_ρ(1)`, so the keystone forces
`ρ n = id`; i.e. `ρ` is trivial on `N`.  Hence `ρ` descends through the quotient
(`Representation.ofQuotient`) to a representation `σ` of `G ⧸ N` with `σ.comp (mk' N) = ρ`, which is
irreducible because `ρ` is (`isIrreducible_of_isIrreducible_comp_of_surjective`).  Then
`χbar := χ_σ` is an irreducible character of `G ⧸ N`, and `inflate N χbar = χ_σ ∘ mk' = χ_ρ = χ`.

Together with `inflate_injective`, `inflate_apply_one` (degree preservation) and
`subset_characterKernel_inflate`, this realizes the inflation map as a degree-preserving
*bijection* `Irr(G ⧸ N) ≃ {χ ∈ Irr G | N ⊆ ker χ}`, hence the (6.6) degree-sum identity
`Σ_{N ⊆ ker χ} χ(1)² = |G ⧸ N|`. -/
theorem exists_inflate_eq_of_subset_characterKernel (χ : IrreducibleCharacter G)
    (hker : (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel
      (χ : ClassFunction G ℂ)) :
    ∃ χbar : IrreducibleCharacter (G ⧸ N), inflate N χbar = χ := by
  -- Unpack a witnessing irreducible representation `ρ` of `G` with `χ = χ_ρ`.
  obtain ⟨V, _, _, _, ρ, hρ, hχ⟩ := χ.isIrreducible
  -- The keystone makes `ρ` trivial on `N`: `n ∈ N ⟹ χ_ρ(n) = χ_ρ(1) ⟹ ρ n = id`.
  have htriv : Representation.IsTrivial (ρ.comp N.subtype) := by
    refine ⟨fun n => ?_⟩
    have hval : ρ.character (n : G) = ρ.character 1 := by
      have hn := hker n.2
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hn
      rw [← congrFun hχ (n : G), ← congrFun hχ 1]
      exact hn
    exact OddOrder.RepresentationTheory.rep_eq_id_of_character_eq_one ρ hval
  -- Descend `ρ` to `σ = ofQuotient ρ N` on `G ⧸ N`; then `σ.comp (mk' N) = ρ`.
  set σ : Representation ℂ (G ⧸ N) V := Representation.ofQuotient ρ N with hσ_def
  have hcomp : σ.comp (QuotientGroup.mk' N) = ρ := by
    ext g v
    simp [hσ_def, Representation.ofQuotient_coe_apply]
  -- `σ` is irreducible because `σ.comp (mk' N) = ρ` is.
  have hσ_irr : Representation.IsIrreducible σ :=
    Representation.isIrreducible_of_isIrreducible_comp_of_surjective σ
      (QuotientGroup.mk'_surjective N) (by rw [hcomp]; exact hρ)
  -- `χbar := χ_σ` is an irreducible character of `G ⧸ N`.
  refine ⟨⟨OddOrder.RepresentationTheory.repCharacterClassFunction σ,
    V, inferInstance, inferInstance, inferInstance, σ, hσ_irr, rfl⟩, ?_⟩
  -- `inflate N χbar = χ_σ ∘ mk' = χ_ρ = χ`.
  apply Subtype.ext
  ext g
  rw [inflate_apply]
  change σ.character (QuotientGroup.mk' N g) = (χ : ClassFunction G ℂ) g
  rw [show σ.character (QuotientGroup.mk' N g)
      = Representation.character (σ.comp (QuotientGroup.mk' N)) g from rfl,
    hcomp, ← congrFun hχ g]

/-- **An irreducible character with abelian image is linear** (degree one).  If `ψ ∈ Irr G` is
trivial on a normal subgroup `N ⊴ G` (`N ⊆ ker ψ` as character kernel) whose quotient `G ⧸ N` is
commutative, then `ψ(1) = 1`.

`ψ` descends through the quotient (`exists_inflate_eq_of_subset_characterKernel`) to an irreducible
character `ψbar` of the *commutative* group `G ⧸ N`, which has degree one
(`IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative`); inflation preserves degree
(`inflate_apply_one`), so `ψ(1) = ψbar(1) = 1`.

This is Peterfalvi (9.9.a)'s "`(θλ)(1) = 1`": the `HC`-character `ψ` lying under `χ ∈ 𝒳(H₀C')` is
linear because `[HC,HC]` lies in its kernel (`[H,H] ⊆ H₀`, `[H,C] ⊆ H₀` as `C = C_U(H̄)`, and
`[C,C] = C' ⊆ ker χ`), so the quotient by that commutator is abelian. -/
theorem apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
    [IsMulCommutative (G ⧸ N)] (ψ : IrreducibleCharacter G)
    (hker : (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction G ℂ)) :
    (ψ : ClassFunction G ℂ) 1 = 1 := by
  obtain ⟨ψbar, hψbar⟩ := exists_inflate_eq_of_subset_characterKernel (N := N) ψ hker
  rw [← hψbar, inflate_apply_one]
  exact ψbar.isIrreducible.apply_one_eq_one_of_isMulCommutative

/-- **Section form of [Is] Corollary 2.30.**  If an irreducible character `φ` of
`G` is trivial on the normal subgroup `N`, `N ≤ D`, and the image `D ⧸ N` is
central in `G ⧸ N`, then `φ(1)² ≤ |G : D|`.

Inflating `φ` from `G ⧸ N` — where `D ⧸ N` is genuinely central, so the central
degree bound `IsIrreducibleCharacter.exists_degree_sq_le_index` applies — gives
`φ(1)² ≤ |G ⧸ N : D ⧸ N| = |G : D|`.  This is the section case of the Peterfalvi
(6.2)/(6.6) degree bound `θ(1) ≤ |K : C|·√|C : D|` (the central case is the
`N = ⊥` specialization). -/
theorem degree_sq_le_index_of_central_quotient
    (φ : IrreducibleCharacter G) (D : Subgroup G) (hND : N ≤ D)
    (hker : (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (φ : ClassFunction G ℂ))
    (hcentral : D.map (QuotientGroup.mk' N) ≤ Subgroup.center (G ⧸ N)) :
    ∃ d : ℕ, (φ : ClassFunction G ℂ) 1 = (d : ℂ) ∧ d ^ 2 ≤ D.index := by
  classical
  obtain ⟨φbar, hφbar⟩ := exists_inflate_eq_of_subset_characterKernel (N := N) φ hker
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have : Invertible ((Nat.card (G ⧸ N) : ℂ)) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨d, hd1, hd2⟩ := φbar.isIrreducible.exists_degree_sq_le_index
    (D.map (QuotientGroup.mk' N)) hcentral
  have hidx : (D.map (QuotientGroup.mk' N)).index = D.index := by
    have h := Subgroup.index_comap_of_surjective (D.map (QuotientGroup.mk' N))
      (QuotientGroup.mk'_surjective N)
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hND] at h
    exact h.symm
  refine ⟨d, ?_, hidx ▸ hd2⟩
  rw [← hφbar, inflate_apply_one]
  exact hd1

open scoped Classical in
/-- **Peterfalvi (6.6) degree-sum identity** ([Isaacs] (2.22) corollary).  The sum of the squared
degrees over exactly the irreducible characters of `G` whose kernel contains the normal subgroup
`N` equals the order of the quotient `G ⧸ N`:
`∑_{χ ∈ Irr G, N ⊆ ker χ} χ(1)² = |G ⧸ N|` in `ℂ`.

This is the payoff of the **diagonalization keystone**: the keystone makes
`exists_inflate_eq_of_subset_characterKernel` (the surjectivity of inflation onto the
kernel-containing characters) available, so together with `inflate_injective`,
`subset_characterKernel_inflate` (image lands in the kernel-subset set) and `inflate_apply_one`
(degree preservation) the inflation map is a degree-preserving **bijection**
`Irr(G ⧸ N) ≃ {χ ∈ Irr G | N ⊆ ker χ}`.  Transporting the Burnside identity
`sumIrreducibleDegreeSq` for `G ⧸ N` (`∑_{χbar ∈ Irr (G ⧸ N)} χbar(1)² = |G ⧸ N|`) across this
bijection — via `Finset.sum_bij'` with `inflate N` as the forward map and the inflation-surjectivity
witness as its inverse — yields the displayed identity.

This is the form Peterfalvi (6.6) reads off the inflation correspondence: the irreducible
characters of `G` killing `N` are precisely the inflations of those of `G ⧸ N`, and their squared
degrees sum to `|G ⧸ N|` by Burnside on the quotient. -/
theorem sumInflatedDegreeSq :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter G =>
        (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ)),
        ((χ : ClassFunction G ℂ) 1) ^ 2 = (Nat.card (G ⧸ N) : ℂ) := by
  rw [← sumIrreducibleDegreeSq (G := G ⧸ N)]
  refine (Finset.sum_bij' (fun χbar _ => inflate N χbar)
    (fun χ hχ => (exists_inflate_eq_of_subset_characterKernel N χ
      ((Finset.mem_filter.mp hχ).2)).choose)
    (fun χbar _ => by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, subset_characterKernel_inflate N χbar⟩)
    (fun _ _ => Finset.mem_univ _)
    (fun χbar _ => by
      -- `choose (inflate N χbar) = χbar` by injectivity of `inflate N`.
      apply inflate_injective N
      exact (exists_inflate_eq_of_subset_characterKernel N (inflate N χbar)
        (subset_characterKernel_inflate N χbar)).choose_spec)
    (fun χ hχ => (exists_inflate_eq_of_subset_characterKernel N χ
      ((Finset.mem_filter.mp hχ).2)).choose_spec)
    (fun χbar _ => by rw [inflate_apply_one])).symm

open scoped Classical in
/-- **The non-trivial inflated degree-sum.**  Removing the trivial character from
`sumInflatedDegreeSq`: the squared degrees of the *non-trivial* irreducibles of `G` killing `N`
sum to `|G ⧸ N| − 1`:
`∑_{χ ∈ Irr G, N ⊆ ker χ, χ ≠ 1} χ(1)² = |G ⧸ N| − 1`.

This is the `∑_{θ ∈ Irr K, A ⊆ ker θ, θ ≠ 1_K} θ(1)² = |K : A| − 1` ingredient of Peterfalvi (6.2)'s
degree-sum (mmd 04.8 L7), with `G = K`, `N = A`: the irreducibles of `K` containing `A` in their
kernel are the inflations of `Irr(K ⧸ A)`, whose non-trivial squared degrees sum to `|K : A| − 1`
(Burnside on `K ⧸ A`, `sumInflatedDegreeSq`, minus the trivial character's `1² = 1`). -/
theorem sumInflatedDegreeSq_ntrivial :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter G =>
        (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ) ∧
          χ ≠ trivialIrreducibleCharacter G),
        ((χ : ClassFunction G ℂ) 1) ^ 2 = (Nat.card (G ⧸ N) : ℂ) - 1 := by
  classical
  have hsplit : (Finset.univ.filter (fun χ : IrreducibleCharacter G =>
        (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ))) =
      insert (trivialIrreducibleCharacter G) (Finset.univ.filter
        (fun χ : IrreducibleCharacter G =>
          (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ) ∧
            χ ≠ trivialIrreducibleCharacter G)) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
    constructor
    · intro hχ
      by_cases h : χ = trivialIrreducibleCharacter G
      · exact Or.inl h
      · exact Or.inr ⟨hχ, h⟩
    · rintro (rfl | ⟨hχ, _⟩)
      · simp
      · exact hχ
  have hnotmem : trivialIrreducibleCharacter G ∉ Finset.univ.filter
      (fun χ : IrreducibleCharacter G =>
        (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ) ∧
          χ ≠ trivialIrreducibleCharacter G) := by
    simp
  have hfull := sumInflatedDegreeSq (N := N)
  rw [hsplit, Finset.sum_insert hnotmem] at hfull
  have htrivdeg : ((trivialIrreducibleCharacter G : ClassFunction G ℂ) 1) ^ 2 = 1 := by simp
  rw [htrivdeg] at hfull
  linear_combination hfull

open scoped Classical in
/-- **Peterfalvi (6.6)/(6.8.3) degree-sum: the `N ⊄ ker χ` part.**

The squared degrees of the irreducible characters of `G` *not* killing `N` sum to `|G| − |G ⧸ N|`:
`∑_{χ ∈ Irr G, N ⊄ ker χ} χ(1)² = |G| − |G ⧸ N|` in `ℂ`.

The complement of `sumInflatedDegreeSq` inside the Burnside total `sumIrreducibleDegreeSq`
(`∑_{χ ∈ Irr G} χ(1)² = |G|`): the filter on `N ⊆ ker χ` and its negation partition `Irr G`
(`Finset.sum_filter_add_sum_filter_not`), so the `N ⊄ ker χ` sum is `|G|` minus the `N ⊆ ker χ`
sum `|G ⧸ N|`.

This is the (6.6)/(6.8) set `X = S − S(Z) = {χ ∈ Irr L | Z ⊄ ker χ}` degree-sum: with `N = Z`,
`∑_{χ ∈ X} χ(1)² = |L| − |L : Z|` (mmd 04.8 L78, L234), the total feeding the (6.6) per-step
square-divisibility (`∑_{j<i} χⱼ(1)² = |L| − |L:Z| − ∑_{j≥i} χⱼ(1)²`) and the (6.8.3) final
inequality `∑_{χ ∈ X} χ(1)²/‖χ‖² = |W₁||H:Z|(|Z|−1)`. -/
theorem sumNonInflatedDegreeSq :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter G =>
        ¬ (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ)),
        ((χ : ClassFunction G ℂ) 1) ^ 2 = (Nat.card G : ℂ) - (Nat.card (G ⧸ N) : ℂ) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (IrreducibleCharacter G))
    (fun χ => (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ))
    (fun χ => ((χ : ClassFunction G ℂ) 1) ^ 2)
  rw [sumInflatedDegreeSq (N := N),
    show (∑ χ : IrreducibleCharacter G, ((χ : ClassFunction G ℂ) 1) ^ 2) = (Nat.card G : ℂ) from
      sumIrreducibleDegreeSq] at hsplit
  linear_combination hsplit

open scoped Classical in
/-- **Peterfalvi (6.8.1) regular-character decomposition, off-identity value.**  For `z ∈ N^#`
(`z ∈ N`, `z ≠ 1`), the `N ⊄ ker χ` part of the regular character of `G` evaluated at `z` is
`-|G ⧸ N|`:
`∑_{χ ∈ Irr G, N ⊄ ker χ} χ(1)·χ(z) = -|G ⧸ N|` in `ℂ`.

This is the off-identity companion of `sumNonInflatedDegreeSq` (the `z = 1` value
`∑_{N ⊄ ker χ} χ(1)² = |G| − |G ⧸ N|`): the class function `ψ_N := ∑_{N ⊄ ker χ} χ(1)·χ`
(`= ρ_G − ρ_{G ⧸ N}`, the difference of regular characters) is constant on `N^#` with value
`-|G ⧸ N|`, so `ψ_N(z) − ψ_N(1) = -|G|` for `z ∈ N^#`.

Two ingredients: the **full** regular character vanishes off `1`
(`∑_{χ ∈ Irr G} χ(1)·χ(z) = 0`, second/column orthogonality `column_orthogonality_not_conjugate`
at the non-conjugate pair `z ≁ 1`); and the **`N ⊆ ker χ`** part is the regular character of
`G ⧸ N` at `mk z = 1`: each such `χ` is constant on `N`, so `χ(z) = χ(1)`, whence
`∑_{N ⊆ ker χ} χ(1)·χ(z) = ∑_{N ⊆ ker χ} χ(1)² = |G ⧸ N|` (`sumInflatedDegreeSq`).  Subtracting,
the `N ⊄ ker χ` part is `0 − |G ⧸ N|`.

With `G = L`, `N = Z`, this is the mmd 04.8 L168 identity
`∑ d_iχ_i(z) = (1/(a|W₁|))(ρ_L − ρ_{L/Z})(z) = -|L:Z|/(a|W₁|)`, the step showing `η₁^{τ₁}` is
constant on `Z^#` in Peterfalvi (6.8.1). -/
theorem sumNonInflatedDegreeMulChar_of_mem {z : G} (hz : z ∈ N) (hz1 : z ≠ 1) :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter G =>
        ¬ (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ)),
        ((χ : ClassFunction G ℂ) 1) * ((χ : ClassFunction G ℂ) z)
      = -(Nat.card (G ⧸ N) : ℂ) := by
  classical
  -- (i) the full regular character vanishes off `1` (column orthogonality at `z ≁ 1`).
  have htot : ∑ χ : IrreducibleCharacter G,
      ((χ : ClassFunction G ℂ) 1) * ((χ : ClassFunction G ℂ) z) = 0 := by
    have hnc : ¬ IsConj z (1 : G) := fun h => hz1 (isConj_one_left.mp h)
    have hcol := column_orthogonality_not_conjugate (G := G) (g := z) (h := 1) hnc
    rw [← hcol]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
    rw [hd, star_natCast]; ring
  -- (ii) the `N ⊆ ker χ` part is the regular character of `G ⧸ N` at `mk z = 1`, i.e. `|G ⧸ N|`.
  have hker : ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter G =>
        (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ)),
        ((χ : ClassFunction G ℂ) 1) * ((χ : ClassFunction G ℂ) z)
      = (Nat.card (G ⧸ N) : ℂ) := by
    rw [← sumInflatedDegreeSq (N := N)]
    refine Finset.sum_congr rfl (fun χ hχ => ?_)
    rw [Finset.mem_filter] at hχ
    have hzk : z ∈ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ) := hχ.2 hz
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hzk
    rw [hzk, OddOrder.Peterfalvi.S03.characterDegree_def]; ring
  -- (iii) `N ⊄ ker χ` part = (full) − (`N ⊆ ker χ` part) = 0 − |G ⧸ N|.
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (IrreducibleCharacter G))
    (fun χ => (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ))
    (fun χ => ((χ : ClassFunction G ℂ) 1) * ((χ : ClassFunction G ℂ) z))
  rw [hker] at hsplit
  linear_combination hsplit + htot

/-- **Inflation preserves (ir)reducibility, both directions.**  For `N ⊴ G` and any class function
`ψ` of `G ⧸ N`, the pullback `compHom (mk' N) ψ` is an irreducible character of `G` iff `ψ` is an
irreducible character of `G ⧸ N`.

Forward is `IsIrreducibleCharacter.compHom_of_surjective` (`mk' N` is surjective).  Backward: an
irreducible `compHom (mk' N) ψ` has `N ⊆ ker` (it is constant `= ψ 1` on `N`), so by
`exists_inflate_eq_of_subset_characterKernel` it equals `inflate χ̄` for some irreducible `χ̄`;
since
`compHom (mk' N)` is injective (`compHom_injective_of_surjective`), `ψ = χ̄` is irreducible.

This is the reducibility correspondence of the §9↔§6 bridge: via the induction-inflation commute
`induceHU (inflate χ̄) = compHom (mk' N) (induce K̄ χ̄)`, the §9 member `φ = induceHU (inflate χ̄)`
is
reducible iff the §6 induction `induce K̄ χ̄` is (issue 1012, B2 bijection). -/
theorem isIrreducibleCharacter_compHom_mk'_iff (ψ : ClassFunction (G ⧸ N) ℂ) :
    IsIrreducibleCharacter (ClassFunction.compHom (QuotientGroup.mk' N) ψ) ↔
      IsIrreducibleCharacter ψ := by
  refine ⟨fun h => ?_, fun h => h.compHom_of_surjective (QuotientGroup.mk'_surjective N)⟩
  have hker : (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel
      (ClassFunction.compHom (QuotientGroup.mk' N) ψ) := by
    intro n hn
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
      ClassFunction.compHom_apply, ClassFunction.compHom_apply, map_one,
      show QuotientGroup.mk' N n = 1 from (QuotientGroup.eq_one_iff n).mpr hn]
  obtain ⟨χbar, hχbar⟩ := exists_inflate_eq_of_subset_characterKernel N
    (⟨ClassFunction.compHom (QuotientGroup.mk' N) ψ, h⟩ : IrreducibleCharacter G) hker
  have heq : ClassFunction.compHom (QuotientGroup.mk' N) (χbar : ClassFunction (G ⧸ N) ℂ)
      = ClassFunction.compHom (QuotientGroup.mk' N) ψ := by
    rw [← inflate_coe, hχbar]
  rw [← ClassFunction.compHom_injective_of_surjective (QuotientGroup.mk'_surjective N) heq]
  exact χbar.2

end Inflation

/-- **Inflation along an arbitrary surjective homomorphism.**  If `f : H →* G` is surjective and
`χ` is an irreducible character of `H` whose character kernel contains `ker f`, then `χ` factors
through `f`: there is an irreducible character `χbar` of `G` with `χ = χbar ∘ f`
(`compHom f χbar = χ`).

This generalizes `exists_inflate_eq_of_subset_characterKernel` (the case `f = mk' N`) to any
surjective `f`, by factoring `f = (quotientKerEquivOfSurjective f) ∘ mk' (ker f)` and transporting
the `mk'`-inflation `θ̄₀ : Irr(H ⧸ ker f)` across the iso `H ⧸ ker f ≃* G`.  It is the form needed
in Peterfalvi (6.8)(c2), where `f` is the subgroup corestriction `↥H →* ↥(H/⁅H,H⁆)`. -/
theorem exists_compHom_eq_of_subset_characterKernel {H G : Type*} [Group H] [Group G] [Finite H]
    {f : H →* G} (hf : Function.Surjective f) (χ : IrreducibleCharacter H)
    (hker : (f.ker : Set H) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction H ℂ)) :
    ∃ χbar : IrreducibleCharacter G,
      ClassFunction.compHom f (χbar : ClassFunction G ℂ) = (χ : ClassFunction H ℂ) := by
  -- Inflate from the kernel quotient, then transport along `e : H ⧸ ker f ≃* G`.
  obtain ⟨θ0, hθ0⟩ := exists_inflate_eq_of_subset_characterKernel f.ker χ hker
  set e : (H ⧸ f.ker) ≃* G := QuotientGroup.quotientKerEquivOfSurjective f hf with he_def
  refine ⟨⟨ClassFunction.compHom e.symm.toMonoidHom (θ0 : ClassFunction (H ⧸ f.ker) ℂ),
    IsIrreducibleCharacter.compHom_of_surjective e.symm.surjective θ0.isIrreducible⟩, ?_⟩
  -- `e ∘ mk' (ker f) = f`, hence `e.symm ∘ f = mk' (ker f)`.
  have he_fe : ∀ x : H, e (QuotientGroup.mk' f.ker x) = f x := fun x => by
    rw [he_def, QuotientGroup.mk'_apply]; exact QuotientGroup.kerLift_mk _ x
  have he_comp : e.symm.toMonoidHom.comp f = QuotientGroup.mk' f.ker := by
    apply MonoidHom.ext; intro x
    change e.symm (f x) = QuotientGroup.mk' f.ker x
    rw [← he_fe x, MulEquiv.symm_apply_apply]
  change ClassFunction.compHom f
    (ClassFunction.compHom e.symm.toMonoidHom (θ0 : ClassFunction (H ⧸ f.ker) ℂ)) =
      (χ : ClassFunction H ℂ)
  rw [ClassFunction.compHom_comp, he_comp, ← inflate_coe f.ker θ0, hθ0]

/-- **Inflation–kernel correspondence.**  For a group homomorphism `f : H →* G`, a class function
`χbar` of `G`, and a subgroup `A ≤ H`, the inflation `compHom f χbar` contains `A` in its character
kernel iff `χbar` contains the image `A.map f` in its character kernel:
`A ⊆ ker (compHom f χbar) ↔ A.map f ⊆ ker χbar`.

Pointwise, `(compHom f χbar)(x) = χbar(f x)` and `(compHom f χbar)(1) = χbar(1)`, so `x` lies in the
kernel of the inflation iff `f x` lies in the kernel of `χbar`; ranging `x` over `A` matches the
image `A.map f`.  This is the `H ⊄ ker χ ↔ H̄ ⊄ ker χ̄` bridge of the §9↔§6 reducible-count
bijection
(issue 1012): the §9 family `𝒳(H₀) ⊆ Irr(HU)` condition `H ⊄ ker` transports to the §6 condition
`H̄ ⊄ ker` on `Irr(K̄)` under the inflation `K̄ = HU/H₀ → HU`. -/
theorem subset_characterKernel_compHom_iff {H G : Type*} [Group H] [Group G]
    (f : H →* G) (χbar : ClassFunction G ℂ) (A : Subgroup H) :
    (A : Set H) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.compHom f χbar) ↔
      (A.map f : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel χbar := by
  simp only [Set.subset_def, SetLike.mem_coe, Subgroup.mem_map,
    OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
    ClassFunction.compHom_apply, map_one]
  constructor
  · rintro h y ⟨x, hx, rfl⟩
    exact h x hx
  · intro h x hx
    exact h (f x) ⟨x, hx, rfl⟩

/-- **A constituent not killing `A`** (constituent transitivity).  For subgroups `A ≤ B ≤ G` and an
irreducible `χ` of `G` with `A ⊄ ker χ`, some irreducible constituent `ψ` of `Res^G_B χ` (i.e. `χ`
lies over `ψ`) also has `A ⊄ ker ψ` (where `A` is realized inside `B` as `A.subgroupOf B`).

If every constituent `ψ` of `Res_B χ` killed `A`, then for `x ∈ A`, expanding `Res_B χ` in the
irreducible basis (`sum_inner_irreducibleCharacter_smul`) and evaluating at `x` would give
`χ(x) = ∑_ψ ⟨Res_B χ,ψ⟩ψ(x) = ∑_ψ ⟨Res_B χ,ψ⟩ψ(1) = χ(1)`, i.e. `A ⊆ ker χ` — contradiction.  This
is the Clifford-correspondent existence input: a constituent of `Res_{HC} χ` not killing `H`, hence
lying over a nontrivial chief-factor character, in Peterfalvi (9.9.a). -/
theorem exists_constituent_not_subset_characterKernel
    {A B : Subgroup G} [Fintype ↥B] [Invertible (Nat.card ↥B : ℂ)]
    [Finite (IrreducibleCharacter ↥B)]
    (hAB : A ≤ B) (χ : IrreducibleCharacter G)
    (hAχ : ¬ ((A : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction G ℂ))) :
    ∃ ψ : IrreducibleCharacter ↥B, IrreducibleCharacter.LiesOver B χ ψ ∧
      ¬ ((A.subgroupOf B : Set ↥B) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction ↥B ℂ)) := by
  classical
  have : Fintype (IrreducibleCharacter ↥B) := Fintype.ofFinite _
  by_contra hcon
  push Not at hcon
  apply hAχ
  intro x hx
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
  set xB : ↥B := ⟨x, hAB hx⟩ with hxB
  have hsum_apply : ∀ (s : Finset (IrreducibleCharacter ↥B))
      (F : IrreducibleCharacter ↥B → ClassFunction ↥B ℂ) (g : ↥B),
      (∑ ψ ∈ s, F ψ) g = ∑ ψ ∈ s, (F ψ) g := by
    intro s F g
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  have hfourier :=
    sum_inner_irreducibleCharacter_smul (ClassFunction.restrict B (χ : ClassFunction G ℂ))
  have key : (χ : ClassFunction G ℂ) x = (χ : ClassFunction G ℂ) 1 := by
    have e1 : (χ : ClassFunction G ℂ) x
        = (ClassFunction.restrict B (χ : ClassFunction G ℂ)) xB := by
      rw [ClassFunction.restrict_apply]
    have e2 : (χ : ClassFunction G ℂ) 1 = (ClassFunction.restrict B (χ : ClassFunction G ℂ)) 1 := by
      rw [ClassFunction.restrict_apply]; rfl
    rw [e1, e2, ← hfourier, hsum_apply, hsum_apply]
    refine Finset.sum_congr rfl (fun ψ _ => ?_)
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply]
    by_cases hm : ClassFunction.inner (ClassFunction.restrict B (χ : ClassFunction G ℂ))
        (ψ : ClassFunction ↥B ℂ) = 0
    · rw [hm]; ring
    · have hlo : IrreducibleCharacter.LiesOver B χ ψ := by
        rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def]; exact hm
      have hxmem : xB ∈ A.subgroupOf B := by rw [Subgroup.mem_subgroupOf]; exact hx
      have hψ := hcon ψ hlo hxmem
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hψ
      rw [hψ]
  rw [key]

end OddOrder.RepresentationTheory


