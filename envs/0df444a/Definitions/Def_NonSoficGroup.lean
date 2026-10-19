-- Prove2me | Definitions.Def_NonSoficGroup
-- name    : NonSoficGroup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-19T10:54:31.198+00:00
-- url     : https://prove2.me/theorems/55eb77c8-e8ab-44a7-a4a2-763ad44e6490
-- title:
--   NonSoficGroup
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
set_option autoImplicit true
noncomputable section
namespace SoficGroups
section
open Filter Topology
universe u v w
abbrev UnitaryRepresentation (G : Type u) (H : Type v) [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  G →* (H ≃ₗᵢ[ℂ] H)
open scoped Pointwise commutatorElement symmDiff
structure KazhdanPair (G : Type u) [Group G] where
  generators : Finset G
  kazhdanConstant : ℝ
  positive : 0 < kazhdanConstant
  invariant :
    ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (π : UnitaryRepresentation G H) (ξ : H),
      ‖ξ‖ = 1 →
      (∀ g ∈ generators, ‖π g ξ - ξ‖ < kazhdanConstant) →
      ∃ η : H, η ≠ 0 ∧ ∀ g : G, π g η = η
class HasPropertyT (G : Type u) [Group G] : Prop where
  exists_kazhdanPair : Nonempty (KazhdanPair.{u, v} G)
def normalizedHamming {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) : ℝ :=
  (hammingDist (fun y => p y) (fun y => q y) : ℝ) / Fintype.card Y
@[simp]
theorem normalizedHamming_self {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p : Equiv.Perm Y) : normalizedHamming p p = 0 := by
  simp [normalizedHamming]
structure PermutationModel (G : Type*) [Group G] where
  size : ℕ
  size_pos : 0 < size
  action : G → Equiv.Perm (Fin size)
  map_one : action 1 = 1
structure GoodOn {G : Type*} [Group G]
    (M : PermutationModel G) (F : Finset G) (ε : ℝ) : Prop where
  multiplicative : ∀ g ∈ F, ∀ h ∈ F,
    normalizedHamming (M.action (g * h)) (M.action g * M.action h) < ε
  separated : ∀ g ∈ F, g ≠ 1 →
    1 - ε < normalizedHamming (M.action g) 1
theorem GoodOn.mono {G : Type*} [Group G] {M : PermutationModel G}
    {F F' : Finset G} {ε : ℝ} (h : GoodOn M F' ε) (hF : F ⊆ F') :
    GoodOn M F ε where
  multiplicative g hg k hk := h.multiplicative g (hF hg) k (hF hk)
  separated g hg hne := h.separated g (hF hg) hne
class Sofic (G : Type*) [Group G] : Prop where
  approximation : ∀ (F : Finset G) (ε : ℝ), 0 < ε → ε < 1 →
    ∃ M : PermutationModel G, GoodOn M F ε
theorem normalizedHamming_permCongr
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (e : X ≃ Y) (p q : Equiv.Perm X) :
    normalizedHamming (e.permCongr p) (e.permCongr q) =
      normalizedHamming p q := by
  have hdist :
      hammingDist (fun y => e.permCongr p y) (fun y => e.permCongr q y) =
        hammingDist (fun x => p x) (fun x => q x) := by
    unfold hammingDist
    apply Finset.card_equiv e.symm
    intro y
    simp [Equiv.permCongr_apply, e.injective.eq_iff]
  unfold normalizedHamming
  rw [hdist, ← Fintype.card_congr e]
theorem hammingDist_prodCongr_refl_left
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (p q : Equiv.Perm Y) :
    hammingDist
      (fun z : X × Y => ((Equiv.refl X).prodCongr p) z)
      (fun z : X × Y => ((Equiv.refl X).prodCongr q) z) =
      Fintype.card X * hammingDist (fun y => p y) (fun y => q y) := by
  classical
  change
    (Finset.univ.filter fun z : X × Y =>
      (z.1, p z.2) ≠ (z.1, q z.2)).card =
      Fintype.card X *
        (Finset.univ.filter fun y : Y => p y ≠ q y).card
  have hfilter :
      (Finset.univ.filter fun z : X × Y =>
        (z.1, p z.2) ≠ (z.1, q z.2)) =
        (Finset.univ : Finset X) ×ˢ
          (Finset.univ.filter fun y : Y => p y ≠ q y) := by
    ext z
    simp
  rw [hfilter, Finset.card_product]
  rfl
theorem normalizedHamming_prodCongr_refl_left
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (hX : Fintype.card X ≠ 0)
    (p q : Equiv.Perm Y) :
    normalizedHamming
      ((Equiv.refl X).prodCongr p) ((Equiv.refl X).prodCongr q) =
      normalizedHamming p q := by
  unfold normalizedHamming
  rw [hammingDist_prodCongr_refl_left, Fintype.card_prod, Nat.cast_mul,
    Nat.cast_mul]
  exact mul_div_mul_left _ _ (by exact_mod_cast hX)
def amplifyModel {G : Type*} [Group G]
    (M : PermutationModel G) (k : ℕ) (hk : 0 < k) : PermutationModel G where
  size := k * M.size
  size_pos := Nat.mul_pos hk M.size_pos
  action g := finProdFinEquiv.permCongr
    ((Equiv.refl (Fin k)).prodCongr (M.action g))
  map_one := by
    ext x
    simp [M.map_one, Equiv.permCongr_apply, Equiv.prodCongr,
      Nat.mod_add_div]
theorem amplifyModel_normalizedHamming
    {G : Type*} [Group G] (M : PermutationModel G)
    (k : ℕ) (hk : 0 < k) (g h : G) :
    normalizedHamming ((amplifyModel M k hk).action g)
        ((amplifyModel M k hk).action h) =
      normalizedHamming (M.action g) (M.action h) := by
  change normalizedHamming
    (finProdFinEquiv.permCongr
      ((Equiv.refl (Fin k)).prodCongr (M.action g)))
    (finProdFinEquiv.permCongr
      ((Equiv.refl (Fin k)).prodCongr (M.action h))) = _
  rw [normalizedHamming_permCongr]
  apply normalizedHamming_prodCongr_refl_left
  simpa using hk.ne'
theorem amplifyModel_multiplicative_distance
    {G : Type*} [Group G] (M : PermutationModel G)
    (k : ℕ) (hk : 0 < k) (g h : G) :
    normalizedHamming
      ((amplifyModel M k hk).action (g * h))
      ((amplifyModel M k hk).action g *
        (amplifyModel M k hk).action h) =
    normalizedHamming (M.action (g * h))
      (M.action g * M.action h) := by
  have hprod (p q : Equiv.Perm (Fin M.size)) :
      ((Equiv.refl (Fin k)).prodCongr p) *
        ((Equiv.refl (Fin k)).prodCongr q) =
      (Equiv.refl (Fin k)).prodCongr (p * q) := by
    apply Equiv.ext
    intro z
    exact Prod.ext rfl rfl
  change
    normalizedHamming
      (finProdFinEquiv.permCongr
        ((Equiv.refl (Fin k)).prodCongr (M.action (g * h))))
      (finProdFinEquiv.permCongr
        ((Equiv.refl (Fin k)).prodCongr (M.action g)) *
        finProdFinEquiv.permCongr
        ((Equiv.refl (Fin k)).prodCongr (M.action h))) = _
  rw [← Equiv.permCongr_mul, normalizedHamming_permCongr, hprod]
  apply normalizedHamming_prodCongr_refl_left
  simpa using hk.ne'
theorem amplifyModel_separation_distance
    {G : Type*} [Group G] (M : PermutationModel G)
    (k : ℕ) (hk : 0 < k) (g : G) :
    normalizedHamming ((amplifyModel M k hk).action g) 1 =
      normalizedHamming (M.action g) 1 := by
  calc
    normalizedHamming ((amplifyModel M k hk).action g) 1 =
        normalizedHamming ((amplifyModel M k hk).action g)
          ((amplifyModel M k hk).action 1) := by
            rw [PermutationModel.map_one]
    _ = normalizedHamming (M.action g) (M.action 1) :=
      amplifyModel_normalizedHamming M k hk g 1
    _ = normalizedHamming (M.action g) 1 := by rw [M.map_one]
structure SoficApproximation (G : Type*) [Group G] where
  model : ℕ → PermutationModel G
  multiplicative : ∀ g h : G,
    Tendsto
      (fun n => normalizedHamming
        ((model n).action (g * h)) ((model n).action g * (model n).action h))
      atTop (𝓝 0)
  separated : ∀ g : G, g ≠ 1 →
    Tendsto
      (fun n => normalizedHamming ((model n).action g) 1)
      atTop (𝓝 1)
def pullbackPermutationModel {G H : Type*} [Group G] [Group H]
    (f : H →* G) (M : PermutationModel G) : PermutationModel H where
  size := M.size
  size_pos := M.size_pos
  action h := M.action (f h)
  map_one := by simpa using M.map_one
def pullbackSoficApproximation {G H : Type*} [Group G] [Group H]
    (f : H →* G) (hf : Function.Injective f)
    (A : SoficApproximation G) : SoficApproximation H where
  model n := pullbackPermutationModel f (A.model n)
  multiplicative g h := by
    convert A.multiplicative (f g) (f h) using 1
    funext n
    change
      normalizedHamming ((A.model n).action (f (g * h)))
        ((A.model n).action (f g) * (A.model n).action (f h)) =
      normalizedHamming ((A.model n).action (f g * f h))
        ((A.model n).action (f g) * (A.model n).action (f h))
    rw [map_mul]
  separated g hg := by
    have hfg : f g ≠ 1 := by
      intro he
      apply hg
      apply hf
      simpa using he
    convert A.separated (f g) hfg using 1
    funext n
    rfl
def amplifyApproximation {G : Type*} [Group G]
    (A : SoficApproximation G) : SoficApproximation G where
  model n := amplifyModel (A.model n) (n + 1) (Nat.zero_lt_succ n)
  multiplicative g h := by
    simpa only [amplifyModel_multiplicative_distance] using
      A.multiplicative g h
  separated g hg := by
    simpa only [amplifyModel_separation_distance] using
      A.separated g hg
noncomputable def multiplicationTable {G : Type*} [Group G]
    (F : Finset G) : Finset G := by
  classical
  exact F ∪ (F.product F).image (fun x : G × G => x.1 * x.2)
theorem mem_multiplicationTable_of_mem {G : Type*} [Group G]
    {F : Finset G} {g : G} (hg : g ∈ F) : g ∈ multiplicationTable F := by
  classical
  simp [multiplicationTable, hg]
theorem mul_mem_multiplicationTable {G : Type*} [Group G]
    {F : Finset G} {g h : G} (hg : g ∈ F) (hh : h ∈ F) :
    g * h ∈ multiplicationTable F := by
  classical
  change g * h ∈ F ∪ (F.product F).image (fun x : G × G => x.1 * x.2)
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr
    ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, rfl⟩
noncomputable def tableRelators {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) :
    Finset (FreeGroup ↥(multiplicationTable F)) := by
  classical
  let oneGenerator : ↥(multiplicationTable F) :=
    ⟨1, mem_multiplicationTable_of_mem h₁⟩
  let word (x : ↥F × ↥F) : FreeGroup ↥(multiplicationTable F) :=
    FreeGroup.of ⟨x.1.1, mem_multiplicationTable_of_mem x.1.2⟩ *
      FreeGroup.of ⟨x.2.1, mem_multiplicationTable_of_mem x.2.2⟩ *
      (FreeGroup.of
        ⟨x.1.1 * x.2.1, mul_mem_multiplicationTable x.1.2 x.2.2⟩)⁻¹
  exact {FreeGroup.of oneGenerator} ∪ (F.attach.product F.attach).image word
abbrev tableGroup {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) : Type _ :=
  PresentedGroup (tableRelators F h₁ : Set (FreeGroup ↥(multiplicationTable F)))
noncomputable def tableGenerator {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) (g : ↥(multiplicationTable F)) :
    tableGroup F h₁ :=
  PresentedGroup.of g
theorem tableGenerator_one {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) :
    tableGenerator F h₁ ⟨1, mem_multiplicationTable_of_mem h₁⟩ = 1 := by
  classical
  change PresentedGroup.mk _ (FreeGroup.of _) = 1
  apply PresentedGroup.one_of_mem
  change FreeGroup.of _ ∈ tableRelators F h₁
  simp [tableRelators]
noncomputable def tableEvaluation {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) : tableGroup F h₁ →* G := by
  classical
  apply PresentedGroup.toGroup (f := fun g : ↥(multiplicationTable F) => g.1)
  intro r hr
  change r ∈ tableRelators F h₁ at hr
  simp only [tableRelators, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_image] at hr
  rcases hr with rfl | ⟨⟨g, h⟩, _, rfl⟩
  · simp
  · simp
@[simp]
theorem tableEvaluation_generator {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) (g : ↥(multiplicationTable F)) :
    tableEvaluation F h₁ (tableGenerator F h₁ g) = g.1 := by
  change PresentedGroup.toGroup _ (PresentedGroup.of g) = g.1
  exact PresentedGroup.toGroup.of _
noncomputable def tableTestSet {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) : Finset (tableGroup F h₁) := by
  classical
  exact F.attach.image fun g =>
    tableGenerator F h₁ ⟨g.1, mem_multiplicationTable_of_mem g.2⟩
noncomputable def pullbackTableModel {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F)
    (M : PermutationModel (tableGroup F h₁)) : PermutationModel G := by
  classical
  refine
    { size := M.size
      size_pos := M.size_pos
      action := fun g => if hg : g ∈ multiplicationTable F then
        M.action (tableGenerator F h₁ ⟨g, hg⟩) else 1
      map_one := ?_ }
  simp [mem_multiplicationTable_of_mem h₁, tableGenerator_one F h₁,
    M.map_one]
structure LocalMultiplicativeOn {G : Type u} {H : Type v}
    [Group G] [Group H] (s : Finset G) (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ x ∈ s, ∀ y ∈ s, f (x * y) = f x * f y
class LEF (G : Type u) [Group G] : Prop where
  approximate : ∀ s : Finset G, ∃ (n : ℕ) (f : G → Equiv.Perm (Fin n)),
    Set.InjOn f (s : Set G) ∧ LocalMultiplicativeOn s f
namespace LocalMultiplicativeOn
variable {G : Type u} {H : Type v} [Group G] [Group H]
theorem mono {s t : Finset G} {f : G → H}
    (h : LocalMultiplicativeOn t f) (hst : s ⊆ t) : LocalMultiplicativeOn s f where
  map_one := h.map_one
  map_mul x hx y hy := h.map_mul x (hst hx) y (hst hy)
end LocalMultiplicativeOn
def boundary {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (A : Finset V) : ℕ :=
  ∑ i : ι, (A.filter fun x => σ i x ∉ A).card
def agreementSet {V : Type*} [Fintype V] [DecidableEq V]
    (c c' : Equiv.Perm V) : Finset V :=
  Finset.univ.filter (fun x => c x = c' x)
def permutationCommutationDefect {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (c : Equiv.Perm V) : ℕ :=
  ∑ i : ι, (Finset.univ.filter fun x => c (σ i x) ≠ σ i (c x)).card
def inducedBoundary {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B E : Finset V) : ℕ :=
  ∑ i : ι, (E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E).card
def matchedRetainedSupport {V : Type*} [DecidableEq V]
    (R : Finset (Finset V)) : Finset V :=
  R.biUnion id
def matchedCore {V : Type*} [DecidableEq V]
    (R : Finset (Finset V)) (D : Finset V → Finset V) : Finset V :=
  R.biUnion fun C => C ∩ D C
def partitionWordCrossing {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U) (w : Equiv.Perm V) : Finset V :=
  U.filter (fun x => w x ∉ P.part x)
def matchedWordPreimageBad {V : Type*} [DecidableEq V]
    (U : Finset V) (R : Finset (Finset V))
    (D : Finset V → Finset V) (w : Equiv.Perm V) : Finset V :=
  U.filter (fun x => w x ∈ U \ matchedCore R D)
theorem exists_completion_of_internal_permutation {V : Type*}
    [Fintype V]
    (p : Equiv.Perm V) (Z : Finset V) :
    ∃ q : Equiv.Perm {x : V // x ∈ Z},
      ∀ (x : V) (hx : x ∈ Z) (_hp : p x ∈ Z),
        (q ⟨x, hx⟩ : V) = p x := by
  classical
  let A := {x : V // x ∈ Z ∧ p x ∈ Z}
  let f : A → {x : V // x ∈ Z} := fun x => ⟨x.1, x.2.1⟩
  let g : A → {x : V // x ∈ Z} := fun x => ⟨p x.1, x.2.2⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {x : V // x ∈ Z} => (z : V)) h
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact p.injective
      (congrArg (fun z : {x : V // x ∈ Z} => (z : V)) h)
  obtain ⟨q, hq⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨q, ?_⟩
  intro x hx hp
  have h := hq (⟨x, hx, hp⟩ : A)
  exact congrArg (fun z : {x : V // x ∈ Z} => (z : V)) h
def diagonalRadius (e : ℕ → ℕ → ℝ) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun k => e n k < 1 / ((k : ℝ) + 1)) n
inductive LeavittGenerator where
  | s : Fin 2 → LeavittGenerator
  | t : Fin 2 → LeavittGenerator
  deriving Fintype
abbrev LeavittFree : Type := FreeAlgebra (ZMod 2) LeavittGenerator
instance leavittFreeCountable : Countable LeavittFree :=
  ((FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := ZMod 2) (X := LeavittGenerator)).toEquiv.trans
    (MonoidAlgebra.coeffEquiv
      (R := ZMod 2) (M := FreeMonoid LeavittGenerator))).injective.countable
inductive LeavittRelation : LeavittFree → LeavittFree → Prop where
  | inverse (i j : Fin 2) :
      LeavittRelation
        (FreeAlgebra.ι (ZMod 2) (.t i) * FreeAlgebra.ι (ZMod 2) (.s j))
        (if i = j then 1 else 0)
  | partition :
      LeavittRelation
        (FreeAlgebra.ι (ZMod 2) (.s 0) * FreeAlgebra.ι (ZMod 2) (.t 0) +
          FreeAlgebra.ι (ZMod 2) (.s 1) * FreeAlgebra.ι (ZMod 2) (.t 1))
        1
abbrev BinaryLeavitt : Type := RingQuot LeavittRelation
instance binaryLeavittCountable : Countable BinaryLeavitt :=
  (RingQuot.mkAlgHom_surjective (ZMod 2) LeavittRelation).countable
def leavittQuotient : LeavittFree →ₐ[ZMod 2] BinaryLeavitt :=
  RingQuot.mkAlgHom (ZMod 2) LeavittRelation
instance binaryLeavittFiniteType : Algebra.FiniteType (ZMod 2) BinaryLeavitt :=
  Algebra.FiniteType.of_surjective leavittQuotient
    (RingQuot.mkAlgHom_surjective (ZMod 2) LeavittRelation)
def leavittS (i : Fin 2) : BinaryLeavitt :=
  leavittQuotient (FreeAlgebra.ι (ZMod 2) (.s i))
def leavittT (i : Fin 2) : BinaryLeavitt :=
  leavittQuotient (FreeAlgebra.ι (ZMod 2) (.t i))
theorem leavittT_mul_S (i j : Fin 2) :
    leavittT i * leavittS j = if i = j then 1 else 0 := by
  simpa [leavittT, leavittS, leavittQuotient] using
    RingQuot.mkAlgHom_rel (ZMod 2) (LeavittRelation.inverse i j)
theorem leavitt_partition :
    leavittS 0 * leavittT 0 + leavittS 1 * leavittT 1 = 1 := by
  simpa [leavittT, leavittS, leavittQuotient] using
    RingQuot.mkAlgHom_rel (ZMod 2) LeavittRelation.partition
abbrev leavittSequence : Type := ℕ → ZMod 2
def prefixOperator (i : Fin 2) : Module.End (ZMod 2) leavittSequence where
  toFun x n := if n % 2 = i.val then x (n / 2) else 0
  map_add' x y := by
    ext n
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' a x := by
    ext n
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp
def deletionOperator (i : Fin 2) : Module.End (ZMod 2) leavittSequence where
  toFun x n := x (2 * n + i.val)
  map_add' x y := by
    ext n
    rfl
  map_smul' a x := by
    ext n
    rfl
theorem deletion_mul_prefix (i j : Fin 2) :
    deletionOperator i * prefixOperator j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> ext x n <;>
    simp [deletionOperator, prefixOperator, Module.End.mul_apply, Nat.add_mod]
  congr 1
  omega
theorem prefix_deletion_partition :
    prefixOperator 0 * deletionOperator 0 +
      prefixOperator 1 * deletionOperator 1 = 1 := by
  ext x n
  simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply]
  change
    (if n % 2 = 0 then x (2 * (n / 2)) else 0) +
      (if n % 2 = 1 then x (2 * (n / 2) + 1) else 0) = x n
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> simp [h] <;> congr 1 <;> omega
def leavittGeneratorAction :
    LeavittGenerator → Module.End (ZMod 2) leavittSequence
  | .s i => prefixOperator i
  | .t i => deletionOperator i
def leavittFreeRepresentation :
    LeavittFree →ₐ[ZMod 2] Module.End (ZMod 2) leavittSequence :=
  FreeAlgebra.lift (ZMod 2) leavittGeneratorAction
theorem leavittFreeRepresentation_respects {x y : LeavittFree}
    (h : LeavittRelation x y) :
    leavittFreeRepresentation x = leavittFreeRepresentation y := by
  cases h with
  | inverse i j =>
      simp [leavittFreeRepresentation, leavittGeneratorAction,
        deletion_mul_prefix]
  | partition =>
      simpa [leavittFreeRepresentation, leavittGeneratorAction] using
        prefix_deletion_partition
def leavittRepresentation :
    BinaryLeavitt →ₐ[ZMod 2] Module.End (ZMod 2) leavittSequence :=
  RingQuot.liftAlgHom (ZMod 2)
    ⟨leavittFreeRepresentation, fun _ _ h => leavittFreeRepresentation_respects h⟩
@[simp] theorem leavittRepresentation_S (i : Fin 2) :
    leavittRepresentation (leavittS i) = prefixOperator i := by
  simp [leavittS, leavittQuotient, leavittRepresentation,
    leavittFreeRepresentation, leavittGeneratorAction]
@[simp] theorem leavittRepresentation_T (i : Fin 2) :
    leavittRepresentation (leavittT i) = deletionOperator i := by
  simp [leavittT, leavittQuotient, leavittRepresentation,
    leavittFreeRepresentation, leavittGeneratorAction]
instance binaryLeavittNontrivial : Nontrivial BinaryLeavitt :=
  leavittRepresentation.toRingHom.domain_nontrivial
theorem prefix_deletion_ne_one :
    prefixOperator 0 * deletionOperator 0 ≠ 1 := by
  intro h
  have h' := congrArg
    (fun f : Module.End (ZMod 2) leavittSequence => f (fun _ => 1) 1) h
  simp [prefixOperator, deletionOperator, Module.End.mul_apply] at h'
theorem leavittS_mul_T_ne_one : leavittS 0 * leavittT 0 ≠ 1 := by
  intro h
  apply prefix_deletion_ne_one
  simpa using congrArg leavittRepresentation h
instance binaryLeavittInfinite : Infinite BinaryLeavitt where
  not_finite h := by
    letI := h
    apply leavittS_mul_T_ne_one
    exact mul_eq_one_symm (by simpa using leavittT_mul_S 0 0)
def leavittWordS : List (Fin 2) → BinaryLeavitt
  | [] => 1
  | i :: a => leavittS i * leavittWordS a
def leavittWordT : List (Fin 2) → BinaryLeavitt
  | [] => 1
  | i :: a => leavittWordT a * leavittT i
theorem leavittWordT_mul_wordS_self (a : List (Fin 2)) :
    leavittWordT a * leavittWordS a = 1 := by
  induction a with
  | nil => simp [leavittWordT, leavittWordS]
  | cons i a ih =>
      calc
        leavittWordT (i :: a) * leavittWordS (i :: a) =
            leavittWordT a *
              ((leavittT i * leavittS i) * leavittWordS a) := by
                simp [leavittWordT, leavittWordS, mul_assoc]
        _ = 1 := by simp [leavittT_mul_S, ih]
theorem leavittWordT_mul_wordS_of_incomparable
    (a b : List (Fin 2)) (hab : ¬a <+: b) (hba : ¬b <+: a) :
    leavittWordT a * leavittWordS b = 0 := by
  induction a generalizing b with
  | nil => exact (hab (by simp)).elim
  | cons i a ih =>
      cases b with
      | nil => exact (hba (by simp)).elim
      | cons j b =>
          by_cases hij : i = j
          · subst j
            have hab' : ¬a <+: b := by
              intro hp
              apply hab
              simpa using hp
            have hba' : ¬b <+: a := by
              intro hp
              apply hba
              simpa using hp
            calc
              leavittWordT (i :: a) * leavittWordS (i :: b) =
                  leavittWordT a *
                    ((leavittT i * leavittS i) * leavittWordS b) := by
                      simp [leavittWordT, leavittWordS, mul_assoc]
              _ = leavittWordT a * leavittWordS b := by
                simp [leavittT_mul_S]
              _ = 0 := ih b hab' hba'
          · calc
              leavittWordT (i :: a) * leavittWordS (j :: b) =
                  leavittWordT a *
                    ((leavittT i * leavittS j) * leavittWordS b) := by
                      simp [leavittWordT, leavittWordS, mul_assoc]
              _ = 0 := by simp [leavittT_mul_S, hij]
theorem leavittWordS_append (a b : List (Fin 2)) :
    leavittWordS (a ++ b) = leavittWordS a * leavittWordS b := by
  induction a with
  | nil => simp [leavittWordS]
  | cons i a ih => simp [leavittWordS, ih, mul_assoc]
theorem leavittWordT_append (a b : List (Fin 2)) :
    leavittWordT (a ++ b) = leavittWordT b * leavittWordT a := by
  induction a with
  | nil => simp [leavittWordT]
  | cons i a ih => simp [leavittWordT, ih, mul_assoc]
def leavittCylinder (a : List (Fin 2)) : BinaryLeavitt :=
  leavittWordS a * leavittWordT a
theorem leavittCylinder_split (a : List (Fin 2)) :
    leavittCylinder a =
      leavittCylinder (a ++ [0]) + leavittCylinder (a ++ [1]) := by
  calc
    leavittCylinder a =
        leavittWordS a *
          (leavittS 0 * leavittT 0 + leavittS 1 * leavittT 1) *
          leavittWordT a := by
            rw [leavitt_partition]
            simp [leavittCylinder]
    _ = leavittCylinder (a ++ [0]) + leavittCylinder (a ++ [1]) := by
      simp [leavittCylinder, leavittWordS_append, leavittWordT_append,
        leavittWordS, leavittWordT, mul_add, add_mul, mul_assoc]
namespace MatrixCorner
variable {ι A : Type*} [Fintype ι] [Ring A]
def codeIdempotent (s t : ι → A) : A := ∑ i, s i * t i
def encode (s t : ι → A) (M : Matrix ι ι A) : A :=
  ∑ i, ∑ j, s i * M i j * t j
def decode (s t : ι → A) (x : A) : Matrix ι ι A :=
  fun i j => t i * x * s j
theorem decode_encode [DecidableEq ι] (s t : ι → A)
    (h : ∀ i j, t i * s j = if i = j then 1 else 0)
    (M : Matrix ι ι A) : decode s t (encode s t M) = M := by
  ext i j
  change t i * (∑ k, ∑ l, s k * M k l * t l) * s j = M i j
  calc
    t i * (∑ k, ∑ l, s k * M k l * t l) * s j =
        ∑ k, ∑ l, (t i * s k) * M k l * (t l * s j) := by
          simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = M i j := by simp [h]
theorem encode_decode (s t : ι → A) (x : A) :
    encode s t (decode s t x) =
      codeIdempotent s t * x * codeIdempotent s t := by
  change
    (∑ i, ∑ j, s i * (t i * x * s j) * t j) =
      (∑ i, s i * t i) * x * (∑ j, s j * t j)
  calc
    (∑ i, ∑ j, s i * (t i * x * s j) * t j) =
        ∑ i, ∑ j, (s i * t i) * x * (s j * t j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          simp [mul_assoc]
    _ = (∑ i, s i * t i) * x * (∑ j, s j * t j) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
theorem codeIdempotent_isIdempotent [DecidableEq ι] (s t : ι → A)
    (h : ∀ i j, t i * s j = if i = j then 1 else 0) :
    IsIdempotentElem (codeIdempotent s t) := by
  change (∑ i, s i * t i) * (∑ i, s i * t i) = ∑ i, s i * t i
  calc
    (∑ i, s i * t i) * (∑ i, s i * t i) =
        ∑ i, ∑ j, s i * (t i * s j) * t j := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp [mul_assoc]
    _ = ∑ i, s i * t i := by simp [h]
theorem encode_one [DecidableEq ι] (s t : ι → A) :
    encode s t (1 : Matrix ι ι A) = codeIdempotent s t := by
  simp [encode, codeIdempotent, Matrix.one_apply, mul_ite, ite_mul]
theorem encode_mul [DecidableEq ι] (s t : ι → A)
    (h : ∀ i j, t i * s j = if i = j then 1 else 0)
    (M N : Matrix ι ι A) :
    encode s t (M * N) = encode s t M * encode s t N := by
  symm
  calc
    encode s t M * encode s t N =
        ∑ i, ∑ j, ∑ k, ∑ l,
          s i * M i j * (t j * s k) * N k l * t l := by
            change
              (∑ i, ∑ j, s i * M i j * t j) *
                (∑ k, ∑ l, s k * N k l * t l) = _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            simp [mul_assoc]
    _ = ∑ i, ∑ j, ∑ l, s i * M i j * N j l * t l := by
      simp [h]
    _ = ∑ i, ∑ l, ∑ j, s i * M i j * N j l * t l := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = encode s t (M * N) := by
      simp only [encode, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp [mul_assoc]
def ringEquiv [DecidableEq ι] (s t : ι → A)
    (h : ∀ i j, t i * s j = if i = j then 1 else 0) :
    Matrix ι ι A ≃+* (codeIdempotent_isIdempotent s t h).Corner where
  toFun M :=
    ⟨encode s t M, ⟨encode s t M, by
      change
        codeIdempotent s t * encode s t M * codeIdempotent s t =
          encode s t M
      rw [← encode_decode, decode_encode s t h]⟩⟩
  invFun x := decode s t x.1
  left_inv M := decode_encode s t h M
  right_inv x := Subtype.ext <| by
    change encode s t (decode s t x.1) = x.1
    rw [encode_decode]
    have hx :=
      (Subsemigroup.mem_corner_iff
        (codeIdempotent_isIdempotent s t h)).mp x.property
    rw [hx.1, hx.2]
  map_mul' M N := Subtype.ext (encode_mul s t h M N)
  map_add' M N := Subtype.ext <| by
    change encode s t (M + N) = encode s t M + encode s t N
    simp [encode, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
end MatrixCorner
structure BinaryPrefixCode (ι : Type*) where
  word : ι → List (Fin 2)
  prefix_free : ∀ ⦃i j⦄, i ≠ j → ¬word i <+: word j
theorem binaryPrefixCode_orthogonal {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) (i j : ι) :
    leavittWordT (E.word i) * leavittWordS (E.word j) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [leavittWordT_mul_wordS_self]
  · simp only [hij, ↓reduceIte]
    exact leavittWordT_mul_wordS_of_incomparable _ _
      (E.prefix_free hij) (E.prefix_free (Ne.symm hij))
def binaryPrefixCornerEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    Matrix ι ι BinaryLeavitt ≃+*
      (MatrixCorner.codeIdempotent_isIdempotent
        (fun i => leavittWordS (E.word i))
        (fun i => leavittWordT (E.word i))
        (binaryPrefixCode_orthogonal E)).Corner :=
  MatrixCorner.ringEquiv
    (fun i => leavittWordS (E.word i))
    (fun i => leavittWordT (E.word i))
    (binaryPrefixCode_orthogonal E)
def prefixTable {ι : Type*} [Fintype ι]
    (source target : BinaryPrefixCode ι) : BinaryLeavitt :=
  ∑ i, leavittWordS (target.word i) * leavittWordT (source.word i)
theorem prefixTable_mul_reverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (source target : BinaryPrefixCode ι) :
    prefixTable source target * prefixTable target source =
      MatrixCorner.codeIdempotent
        (fun i => leavittWordS (target.word i))
        (fun i => leavittWordT (target.word i)) := by
  change
    (∑ i, leavittWordS (target.word i) * leavittWordT (source.word i)) *
        (∑ j, leavittWordS (source.word j) * leavittWordT (target.word j)) =
      ∑ i, leavittWordS (target.word i) * leavittWordT (target.word i)
  calc
    (∑ i, leavittWordS (target.word i) * leavittWordT (source.word i)) *
        (∑ j, leavittWordS (source.word j) * leavittWordT (target.word j)) =
        ∑ i, ∑ j,
          leavittWordS (target.word i) *
            (leavittWordT (source.word i) *
              leavittWordS (source.word j)) *
            leavittWordT (target.word j) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              simp [mul_assoc]
    _ = ∑ i, leavittWordS (target.word i) *
          leavittWordT (target.word i) := by
      simp [binaryPrefixCode_orthogonal]
def prefixTableUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (source target : BinaryPrefixCode ι)
    (hsource : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (source.word i))
      (fun i => leavittWordT (source.word i)) = 1)
    (htarget : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (target.word i))
      (fun i => leavittWordT (target.word i)) = 1) : BinaryLeavittˣ where
  val := prefixTable source target
  inv := prefixTable target source
  val_inv := (prefixTable_mul_reverse source target).trans htarget
  inv_val := (prefixTable_mul_reverse target source).trans hsource
def alphaWord : Fin 3 → List (Fin 2)
  | 0 => [0, 0, 0]
  | 1 => [0, 0, 1]
  | _ => [0, 1]
def betaWord : Fin 3 → List (Fin 2)
  | 0 => [1, 0, 0, 0]
  | 1 => [1, 0, 0, 1]
  | _ => [1, 0, 1]
def nuWord : Fin 3 → List (Fin 2)
  | 0 => [1, 1, 0, 0]
  | 1 => [1, 1, 0, 1]
  | _ => [1, 1, 1]
def etaWord : Fin 3 → List (Fin 2)
  | 0 => [1, 0, 0]
  | 1 => [1, 0, 1]
  | _ => [1, 1]
def nineWord : Fin 9 → List (Fin 2)
  | 0 => alphaWord 0
  | 1 => betaWord 0
  | 2 => nuWord 0
  | 3 => alphaWord 1
  | 4 => betaWord 1
  | 5 => nuWord 1
  | 6 => alphaWord 2
  | 7 => betaWord 2
  | _ => nuWord 2
def uWord : Fin 9 → List (Fin 2)
  | 0 => alphaWord 0 ++ [0]
  | 1 => alphaWord 0 ++ [1]
  | 2 => etaWord 0
  | 3 => alphaWord 1 ++ [0]
  | 4 => alphaWord 1 ++ [1]
  | 5 => etaWord 1
  | 6 => alphaWord 2 ++ [0]
  | 7 => alphaWord 2 ++ [1]
  | _ => etaWord 2
def vWord : Fin 9 → List (Fin 2)
  | 0 => alphaWord 0 ++ [0]
  | 1 => etaWord 0
  | 2 => alphaWord 0 ++ [1]
  | 3 => alphaWord 1 ++ [0]
  | 4 => etaWord 1
  | 5 => alphaWord 1 ++ [1]
  | 6 => alphaWord 2 ++ [0]
  | 7 => etaWord 2
  | _ => alphaWord 2 ++ [1]
def alphaPrefixCode : BinaryPrefixCode (Fin 3) where
  word := alphaWord
  prefix_free := by decide
def ninePrefixCode : BinaryPrefixCode (Fin 9) where
  word := nineWord
  prefix_free := by decide
def uPrefixCode : BinaryPrefixCode (Fin 9) where
  word := uWord
  prefix_free := by decide
def vPrefixCode : BinaryPrefixCode (Fin 9) where
  word := vWord
  prefix_free := by decide
theorem alpha_cylinders :
    leavittCylinder (alphaWord 0) +
        leavittCylinder (alphaWord 1) +
        leavittCylinder (alphaWord 2) =
      leavittCylinder [0] := by
  have h₀₀ :
      leavittCylinder [0, 0, 0] + leavittCylinder [0, 0, 1] =
        leavittCylinder [0, 0] := by
    simpa using (leavittCylinder_split [0, 0]).symm
  have h₀ :
      leavittCylinder [0, 0] + leavittCylinder [0, 1] =
        leavittCylinder [0] := by
    simpa using (leavittCylinder_split [0]).symm
  change
    leavittCylinder [0, 0, 0] +
        leavittCylinder [0, 0, 1] +
        leavittCylinder [0, 1] = leavittCylinder [0]
  rw [h₀₀, h₀]
theorem beta_cylinders :
    leavittCylinder (betaWord 0) +
        leavittCylinder (betaWord 1) +
        leavittCylinder (betaWord 2) =
      leavittCylinder [1, 0] := by
  have h₁₀₀ :
      leavittCylinder [1, 0, 0, 0] + leavittCylinder [1, 0, 0, 1] =
        leavittCylinder [1, 0, 0] := by
    simpa using (leavittCylinder_split [1, 0, 0]).symm
  have h₁₀ :
      leavittCylinder [1, 0, 0] + leavittCylinder [1, 0, 1] =
        leavittCylinder [1, 0] := by
    simpa using (leavittCylinder_split [1, 0]).symm
  change
    leavittCylinder [1, 0, 0, 0] +
        leavittCylinder [1, 0, 0, 1] +
        leavittCylinder [1, 0, 1] = leavittCylinder [1, 0]
  rw [h₁₀₀, h₁₀]
theorem nu_cylinders :
    leavittCylinder (nuWord 0) +
        leavittCylinder (nuWord 1) +
        leavittCylinder (nuWord 2) =
      leavittCylinder [1, 1] := by
  have h₁₁₀ :
      leavittCylinder [1, 1, 0, 0] + leavittCylinder [1, 1, 0, 1] =
        leavittCylinder [1, 1, 0] := by
    simpa using (leavittCylinder_split [1, 1, 0]).symm
  have h₁₁ :
      leavittCylinder [1, 1, 0] + leavittCylinder [1, 1, 1] =
        leavittCylinder [1, 1] := by
    simpa using (leavittCylinder_split [1, 1]).symm
  change
    leavittCylinder [1, 1, 0, 0] +
        leavittCylinder [1, 1, 0, 1] +
        leavittCylinder [1, 1, 1] = leavittCylinder [1, 1]
  rw [h₁₁₀, h₁₁]
theorem eta_cylinders :
    leavittCylinder (etaWord 0) +
        leavittCylinder (etaWord 1) +
        leavittCylinder (etaWord 2) =
      leavittCylinder [1] := by
  have h₁₀ :
      leavittCylinder [1, 0, 0] + leavittCylinder [1, 0, 1] =
        leavittCylinder [1, 0] := by
    simpa using (leavittCylinder_split [1, 0]).symm
  have h₁ :
      leavittCylinder [1, 0] + leavittCylinder [1, 1] =
        leavittCylinder [1] := by
    simpa using (leavittCylinder_split [1]).symm
  change
    leavittCylinder [1, 0, 0] +
        leavittCylinder [1, 0, 1] +
        leavittCylinder [1, 1] = leavittCylinder [1]
  rw [h₁₀, h₁]
theorem ninePrefixCode_complete :
    MatrixCorner.codeIdempotent
      (fun i => leavittWordS (ninePrefixCode.word i))
      (fun i => leavittWordT (ninePrefixCode.word i)) = 1 := by
  change (∑ i : Fin 9, leavittCylinder (nineWord i)) = 1
  have h₁ :
      leavittCylinder [1, 0] + leavittCylinder [1, 1] =
        leavittCylinder [1] := by
    simpa using (leavittCylinder_split [1]).symm
  have hroot : leavittCylinder [0] + leavittCylinder [1] = 1 := by
    simpa [leavittCylinder, leavittWordS, leavittWordT] using
      leavitt_partition
  calc
    (∑ i : Fin 9, leavittCylinder (nineWord i)) =
        (leavittCylinder (alphaWord 0) +
          leavittCylinder (alphaWord 1) +
          leavittCylinder (alphaWord 2)) +
        (leavittCylinder (betaWord 0) +
          leavittCylinder (betaWord 1) +
          leavittCylinder (betaWord 2)) +
        (leavittCylinder (nuWord 0) +
          leavittCylinder (nuWord 1) +
          leavittCylinder (nuWord 2)) := by
          simp [Fin.sum_univ_succ, nineWord]
          ac_rfl
    _ = leavittCylinder [0] +
          leavittCylinder [1, 0] + leavittCylinder [1, 1] := by
      rw [alpha_cylinders, beta_cylinders, nu_cylinders]
    _ = leavittCylinder [0] + leavittCylinder [1] := by
      rw [add_assoc, h₁]
    _ = 1 := hroot
theorem uPrefixCode_complete :
    MatrixCorner.codeIdempotent
      (fun i => leavittWordS (uPrefixCode.word i))
      (fun i => leavittWordT (uPrefixCode.word i)) = 1 := by
  change (∑ i : Fin 9, leavittCylinder (uWord i)) = 1
  have h₀ :
      leavittCylinder (alphaWord 0 ++ [0]) +
          leavittCylinder (alphaWord 0 ++ [1]) =
        leavittCylinder (alphaWord 0) :=
    (leavittCylinder_split (alphaWord 0)).symm
  have h₁ :
      leavittCylinder (alphaWord 1 ++ [0]) +
          leavittCylinder (alphaWord 1 ++ [1]) =
        leavittCylinder (alphaWord 1) :=
    (leavittCylinder_split (alphaWord 1)).symm
  have h₂ :
      leavittCylinder (alphaWord 2 ++ [0]) +
          leavittCylinder (alphaWord 2 ++ [1]) =
        leavittCylinder (alphaWord 2) :=
    (leavittCylinder_split (alphaWord 2)).symm
  have hroot : leavittCylinder [0] + leavittCylinder [1] = 1 := by
    simpa [leavittCylinder, leavittWordS, leavittWordT] using
      leavitt_partition
  calc
    (∑ i : Fin 9, leavittCylinder (uWord i)) =
        ((leavittCylinder (alphaWord 0 ++ [0]) +
            leavittCylinder (alphaWord 0 ++ [1])) +
          (leavittCylinder (alphaWord 1 ++ [0]) +
            leavittCylinder (alphaWord 1 ++ [1])) +
          (leavittCylinder (alphaWord 2 ++ [0]) +
            leavittCylinder (alphaWord 2 ++ [1]))) +
        (leavittCylinder (etaWord 0) +
          leavittCylinder (etaWord 1) +
          leavittCylinder (etaWord 2)) := by
          simp [Fin.sum_univ_succ, uWord]
          ac_rfl
    _ = (leavittCylinder (alphaWord 0) +
          leavittCylinder (alphaWord 1) +
          leavittCylinder (alphaWord 2)) + leavittCylinder [1] := by
      rw [h₀, h₁, h₂, eta_cylinders]
    _ = leavittCylinder [0] + leavittCylinder [1] := by
      rw [alpha_cylinders]
    _ = 1 := hroot
theorem vPrefixCode_complete :
    MatrixCorner.codeIdempotent
      (fun i => leavittWordS (vPrefixCode.word i))
      (fun i => leavittWordT (vPrefixCode.word i)) = 1 := by
  change (∑ i : Fin 9, leavittCylinder (vWord i)) = 1
  calc
    (∑ i : Fin 9, leavittCylinder (vWord i)) =
        ∑ i : Fin 9, leavittCylinder (uWord i) := by
          simp [Fin.sum_univ_succ, vWord, uWord]
          ac_rfl
    _ = 1 := uPrefixCode_complete
def compressionU : BinaryLeavittˣ :=
  prefixTableUnit ninePrefixCode uPrefixCode
    ninePrefixCode_complete uPrefixCode_complete
def compressionV : BinaryLeavittˣ :=
  prefixTableUnit ninePrefixCode vPrefixCode
    ninePrefixCode_complete vPrefixCode_complete
instance binaryLeavittCharP : CharP BinaryLeavitt 2 :=
  CharP.of_ringHom_of_ne_zero
    (algebraMap (ZMod 2) BinaryLeavitt) 2 (by decide)
theorem matrixUnitTransport_root
    {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι]
    (sSource tSource sTarget tTarget : ι → A)
    (hsource : ∀ i j, tSource i * sSource j = if i = j then 1 else 0)
    (i j : ι) (a : A) :
    (∑ k, sTarget k * tSource k) *
        (sSource i * a * tSource j) *
        (∑ k, sSource k * tTarget k) =
      sTarget i * a * tTarget j := by
  have hleft :
      (∑ k, sTarget k * tSource k) * sSource i = sTarget i := by
    calc
      (∑ k, sTarget k * tSource k) * sSource i =
          ∑ k, sTarget k * (tSource k * sSource i) := by
            simp only [Finset.sum_mul, mul_assoc]
      _ = sTarget i := by simp [hsource]
  have hright :
      tSource j * (∑ k, sSource k * tTarget k) = tTarget j := by
    calc
      tSource j * (∑ k, sSource k * tTarget k) =
          ∑ k, (tSource j * sSource k) * tTarget k := by
            simp only [Finset.mul_sum, mul_assoc]
      _ = tTarget j := by simp [hsource]
  calc
    (∑ k, sTarget k * tSource k) *
        (sSource i * a * tSource j) *
        (∑ k, sSource k * tTarget k) =
        ((∑ k, sTarget k * tSource k) * sSource i) * a *
          (tSource j * (∑ k, sSource k * tTarget k)) := by
            simp [mul_assoc]
    _ = sTarget i * a * tTarget j := by rw [hleft, hright]
theorem prefixTable_transport_root {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (source target : BinaryPrefixCode ι) (i j : ι)
    (a : BinaryLeavitt) :
    prefixTable source target *
        (leavittWordS (source.word i) * a *
          leavittWordT (source.word j)) *
        prefixTable target source =
      leavittWordS (target.word i) * a * leavittWordT (target.word j) := by
  exact matrixUnitTransport_root
    (fun k => leavittWordS (source.word k))
    (fun k => leavittWordT (source.word k))
    (fun k => leavittWordS (target.word k))
    (fun k => leavittWordT (target.word k))
    (binaryPrefixCode_orthogonal source) i j a
theorem compressionU_conjugate_root (i j : Fin 9) (a : BinaryLeavitt) :
    (compressionU : BinaryLeavitt) *
        (leavittWordS (nineWord i) * a * leavittWordT (nineWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) =
      leavittWordS (uWord i) * a * leavittWordT (uWord j) := by
  exact prefixTable_transport_root ninePrefixCode uPrefixCode i j a
theorem compressionV_conjugate_root (i j : Fin 9) (a : BinaryLeavitt) :
    (compressionV : BinaryLeavitt) *
        (leavittWordS (nineWord i) * a * leavittWordT (nineWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) =
      leavittWordS (vWord i) * a * leavittWordT (vWord j) := by
  exact prefixTable_transport_root ninePrefixCode vPrefixCode i j a
def alphaNineIndex (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val, by omega⟩
@[simp]
theorem nineWord_alphaNineIndex (i : Fin 3) :
    nineWord (alphaNineIndex i) = alphaWord i := by
  fin_cases i <;> rfl
@[simp]
theorem uWord_alphaNineIndex (i : Fin 3) :
    uWord (alphaNineIndex i) = alphaWord i ++ [0] := by
  fin_cases i <;> rfl
@[simp]
theorem vWord_alphaNineIndex (i : Fin 3) :
    vWord (alphaNineIndex i) = alphaWord i ++ [0] := by
  fin_cases i <;> rfl
theorem compressionU_conjugate_alpha_root
    (i j : Fin 3) (a : BinaryLeavitt) :
    (compressionU : BinaryLeavitt) *
        (leavittWordS (alphaWord i) * a * leavittWordT (alphaWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) =
      leavittWordS (alphaWord i ++ [0]) * a *
        leavittWordT (alphaWord j ++ [0]) := by
  simpa only [nineWord_alphaNineIndex, uWord_alphaNineIndex] using
    compressionU_conjugate_root (alphaNineIndex i) (alphaNineIndex j) a
theorem compressionV_conjugate_alpha_root
    (i j : Fin 3) (a : BinaryLeavitt) :
    (compressionV : BinaryLeavitt) *
        (leavittWordS (alphaWord i) * a * leavittWordT (alphaWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) =
      leavittWordS (alphaWord i ++ [0]) * a *
        leavittWordT (alphaWord j ++ [0]) := by
  simpa only [nineWord_alphaNineIndex, vWord_alphaNineIndex] using
    compressionV_conjugate_root (alphaNineIndex i) (alphaNineIndex j) a
def alphaZeroPrefixCode : BinaryPrefixCode (Fin 3) where
  word i := alphaWord i ++ [0]
  prefix_free := by decide
def prefixElementaryUnit {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) (i j : ι) (hij : i ≠ j)
    (a : BinaryLeavitt) : BinaryLeavittˣ := by
  let x := leavittWordS (E.word i) * a * leavittWordT (E.word j)
  have hzero : leavittWordT (E.word j) * leavittWordS (E.word i) = 0 := by
    simpa [hij.symm] using binaryPrefixCode_orthogonal E j i
  have hx : x * x = 0 := by
    dsimp [x]
    calc
      (leavittWordS (E.word i) * a * leavittWordT (E.word j)) *
          (leavittWordS (E.word i) * a * leavittWordT (E.word j)) =
        leavittWordS (E.word i) * a *
          (leavittWordT (E.word j) * leavittWordS (E.word i)) *
          a * leavittWordT (E.word j) := by
            simp [mul_assoc]
      _ = 0 := by rw [hzero]; simp
  exact
    { val := 1 + x
      inv := 1 - x
      val_inv := by noncomm_ring [hx]
      inv_val := by noncomm_ring [hx] }
def prefixElementaryGroup {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) : Subgroup BinaryLeavittˣ :=
  Subgroup.closure
    {z | ∃ (i j : ι) (h : i ≠ j) (a : BinaryLeavitt),
      prefixElementaryUnit E i j h a = z}
theorem compressionU_conjugate_alpha_elementaryUnit
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    MulAut.conj compressionU
        (prefixElementaryUnit alphaPrefixCode i j hij a) =
      prefixElementaryUnit alphaZeroPrefixCode i j hij a := by
  apply Units.ext
  change
    (compressionU : BinaryLeavitt) *
        (1 + leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) =
      1 + leavittWordS (alphaWord i ++ [0]) * a *
        leavittWordT (alphaWord j ++ [0])
  calc
    (compressionU : BinaryLeavitt) *
        (1 + leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) =
      1 + (compressionU : BinaryLeavitt) *
        (leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) := by
          simp [mul_add, add_mul]
    _ = 1 + leavittWordS (alphaWord i ++ [0]) * a *
          leavittWordT (alphaWord j ++ [0]) := by
      rw [compressionU_conjugate_alpha_root]
theorem compressionV_conjugate_alpha_elementaryUnit
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    MulAut.conj compressionV
        (prefixElementaryUnit alphaPrefixCode i j hij a) =
      prefixElementaryUnit alphaZeroPrefixCode i j hij a := by
  apply Units.ext
  change
    (compressionV : BinaryLeavitt) *
        (1 + leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) =
      1 + leavittWordS (alphaWord i ++ [0]) * a *
        leavittWordT (alphaWord j ++ [0])
  calc
    (compressionV : BinaryLeavitt) *
        (1 + leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) =
      1 + (compressionV : BinaryLeavitt) *
        (leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) := by
          simp [mul_add, add_mul]
    _ = 1 + leavittWordS (alphaWord i ++ [0]) * a *
          leavittWordT (alphaWord j ++ [0]) := by
      rw [compressionV_conjugate_alpha_root]
theorem prefixElementaryGroup_map_conj
    {ι : Type*} [DecidableEq ι]
    (E E' : BinaryPrefixCode ι) (g : BinaryLeavittˣ)
    (hconj : ∀ (i j : ι) (hij : i ≠ j) (a : BinaryLeavitt),
      MulAut.conj g (prefixElementaryUnit E i j hij a) =
        prefixElementaryUnit E' i j hij a) :
    (prefixElementaryGroup E).map (MulAut.conj g).toMonoidHom =
      prefixElementaryGroup E' := by
  unfold prefixElementaryGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, j, hij, a, rfl⟩, hz⟩
    exact ⟨i, j, hij, a, (hconj i j hij a).symm.trans hz⟩
  · rintro ⟨i, j, hij, a, rfl⟩
    exact ⟨prefixElementaryUnit E i j hij a,
      ⟨i, j, hij, a, rfl⟩, hconj i j hij a⟩
theorem compressionU_map_alphaPrefixElementaryGroup :
    (prefixElementaryGroup alphaPrefixCode).map
        (MulAut.conj compressionU).toMonoidHom =
      prefixElementaryGroup alphaZeroPrefixCode :=
  prefixElementaryGroup_map_conj alphaPrefixCode alphaZeroPrefixCode
    compressionU compressionU_conjugate_alpha_elementaryUnit
theorem compressionV_map_alphaPrefixElementaryGroup :
    (prefixElementaryGroup alphaPrefixCode).map
        (MulAut.conj compressionV).toMonoidHom =
      prefixElementaryGroup alphaZeroPrefixCode :=
  prefixElementaryGroup_map_conj alphaPrefixCode alphaZeroPrefixCode
    compressionV compressionV_conjugate_alpha_elementaryUnit
theorem alphaZero_prefixElementaryUnit_eq
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    prefixElementaryUnit alphaZeroPrefixCode i j hij a =
      prefixElementaryUnit alphaPrefixCode i j hij
        (leavittS 0 * a * leavittT 0) := by
  apply Units.ext
  change
    1 + leavittWordS (alphaWord i ++ [0]) * a *
      leavittWordT (alphaWord j ++ [0]) =
    1 + leavittWordS (alphaWord i) *
      (leavittS 0 * a * leavittT 0) * leavittWordT (alphaWord j)
  simp [leavittWordS_append, leavittWordT_append,
    leavittWordS, leavittWordT, mul_assoc]
theorem alphaZero_prefixElementaryGroup_le :
    prefixElementaryGroup alphaZeroPrefixCode ≤
      prefixElementaryGroup alphaPrefixCode := by
  rw [prefixElementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  rw [alphaZero_prefixElementaryUnit_eq]
  exact Subgroup.subset_closure
    ⟨i, j, hij, leavittS 0 * a * leavittT 0, rfl⟩
section NoncommutativeElementaryGroup
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
theorem single_mul_self_eq_zero (i j : ι) (h : i ≠ j) (a : R) :
    Matrix.single i j a * Matrix.single i j a = 0 :=
  Matrix.single_mul_single_of_ne (c := a) i j i h.symm a
def elementaryUnit (i j : ι) (h : i ≠ j) (a : R) : (Matrix ι ι R)ˣ where
  val := 1 + Matrix.single i j a
  inv := 1 - Matrix.single i j a
  val_inv := by
    have hx := single_mul_self_eq_zero i j h a
    noncomm_ring [hx]
  inv_val := by
    have hx := single_mul_self_eq_zero i j h a
    noncomm_ring [hx]
@[simp] theorem elementaryUnit_zero (i j : ι) (h : i ≠ j) :
    elementaryUnit (R := R) i j h 0 = 1 := by
  apply Units.ext
  simp [elementaryUnit]
theorem elementaryUnit_mul (i j : ι) (h : i ≠ j) (a b : R) :
    elementaryUnit i j h a * elementaryUnit i j h b =
      elementaryUnit i j h (a + b) := by
  apply Units.ext
  change
    (1 + Matrix.single i j a) * (1 + Matrix.single i j b) =
      1 + Matrix.single i j (a + b)
  have hab : Matrix.single i j a * Matrix.single i j b = 0 :=
    Matrix.single_mul_single_of_ne (c := a) i j i h.symm b
  rw [Matrix.single_add]
  noncomm_ring [hab]
def elementaryGroup (ι R : Type*) [Fintype ι] [DecidableEq ι] [Ring R] :
    Subgroup (Matrix ι ι R)ˣ :=
  Subgroup.closure
    {z | ∃ (i j : ι) (h : i ≠ j) (a : R), elementaryUnit i j h a = z}
theorem elementaryUnit_mem (i j : ι) (h : i ≠ j) (a : R) :
    elementaryUnit i j h a ∈ elementaryGroup ι R :=
  Subgroup.subset_closure ⟨i, j, h, a, rfl⟩
def elementaryRootHom (i j : ι) (h : i ≠ j) :
    Multiplicative R →* elementaryGroup ι R where
  toFun a := ⟨elementaryUnit i j h a.toAdd, elementaryUnit_mem i j h a.toAdd⟩
  map_one' := by
    apply Subtype.ext
    exact elementaryUnit_zero i j h
  map_mul' a b := by
    apply Subtype.ext
    exact (elementaryUnit_mul i j h a.toAdd b.toAdd).symm
theorem cylinder_transposition_factorization [CharP R 2] (P Q : R)
    (hPP : P * P = 0) (hPQP : P * Q * P = P) :
    (1 + P) * (1 + Q) * (1 + P) =
      1 - P * Q - Q * P + P + Q := by
  simp only [CharTwo.sub_eq_add]
  have hthree : (3 : ℤ) • P = P := by
    rw [zsmul_eq_mul, CharTwo.intCast_eq_mod]
    norm_num
  noncomm_ring [hPP, hPQP]
  simp only [hthree]
theorem elementaryUnit_commutator (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅elementaryUnit i j hij a, elementaryUnit j k hjk b⁆ =
      elementaryUnit i k hik (a * b) := by
  apply Units.ext
  change
    (1 + Matrix.single i j a) * (1 + Matrix.single j k b) *
      (1 - Matrix.single i j a) * (1 - Matrix.single j k b) =
      1 + Matrix.single i k (a * b)
  have hxx := single_mul_self_eq_zero i j hij a
  have hyy := single_mul_self_eq_zero j k hjk b
  have hyx : Matrix.single j k b * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := b) j k i hik.symm a
  have hxy : Matrix.single i j a * Matrix.single j k b =
      Matrix.single i k (a * b) :=
    Matrix.single_mul_single_same (c := a) i j k b
  have hzx : Matrix.single i k (a * b) * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := a * b) i k i hik.symm a
  have hzy : Matrix.single i k (a * b) * Matrix.single j k b = 0 :=
    Matrix.single_mul_single_of_ne (c := a * b) i k j hjk.symm b
  have hzz := single_mul_self_eq_zero i k hik (a * b)
  noncomm_ring [hxx, hyy, hyx, hxy, hzx, hzy, hzz]
theorem elementaryUnit_mem_of_two_step
    (H : Subgroup (Matrix ι ι R)ˣ) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : R)
    (hleft : elementaryUnit i j hij a ∈ H)
    (hright : elementaryUnit j k hjk 1 ∈ H) :
    elementaryUnit i k hik a ∈ H := by
  have hc : ⁅elementaryUnit i j hij a, elementaryUnit j k hjk 1⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hleft hright) (H.inv_mem hleft))
      (H.inv_mem hright)
  rw [elementaryUnit_commutator i j k hij hjk hik a 1] at hc
  simpa using hc
end NoncommutativeElementaryGroup
section FiniteGeneration
variable {R : Type*} [Ring R]
noncomputable def finiteElementaryGenerators [DecidableEq R]
    (n : ℕ) (s : Finset R) : Finset (Matrix (Fin n) (Fin n) R)ˣ :=
  Finset.univ.biUnion (fun i : Fin n =>
    Finset.univ.biUnion (fun j : Fin n =>
      if h : i ≠ j then (insert 1 s).image (elementaryUnit i j h) else ∅))
variable [Algebra (ZMod 2) R]
def elementaryCoefficientSubalgebra (n : ℕ) (hn : 2 < n)
    (H : Subgroup (Matrix (Fin n) (Fin n) R)ˣ)
    (hunit : ∀ (i j : Fin n) (h : i ≠ j), elementaryUnit i j h (1 : R) ∈ H) :
    Subalgebra (ZMod 2) R where
  carrier :=
    {a | ∀ (i j : Fin n) (h : i ≠ j), elementaryUnit i j h a ∈ H}
  add_mem' := by
    intro a b ha hb i j hij
    rw [← elementaryUnit_mul]
    exact H.mul_mem (ha i j hij) (hb i j hij)
  mul_mem' := by
    intro a b ha hb i j hij
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
    have hik : i ≠ k := hki.symm
    have hleft := ha i k hik
    have hright := hb k j hkj
    have hc : ⁅elementaryUnit i k hik a, elementaryUnit k j hkj b⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem
        (H.mul_mem (H.mul_mem hleft hright) (H.inv_mem hleft))
        (H.inv_mem hright)
    rw [elementaryUnit_commutator i k j hik hkj hij a b] at hc
    exact hc
  algebraMap_mem' := by
    intro z
    have hz : z = 0 ∨ z = 1 := by
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hz with rfl | rfl
    · intro i j hij
      simpa only [map_zero, elementaryUnit_zero] using H.one_mem
    · intro i j hij
      simpa only [map_one] using hunit i j hij
end FiniteGeneration
abbrev binaryLeavittElementaryGroup (n : ℕ) : Type :=
  elementaryGroup (Fin n) BinaryLeavitt
def completePrefixMatrixEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1) :
    Matrix ι ι BinaryLeavitt ≃+* BinaryLeavitt where
  toFun := MatrixCorner.encode
    (fun i => leavittWordS (E.word i))
    (fun i => leavittWordT (E.word i))
  invFun := MatrixCorner.decode
    (fun i => leavittWordS (E.word i))
    (fun i => leavittWordT (E.word i))
  left_inv := MatrixCorner.decode_encode _ _ (binaryPrefixCode_orthogonal E)
  right_inv x := by
    rw [MatrixCorner.encode_decode, hcomplete]
    simp
  map_mul' := MatrixCorner.encode_mul _ _ (binaryPrefixCode_orthogonal E)
  map_add' M N := by
    simp [MatrixCorner.encode, Matrix.add_apply, mul_add, add_mul,
      Finset.sum_add_distrib]
def completePrefixUnitEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1) :
    (Matrix ι ι BinaryLeavitt)ˣ ≃* BinaryLeavittˣ :=
  Units.mapEquiv (completePrefixMatrixEquiv E hcomplete).toMulEquiv
theorem completePrefixUnitEquiv_elementaryUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1)
    (i j : ι) (hij : i ≠ j) (a : BinaryLeavitt) :
    completePrefixUnitEquiv E hcomplete (elementaryUnit i j hij a) =
      prefixElementaryUnit E i j hij a := by
  apply Units.ext
  change
    MatrixCorner.encode
      (fun k => leavittWordS (E.word k))
      (fun k => leavittWordT (E.word k))
      (1 + Matrix.single i j a) =
        1 + leavittWordS (E.word i) * a * leavittWordT (E.word j)
  have h₁ :
      MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (1 : Matrix ι ι BinaryLeavitt) = 1 := by
    rw [MatrixCorner.encode_one, hcomplete]
  calc
    MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (1 + Matrix.single i j a) =
      MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (1 : Matrix ι ι BinaryLeavitt) +
      MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (Matrix.single i j a) := by
          simp [MatrixCorner.encode, Matrix.add_apply, mul_add, add_mul,
            Finset.sum_add_distrib]
    _ = 1 + leavittWordS (E.word i) * a * leavittWordT (E.word j) := by
      rw [h₁]
      simp [MatrixCorner.encode, Matrix.single_apply, mul_ite, ite_mul, ite_and]
theorem completePrefixElementaryGroup_map
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1) :
    (elementaryGroup ι BinaryLeavitt).map
        (completePrefixUnitEquiv E hcomplete).toMonoidHom =
      prefixElementaryGroup E := by
  unfold elementaryGroup prefixElementaryGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, j, hij, a, rfl⟩, hz⟩
    exact ⟨i, j, hij, a,
      (completePrefixUnitEquiv_elementaryUnit E hcomplete i j hij a).symm.trans hz⟩
  · rintro ⟨i, j, hij, a, rfl⟩
    exact ⟨elementaryUnit i j hij a, ⟨i, j, hij, a, rfl⟩,
      completePrefixUnitEquiv_elementaryUnit E hcomplete i j hij a⟩
def ninePrefixElementaryGroupEquiv :
    binaryLeavittElementaryGroup 9 ≃* prefixElementaryGroup ninePrefixCode :=
  ((completePrefixUnitEquiv ninePrefixCode ninePrefixCode_complete).subgroupMap
      (elementaryGroup (Fin 9) BinaryLeavitt)).trans
    (MulEquiv.subgroupCongr
      (completePrefixElementaryGroup_map ninePrefixCode ninePrefixCode_complete))
def idempotentCornerUnitExtension {A : Type*} [Ring A]
    {e : A} (he : IsIdempotentElem e) : he.Cornerˣ →* Aˣ where
  toFun u :=
    { val := u.val.val + (1 - e)
      inv := u.inv.val + (1 - e)
      val_inv := by
        have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
        have hv := (Subsemigroup.mem_corner_iff he).mp u.inv.property
        have huv : u.val.val * u.inv.val = e := by
          have h := congrArg (fun z : he.Corner => z.val) u.val_inv
          exact h
        noncomm_ring [he.eq, hu.1, hu.2, hv.1, hv.2, huv]
      inv_val := by
        have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
        have hv := (Subsemigroup.mem_corner_iff he).mp u.inv.property
        have hvu : u.inv.val * u.val.val = e := by
          have h := congrArg (fun z : he.Corner => z.val) u.inv_val
          exact h
        noncomm_ring [he.eq, hu.1, hu.2, hv.1, hv.2, hvu] }
  map_one' := by
    apply Units.ext
    change e + (1 - e) = 1
    noncomm_ring
  map_mul' u v := by
    apply Units.ext
    have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
    have hv := (Subsemigroup.mem_corner_iff he).mp v.val.property
    change
      u.val.val * v.val.val + (1 - e) =
        (u.val.val + (1 - e)) * (v.val.val + (1 - e))
    noncomm_ring [he.eq, hu.1, hu.2, hv.1, hv.2]
theorem idempotentCornerUnitExtension_injective
    {A : Type*} [Ring A] {e : A} (he : IsIdempotentElem e) :
    Function.Injective (idempotentCornerUnitExtension he) := by
  intro u v huv
  apply Units.ext
  apply Subtype.ext
  have h := congrArg (fun z : Aˣ => (z : A)) huv
  change u.val.val + (1 - e) = v.val.val + (1 - e) at h
  exact add_right_cancel h
def prefixCornerUnitHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    (Matrix ι ι BinaryLeavitt)ˣ →* BinaryLeavittˣ :=
  (idempotentCornerUnitExtension
    (MatrixCorner.codeIdempotent_isIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i))
      (binaryPrefixCode_orthogonal E))).comp
    (Units.mapEquiv (binaryPrefixCornerEquiv E).toMulEquiv).toMonoidHom
theorem prefixCornerUnitHom_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    Function.Injective (prefixCornerUnitHom E) := by
  exact (idempotentCornerUnitExtension_injective
    (MatrixCorner.codeIdempotent_isIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i))
      (binaryPrefixCode_orthogonal E))).comp
    (Units.mapEquiv (binaryPrefixCornerEquiv E).toMulEquiv).injective
theorem prefixCornerUnitHom_elementaryUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a : BinaryLeavitt) :
    prefixCornerUnitHom E (elementaryUnit i j hij a) =
      prefixElementaryUnit E i j hij a := by
  apply Units.ext
  change
    MatrixCorner.encode
      (fun k => leavittWordS (E.word k))
      (fun k => leavittWordT (E.word k))
      (1 + Matrix.single i j a) +
      (1 - MatrixCorner.codeIdempotent
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))) =
      1 + leavittWordS (E.word i) * a * leavittWordT (E.word j)
  have henc :
      MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (1 + Matrix.single i j a) =
      MatrixCorner.codeIdempotent
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k)) +
        leavittWordS (E.word i) * a * leavittWordT (E.word j) := by
    calc
      MatrixCorner.encode
          (fun k => leavittWordS (E.word k))
          (fun k => leavittWordT (E.word k))
          (1 + Matrix.single i j a) =
        MatrixCorner.encode
          (fun k => leavittWordS (E.word k))
          (fun k => leavittWordT (E.word k))
          (1 : Matrix ι ι BinaryLeavitt) +
        MatrixCorner.encode
          (fun k => leavittWordS (E.word k))
          (fun k => leavittWordT (E.word k))
          (Matrix.single i j a) := by
            simp [MatrixCorner.encode, Matrix.add_apply, mul_add, add_mul,
              Finset.sum_add_distrib]
      _ = MatrixCorner.codeIdempotent
          (fun k => leavittWordS (E.word k))
          (fun k => leavittWordT (E.word k)) +
          leavittWordS (E.word i) * a * leavittWordT (E.word j) := by
            rw [MatrixCorner.encode_one]
            simp [MatrixCorner.encode, Matrix.single_apply,
              mul_ite, ite_mul, ite_and]
  rw [henc]
  noncomm_ring
theorem prefixCornerElementaryGroup_map
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    (elementaryGroup ι BinaryLeavitt).map (prefixCornerUnitHom E) =
      prefixElementaryGroup E := by
  unfold elementaryGroup prefixElementaryGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, j, hij, a, rfl⟩, hz⟩
    exact ⟨i, j, hij, a,
      (prefixCornerUnitHom_elementaryUnit E i j hij a).symm.trans hz⟩
  · rintro ⟨i, j, hij, a, rfl⟩
    exact ⟨elementaryUnit i j hij a, ⟨i, j, hij, a, rfl⟩,
      prefixCornerUnitHom_elementaryUnit E i j hij a⟩
def alphaPrefixElementaryGroupEquiv :
    binaryLeavittElementaryGroup 3 ≃* prefixElementaryGroup alphaPrefixCode :=
  ((elementaryGroup (Fin 3) BinaryLeavitt).equivMapOfInjective
      (prefixCornerUnitHom alphaPrefixCode)
      (prefixCornerUnitHom_injective alphaPrefixCode)).trans
    (MulEquiv.subgroupCongr
      (prefixCornerElementaryGroup_map alphaPrefixCode))
namespace SourceGeneration
open scoped commutatorElement
def sourceGeneratedGroup : Subgroup BinaryLeavittˣ :=
  Subgroup.closure
    ((prefixElementaryGroup alphaPrefixCode : Set BinaryLeavittˣ) ∪
      {compressionU, compressionV})
def betaNineIndex (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val + 1, by omega⟩
def nuNineIndex (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val + 2, by omega⟩
@[simp] theorem nineWord_betaNineIndex (i : Fin 3) :
    nineWord (betaNineIndex i) = betaWord i := by
  fin_cases i <;> rfl
@[simp] theorem nineWord_nuNineIndex (i : Fin 3) :
    nineWord (nuNineIndex i) = nuWord i := by
  fin_cases i <;> rfl
@[simp] theorem uWord_betaNineIndex (i : Fin 3) :
    uWord (betaNineIndex i) = alphaWord i ++ [1] := by
  fin_cases i <;> rfl
@[simp] theorem vWord_nuNineIndex (i : Fin 3) :
    vWord (nuNineIndex i) = alphaWord i ++ [1] := by
  fin_cases i <;> rfl
def alphaBetaNineIndex (p : Fin 2) (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val + p.val, by omega⟩
theorem alphaBetaNineIndex_ne {i j : Fin 3} (hij : i ≠ j)
    (p q : Fin 2) : alphaBetaNineIndex p i ≠ alphaBetaNineIndex q j := by
  intro h
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 3 * i.val + p.val = 3 * j.val + q.val at hv
  omega
@[simp] theorem nineWord_alphaBetaNineIndex (p : Fin 2) (i : Fin 3) :
    nineWord (alphaBetaNineIndex p i) =
      if p = 0 then alphaWord i else betaWord i := by
  fin_cases p <;> fin_cases i <;> rfl
def prefixElementaryEntry {ι : Type*} (E : BinaryPrefixCode ι)
    (i j : ι) (a : BinaryLeavitt) : BinaryLeavitt :=
  leavittWordS (E.word i) * a * leavittWordT (E.word j)
def alphaNuNineIndex (p : Fin 2) (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val + 2 * p.val, by omega⟩
theorem alphaNuNineIndex_ne {i j : Fin 3} (hij : i ≠ j)
    (p q : Fin 2) : alphaNuNineIndex p i ≠ alphaNuNineIndex q j := by
  intro h
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 3 * i.val + 2 * p.val = 3 * j.val + 2 * q.val at hv
  omega
@[simp] theorem nineWord_alphaNuNineIndex (p : Fin 2) (i : Fin 3) :
    nineWord (alphaNuNineIndex p i) =
      if p = 0 then alphaWord i else nuWord i := by
  fin_cases p <;> fin_cases i <;> rfl
theorem alphaNineIndex_ne {i j : Fin 3} (hij : i ≠ j) :
    alphaNineIndex i ≠ alphaNineIndex j := by
  intro h
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 3 * i.val = 3 * j.val at hv
  omega
theorem alphaPrefixElementaryUnit_eq_nine
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    prefixElementaryUnit alphaPrefixCode i j hij a =
      prefixElementaryUnit ninePrefixCode
        (alphaNineIndex i) (alphaNineIndex j)
        (alphaNineIndex_ne hij) a := by
  apply Units.ext
  change
    1 + leavittWordS (alphaWord i) * a * leavittWordT (alphaWord j) =
      1 + leavittWordS (nineWord (alphaNineIndex i)) * a *
        leavittWordT (nineWord (alphaNineIndex j))
  rw [nineWord_alphaNineIndex, nineWord_alphaNineIndex]
theorem alphaPrefixElementaryGroup_le_nine :
    prefixElementaryGroup alphaPrefixCode ≤
      prefixElementaryGroup ninePrefixCode := by
  rw [prefixElementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  rw [alphaPrefixElementaryUnit_eq_nine]
  exact Subgroup.subset_closure
    ⟨alphaNineIndex i, alphaNineIndex j, alphaNineIndex_ne hij, a, rfl⟩
end SourceGeneration
theorem binaryLeavittMatrixUnitSubgroup_countable (n : ℕ)
    (H : Subgroup (Matrix (Fin n) (Fin n) BinaryLeavitt)ˣ) : Countable H := by
  letI : Countable (Matrix (Fin n) (Fin n) BinaryLeavitt) :=
    Countable.of_equiv (Fin n → Fin n → BinaryLeavitt)
      (Matrix.of : (Fin n → Fin n → BinaryLeavitt) ≃
        Matrix (Fin n) (Fin n) BinaryLeavitt)
  have h : Function.Injective
      (fun x : H => (x.val.val : Matrix (Fin n) (Fin n) BinaryLeavitt)) := by
    intro x y hxy
    apply Subtype.ext
    exact Units.ext hxy
  exact h.countable
instance binaryLeavittElementaryGroupCountable (n : ℕ) :
    Countable (binaryLeavittElementaryGroup n) :=
  binaryLeavittMatrixUnitSubgroup_countable n
    (elementaryGroup (Fin n) BinaryLeavitt)
noncomputable def midrankFirstMoment (a : ℝ) : List ℝ → ℝ
  | [] => 0
  | p :: ps => p * (a + p / 2) + midrankFirstMoment (a + p) ps
noncomputable def midrankSecondMoment (a : ℝ) : List ℝ → ℝ
  | [] => 0
  | p :: ps => p * (a + p / 2) ^ 2 + midrankSecondMoment (a + p) ps
noncomputable def midrankVariance (ps : List ℝ) : ℝ :=
  midrankSecondMoment 0 ps - (midrankFirstMoment 0 ps) ^ 2
def componentRankMass {V : Type*}
    (C : Finset V) (b : V → ℤ) (j : ℤ) : ℝ :=
  ((C.filter fun x => b x = j).card : ℝ) / (C.card : ℝ)
def componentVertexMidrank {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) : ℝ :=
  (((C.filter fun z => b z < b x).card : ℝ) +
      ((C.filter fun z => b z = b x).card : ℝ) / 2) /
    (C.card : ℝ)
def componentRankMassList {V : Type*}
    (C : Finset V) (b : V → ℤ) : List ℝ :=
  ((C.image b).sort (· ≤ ·)).map (componentRankMass C b)
theorem exists_maximum_overlap_component
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V)
    (hC : C.Nonempty) (hCU : C ⊆ U) :
    ∃ D ∈ Q.parts,
      ∀ E ∈ Q.parts, (C ∩ E).card ≤ (C ∩ D).card := by
  classical
  have hU : U.Nonempty := hC.mono hCU
  exact Finset.exists_max_image Q.parts
    (fun D : Finset V => (C ∩ D).card)
    (Q.parts_nonempty hU.ne_empty)
noncomputable def maximumOverlapPart
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V) : Finset V := by
  classical
  exact if h : C.Nonempty ∧ C ⊆ U then
    (exists_maximum_overlap_component Q C h.1 h.2).choose else ∅
namespace PrefixCompressionU
open scoped BigOperators
def sourceCrossRoot (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) : BinaryLeavittˣ :=
  prefixElementaryUnit ninePrefixCode i j h
    (leavittWordS a * leavittWordT b)
theorem sourceCrossRoot_mem (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    sourceCrossRoot i j h a b ∈ prefixElementaryGroup ninePrefixCode :=
  Subgroup.subset_closure ⟨i, j, h,
    leavittWordS a * leavittWordT b, rfl⟩
@[simp] theorem sourceCrossRoot_val (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    (↑(sourceCrossRoot i j h a b) : BinaryLeavitt) =
      1 + leavittWordS (nineWord i ++ a) *
        leavittWordT (nineWord j ++ b) := by
  change
    1 + leavittWordS (nineWord i) *
      (leavittWordS a * leavittWordT b) * leavittWordT (nineWord j) = _
  rw [leavittWordS_append, leavittWordT_append]
  noncomm_ring
def sourceCrossSwap (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) : BinaryLeavittˣ :=
  sourceCrossRoot i j h a b *
    sourceCrossRoot j i h.symm b a *
    sourceCrossRoot i j h a b
theorem sourceCrossSwap_mem (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    sourceCrossSwap i j h a b ∈ prefixElementaryGroup ninePrefixCode := by
  exact (prefixElementaryGroup ninePrefixCode).mul_mem
    ((prefixElementaryGroup ninePrefixCode).mul_mem
      (sourceCrossRoot_mem i j h a b)
      (sourceCrossRoot_mem j i h.symm b a))
    (sourceCrossRoot_mem i j h a b)
theorem sourceRefinementOrthogonal (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    leavittWordT (nineWord i ++ a) *
      leavittWordS (nineWord j ++ b) = 0 := by
  have hz : leavittWordT (nineWord i) * leavittWordS (nineWord j) = 0 := by
    simpa [ninePrefixCode, h] using
      binaryPrefixCode_orthogonal ninePrefixCode i j
  rw [leavittWordT_append, leavittWordS_append]
  calc
    (leavittWordT a * leavittWordT (nineWord i)) *
        (leavittWordS (nineWord j) * leavittWordS b) =
      leavittWordT a *
        (leavittWordT (nineWord i) * leavittWordS (nineWord j)) *
        leavittWordS b := by noncomm_ring
    _ = 0 := by rw [hz]; simp
theorem sourceCrossSwap_val (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    (↑(sourceCrossSwap i j h a b) : BinaryLeavitt) =
      1 - leavittWordS (nineWord i ++ a) *
          leavittWordT (nineWord i ++ a) -
        leavittWordS (nineWord j ++ b) *
          leavittWordT (nineWord j ++ b) +
        leavittWordS (nineWord i ++ a) *
          leavittWordT (nineWord j ++ b) +
        leavittWordS (nineWord j ++ b) *
          leavittWordT (nineWord i ++ a) := by
  let A : List (Fin 2) := nineWord i ++ a
  let B : List (Fin 2) := nineWord j ++ b
  let P : BinaryLeavitt := leavittWordS A * leavittWordT B
  let Q : BinaryLeavitt := leavittWordS B * leavittWordT A
  have hba : leavittWordT B * leavittWordS A = 0 :=
    sourceRefinementOrthogonal j i h.symm b a
  have hPP : P * P = 0 := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS A * leavittWordT B) = 0
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS A) * leavittWordT B := by
            noncomm_ring
      _ = 0 := by rw [hba]; simp
  have hPQ : P * Q = leavittWordS A * leavittWordT A := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS B * leavittWordT A) =
        leavittWordS A * leavittWordT A
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) * leavittWordT A := by
            noncomm_ring
      _ = leavittWordS A * leavittWordT A := by
        rw [leavittWordT_mul_wordS_self]
        simp
  have hQP : Q * P = leavittWordS B * leavittWordT B := by
    change
      (leavittWordS B * leavittWordT A) *
        (leavittWordS A * leavittWordT B) =
        leavittWordS B * leavittWordT B
    calc
      (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS B *
          (leavittWordT A * leavittWordS A) * leavittWordT B := by
            noncomm_ring
      _ = leavittWordS B * leavittWordT B := by
        rw [leavittWordT_mul_wordS_self]
        simp
  have hPQP : P * Q * P = P := by
    rw [hPQ]
    change
      (leavittWordS A * leavittWordT A) *
        (leavittWordS A * leavittWordT B) =
        leavittWordS A * leavittWordT B
    calc
      (leavittWordS A * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT A * leavittWordS A) * leavittWordT B := by
            noncomm_ring
      _ = leavittWordS A * leavittWordT B := by
        rw [leavittWordT_mul_wordS_self]
        simp
  change
    (↑(sourceCrossSwap i j h a b) : BinaryLeavitt) =
      1 - leavittWordS A * leavittWordT A -
        leavittWordS B * leavittWordT B + P + Q
  calc
    (↑(sourceCrossSwap i j h a b) : BinaryLeavitt) =
        (1 + P) * (1 + Q) * (1 + P) := by
          simp only [sourceCrossSwap, Units.val_mul, sourceCrossRoot_val]
          rfl
    _ = 1 - P * Q - Q * P + P + Q :=
      cylinder_transposition_factorization P Q hPP hPQP
    _ = 1 - leavittWordS A * leavittWordT A -
        leavittWordS B * leavittWordT B + P + Q := by rw [hPQ, hQP]
def refinedSourceWord : Fin 19 → List (Fin 2)
  | 0 => [0, 0, 0, 0]
  | 1 => [0, 0, 0, 1]
  | 2 => [1, 0, 0, 0, 0]
  | 3 => [1, 0, 0, 0, 1]
  | 4 => [1, 1, 0, 0, 0]
  | 5 => [1, 1, 0, 0, 1]
  | 6 => [0, 0, 1]
  | 7 => [1, 0, 0, 1, 0]
  | 8 => [1, 0, 0, 1, 1]
  | 9 => [1, 1, 0, 1]
  | 10 => [0, 1, 0, 0]
  | 11 => [0, 1, 0, 1]
  | 12 => [0, 1, 1]
  | 13 => [1, 0, 1, 0, 0]
  | 14 => [1, 0, 1, 0, 1]
  | 15 => [1, 0, 1, 1]
  | 16 => [1, 1, 1, 0, 0]
  | 17 => [1, 1, 1, 0, 1]
  | _ => [1, 1, 1, 1]
def refinedSourcePrefixCode : BinaryPrefixCode (Fin 19) where
  word := refinedSourceWord
  prefix_free := by decide
theorem refinedSourcePrefixCode_complete :
    MatrixCorner.codeIdempotent
      (fun i => leavittWordS (refinedSourcePrefixCode.word i))
      (fun i => leavittWordT (refinedSourcePrefixCode.word i)) = 1 := by
  have h000 :
      leavittCylinder [0, 0, 0, 0] +
          leavittCylinder [0, 0, 0, 1] =
        leavittCylinder [0, 0, 0] := by
    simpa using (leavittCylinder_split [0, 0, 0]).symm
  have h1000 :
      leavittCylinder [1, 0, 0, 0, 0] +
          leavittCylinder [1, 0, 0, 0, 1] =
        leavittCylinder [1, 0, 0, 0] := by
    simpa using (leavittCylinder_split [1, 0, 0, 0]).symm
  have h1100 :
      leavittCylinder [1, 1, 0, 0, 0] +
          leavittCylinder [1, 1, 0, 0, 1] =
        leavittCylinder [1, 1, 0, 0] := by
    simpa using (leavittCylinder_split [1, 1, 0, 0]).symm
  have h1001 :
      leavittCylinder [1, 0, 0, 1, 0] +
          leavittCylinder [1, 0, 0, 1, 1] =
        leavittCylinder [1, 0, 0, 1] := by
    simpa using (leavittCylinder_split [1, 0, 0, 1]).symm
  have h010 :
      leavittCylinder [0, 1, 0, 0] +
          leavittCylinder [0, 1, 0, 1] =
        leavittCylinder [0, 1, 0] := by
    simpa using (leavittCylinder_split [0, 1, 0]).symm
  have h01 :
      leavittCylinder [0, 1, 0] +
          leavittCylinder [0, 1, 1] =
        leavittCylinder [0, 1] := by
    simpa using (leavittCylinder_split [0, 1]).symm
  have h1010 :
      leavittCylinder [1, 0, 1, 0, 0] +
          leavittCylinder [1, 0, 1, 0, 1] =
        leavittCylinder [1, 0, 1, 0] := by
    simpa using (leavittCylinder_split [1, 0, 1, 0]).symm
  have h101 :
      leavittCylinder [1, 0, 1, 0] +
          leavittCylinder [1, 0, 1, 1] =
        leavittCylinder [1, 0, 1] := by
    simpa using (leavittCylinder_split [1, 0, 1]).symm
  have h1110 :
      leavittCylinder [1, 1, 1, 0, 0] +
          leavittCylinder [1, 1, 1, 0, 1] =
        leavittCylinder [1, 1, 1, 0] := by
    simpa using (leavittCylinder_split [1, 1, 1, 0]).symm
  have h111 :
      leavittCylinder [1, 1, 1, 0] +
          leavittCylinder [1, 1, 1, 1] =
        leavittCylinder [1, 1, 1] := by
    simpa using (leavittCylinder_split [1, 1, 1]).symm
  change (∑ i : Fin 19, leavittCylinder (refinedSourceWord i)) = 1
  calc
    (∑ i : Fin 19, leavittCylinder (refinedSourceWord i)) =
        (leavittCylinder [0, 0, 0, 0] +
          leavittCylinder [0, 0, 0, 1]) +
        (leavittCylinder [1, 0, 0, 0, 0] +
          leavittCylinder [1, 0, 0, 0, 1]) +
        (leavittCylinder [1, 1, 0, 0, 0] +
          leavittCylinder [1, 1, 0, 0, 1]) +
        leavittCylinder [0, 0, 1] +
        (leavittCylinder [1, 0, 0, 1, 0] +
          leavittCylinder [1, 0, 0, 1, 1]) +
        leavittCylinder [1, 1, 0, 1] +
        ((leavittCylinder [0, 1, 0, 0] +
            leavittCylinder [0, 1, 0, 1]) +
          leavittCylinder [0, 1, 1]) +
        ((leavittCylinder [1, 0, 1, 0, 0] +
            leavittCylinder [1, 0, 1, 0, 1]) +
          leavittCylinder [1, 0, 1, 1]) +
        ((leavittCylinder [1, 1, 1, 0, 0] +
            leavittCylinder [1, 1, 1, 0, 1]) +
          leavittCylinder [1, 1, 1, 1]) := by
            simp [Fin.sum_univ_succ, refinedSourceWord]
            ac_rfl
    _ = leavittCylinder [0, 0, 0] +
          leavittCylinder [1, 0, 0, 0] +
          leavittCylinder [1, 1, 0, 0] +
          leavittCylinder [0, 0, 1] +
          leavittCylinder [1, 0, 0, 1] +
          leavittCylinder [1, 1, 0, 1] +
          leavittCylinder [0, 1] +
          leavittCylinder [1, 0, 1] +
          leavittCylinder [1, 1, 1] := by
            rw [h000, h1000, h1100, h1001, h010, h01,
              h1010, h101, h1110, h111]
    _ = ∑ i : Fin 9, leavittCylinder (nineWord i) := by
      simp [Fin.sum_univ_succ, nineWord, alphaWord, betaWord, nuWord]
      ac_rfl
    _ = 1 := ninePrefixCode_complete
theorem completePrefixWord_ext {ι : Type*} [Fintype ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1)
    (x y : BinaryLeavitt)
    (haction : ∀ i : ι,
      x * leavittWordS (E.word i) =
        y * leavittWordS (E.word i)) :
    x = y := by
  calc
    x = x * 1 := (mul_one x).symm
    _ = x * MatrixCorner.codeIdempotent
        (fun i => leavittWordS (E.word i))
        (fun i => leavittWordT (E.word i)) := by rw [hcomplete]
    _ = ∑ i : ι,
        (x * leavittWordS (E.word i)) *
          leavittWordT (E.word i) := by
      rw [MatrixCorner.codeIdempotent, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (mul_assoc x _ _).symm
    _ = ∑ i : ι,
        (y * leavittWordS (E.word i)) *
          leavittWordT (E.word i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [haction i]
    _ = y * MatrixCorner.codeIdempotent
        (fun i => leavittWordS (E.word i))
        (fun i => leavittWordT (E.word i)) := by
      rw [MatrixCorner.codeIdempotent, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_assoc y _ _
    _ = y := by rw [hcomplete, mul_one]
theorem prefixTable_mul_sourceWord {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (source target : BinaryPrefixCode ι) (i : ι) :
    prefixTable source target * leavittWordS (source.word i) =
      leavittWordS (target.word i) := by
  classical
  simp [prefixTable, Finset.sum_mul, mul_assoc,
    binaryPrefixCode_orthogonal]
theorem compressionU_mul_nine_refinement
    (i : Fin 9) (r : List (Fin 2)) :
    (compressionU : BinaryLeavitt) *
        leavittWordS (nineWord i ++ r) =
      leavittWordS (uWord i ++ r) := by
  rw [leavittWordS_append, leavittWordS_append]
  change
    prefixTable ninePrefixCode uPrefixCode *
        (leavittWordS (ninePrefixCode.word i) * leavittWordS r) =
      leavittWordS (uPrefixCode.word i) * leavittWordS r
  rw [← mul_assoc, prefixTable_mul_sourceWord]
def refinedSourceParent : Fin 19 → Fin 9
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 4
  | 8 => 4
  | 9 => 5
  | 10 => 6
  | 11 => 6
  | 12 => 6
  | 13 => 7
  | 14 => 7
  | 15 => 7
  | 16 => 8
  | 17 => 8
  | _ => 8
def refinedSourceSuffix : Fin 19 → List (Fin 2)
  | 0 => [0]
  | 1 => [1]
  | 2 => [0]
  | 3 => [1]
  | 4 => [0]
  | 5 => [1]
  | 6 => []
  | 7 => [0]
  | 8 => [1]
  | 9 => []
  | 10 => [0, 0]
  | 11 => [0, 1]
  | 12 => [1]
  | 13 => [0, 0]
  | 14 => [0, 1]
  | 15 => [1]
  | 16 => [0, 0]
  | 17 => [0, 1]
  | _ => [1]
def refinedTargetWord (i : Fin 19) : List (Fin 2) :=
  uWord (refinedSourceParent i) ++ refinedSourceSuffix i
theorem refinedSourceWord_eq_parent_append (i : Fin 19) :
    refinedSourceWord i =
      nineWord (refinedSourceParent i) ++ refinedSourceSuffix i := by
  fin_cases i <;> decide
theorem compressionU_mul_refinedSourceWord (i : Fin 19) :
    (compressionU : BinaryLeavitt) *
        leavittWordS (refinedSourceWord i) =
      leavittWordS (refinedTargetWord i) := by
  rw [refinedSourceWord_eq_parent_append]
  exact compressionU_mul_nine_refinement
    (refinedSourceParent i) (refinedSourceSuffix i)
def binaryWordCancellation (a b : List (Fin 2)) : BinaryLeavitt :=
  match a, b with
  | [], b => leavittWordS b
  | a, [] => leavittWordT a
  | i :: a, j :: b =>
      if i = j then binaryWordCancellation a b else 0
theorem leavittWordT_mul_wordS_cancel (a b : List (Fin 2)) :
    leavittWordT a * leavittWordS b =
      binaryWordCancellation a b := by
  induction a generalizing b with
  | nil => simp [binaryWordCancellation, leavittWordT]
  | cons i a ih =>
      cases b with
      | nil => simp [binaryWordCancellation, leavittWordS]
      | cons j b =>
          by_cases hij : i = j
          · subst j
            change
              (leavittWordT a * leavittT i) *
                  (leavittS i * leavittWordS b) =
                if i = i then binaryWordCancellation a b else 0
            rw [if_pos rfl]
            calc
              (leavittWordT a * leavittT i) *
                  (leavittS i * leavittWordS b) =
                leavittWordT a *
                  ((leavittT i * leavittS i) * leavittWordS b) := by
                    noncomm_ring
              _ = binaryWordCancellation a b := by
                rw [leavittT_mul_S]
                simpa using ih b
          · change
              (leavittWordT a * leavittT i) *
                  (leavittS j * leavittWordS b) =
                if i = j then binaryWordCancellation a b else 0
            rw [if_neg hij]
            calc
              (leavittWordT a * leavittT i) *
                  (leavittS j * leavittWordS b) =
                leavittWordT a *
                  ((leavittT i * leavittS j) * leavittWordS b) := by
                    noncomm_ring
              _ = 0 := by rw [leavittT_mul_S]; simp [hij]
theorem leavittWordS_mul_wordS (a b : List (Fin 2)) :
    leavittWordS a * leavittWordS b = leavittWordS (a ++ b) :=
  (leavittWordS_append a b).symm
theorem sourceCrossSwap_mul_leavittWordS
    (i j : Fin 9) (h : i ≠ j)
    (a b x : List (Fin 2)) :
    (↑(sourceCrossSwap i j h a b) : BinaryLeavitt) * leavittWordS x =
      leavittWordS x -
        leavittWordS (nineWord i ++ a) *
          binaryWordCancellation (nineWord i ++ a) x -
        leavittWordS (nineWord j ++ b) *
          binaryWordCancellation (nineWord j ++ b) x +
        leavittWordS (nineWord i ++ a) *
          binaryWordCancellation (nineWord j ++ b) x +
        leavittWordS (nineWord j ++ b) *
          binaryWordCancellation (nineWord i ++ a) x := by
  rw [sourceCrossSwap_val]
  simp only [sub_mul, add_mul, one_mul, mul_assoc,
    leavittWordT_mul_wordS_cancel]
def sourceUChronologicalSwaps : List BinaryLeavittˣ :=
  [sourceCrossSwap 0 1 (by decide) [0] [],
   sourceCrossSwap 0 4 (by decide) [1] [],
   sourceCrossSwap 3 7 (by decide) [] [],
   sourceCrossSwap 6 2 (by decide) [0, 0] [],
   sourceCrossSwap 6 5 (by decide) [0, 1] [],
   sourceCrossSwap 6 8 (by decide) [1] [],
   sourceCrossSwap 3 6 (by decide) [] [0],
   sourceCrossSwap 1 0 (by decide) [] [0, 0],
   sourceCrossSwap 4 0 (by decide) [] [0, 1],
   sourceCrossSwap 1 0 (by decide) [] [1, 0],
   sourceCrossSwap 4 0 (by decide) [] [1, 1],
   sourceCrossSwap 3 1 (by decide) [0, 0] [],
   sourceCrossSwap 3 4 (by decide) [0, 1] [],
   sourceCrossSwap 7 3 (by decide) [] [0],
   sourceCrossSwap 7 3 (by decide) [] [1],
   sourceCrossSwap 2 6 (by decide) [] [0, 0, 0],
   sourceCrossSwap 5 6 (by decide) [] [0, 0, 1],
   sourceCrossSwap 8 6 (by decide) [] [0, 1],
   sourceCrossSwap 2 6 (by decide) [] [1, 0, 0],
   sourceCrossSwap 5 6 (by decide) [] [1, 0, 1],
   sourceCrossSwap 8 6 (by decide) [] [1, 1]]
def elementaryCompressionU : BinaryLeavittˣ :=
  sourceUChronologicalSwaps.reverse.prod
theorem elementaryCompressionU_mem :
    elementaryCompressionU ∈ prefixElementaryGroup ninePrefixCode := by
  apply (prefixElementaryGroup ninePrefixCode).list_prod_mem
  intro x hx
  simp only [List.mem_reverse, sourceUChronologicalSwaps,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h <;>
    subst x <;> exact sourceCrossSwap_mem _ _ _ _ _
theorem elementaryCompressionU_mul_refinedSourceWord (i : Fin 19) :
    (elementaryCompressionU : BinaryLeavitt) *
        leavittWordS (refinedSourceWord i) =
      leavittWordS (refinedTargetWord i) := by
  fin_cases i <;>
    simp [elementaryCompressionU, sourceUChronologicalSwaps,
      sourceCrossSwap_mul_leavittWordS,
      refinedSourceWord, refinedTargetWord,
      refinedSourceParent, refinedSourceSuffix,
      nineWord, uWord, alphaWord, betaWord, nuWord, etaWord,
      binaryWordCancellation, leavittWordS_mul_wordS,
      List.prod_cons, mul_assoc]
theorem elementaryCompressionU_eq_compressionU :
    elementaryCompressionU = compressionU := by
  apply Units.ext
  apply completePrefixWord_ext refinedSourcePrefixCode
    refinedSourcePrefixCode_complete
  intro i
  change
    (elementaryCompressionU : BinaryLeavitt) *
        leavittWordS (refinedSourceWord i) =
      (compressionU : BinaryLeavitt) *
        leavittWordS (refinedSourceWord i)
  rw [elementaryCompressionU_mul_refinedSourceWord,
    compressionU_mul_refinedSourceWord]
theorem compressionU_mem_ninePrefixElementaryGroup :
    compressionU ∈ prefixElementaryGroup ninePrefixCode := by
  rw [← elementaryCompressionU_eq_compressionU]
  exact elementaryCompressionU_mem
end PrefixCompressionU
theorem compressionU_mem_ninePrefixElementaryGroup :
    compressionU ∈ prefixElementaryGroup ninePrefixCode :=
  PrefixCompressionU.compressionU_mem_ninePrefixElementaryGroup
namespace PrefixCompression
open scoped BigOperators
theorem prefixTable_compose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (source middle target : BinaryPrefixCode ι) :
    prefixTable middle target * prefixTable source middle =
      prefixTable source target := by
  change
    (∑ i, leavittWordS (target.word i) *
      leavittWordT (middle.word i)) *
      (∑ j, leavittWordS (middle.word j) *
        leavittWordT (source.word j)) =
      ∑ i, leavittWordS (target.word i) *
        leavittWordT (source.word i)
  calc
    (∑ i, leavittWordS (target.word i) *
        leavittWordT (middle.word i)) *
        (∑ j, leavittWordS (middle.word j) *
          leavittWordT (source.word j)) =
      ∑ i, ∑ j,
        leavittWordS (target.word i) *
          (leavittWordT (middle.word i) *
            leavittWordS (middle.word j)) *
          leavittWordT (source.word j) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            simp [mul_assoc]
    _ = ∑ i, leavittWordS (target.word i) *
          leavittWordT (source.word i) := by
      simp [binaryPrefixCode_orthogonal]
def compressionTransition : BinaryLeavittˣ :=
  prefixTableUnit uPrefixCode vPrefixCode
    uPrefixCode_complete vPrefixCode_complete
theorem compressionV_eq_transition_mul :
    compressionV = compressionTransition * compressionU := by
  apply Units.ext
  change
    prefixTable ninePrefixCode vPrefixCode =
      prefixTable uPrefixCode vPrefixCode *
        prefixTable ninePrefixCode uPrefixCode
  exact (prefixTable_compose ninePrefixCode uPrefixCode vPrefixCode).symm
def nineCrossRoot (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) : BinaryLeavittˣ :=
  prefixElementaryUnit ninePrefixCode i j hij
    (leavittWordS a * leavittWordT b)
theorem nineCrossRoot_mem (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) :
    nineCrossRoot i j hij a b ∈ prefixElementaryGroup ninePrefixCode := by
  exact Subgroup.subset_closure
    ⟨i, j, hij, leavittWordS a * leavittWordT b, rfl⟩
def nineCrossSwap (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) : BinaryLeavittˣ :=
  nineCrossRoot i j hij a b *
    nineCrossRoot j i hij.symm b a *
    nineCrossRoot i j hij a b
theorem nineCrossSwap_mem (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) :
    nineCrossSwap i j hij a b ∈ prefixElementaryGroup ninePrefixCode := by
  exact (prefixElementaryGroup ninePrefixCode).mul_mem
    ((prefixElementaryGroup ninePrefixCode).mul_mem
      (nineCrossRoot_mem i j hij a b)
      (nineCrossRoot_mem j i hij.symm b a))
    (nineCrossRoot_mem i j hij a b)
def compressionTransitionCrossSwaps : List BinaryLeavittˣ :=
  [nineCrossSwap 0 1 (by decide) [1, 0] [],
   nineCrossSwap 0 4 (by decide) [1, 1] [],
   nineCrossSwap 3 7 (by decide) [1] [],
   nineCrossSwap 6 2 (by decide) [1, 0, 0] [],
   nineCrossSwap 6 5 (by decide) [1, 0, 1] [],
   nineCrossSwap 6 8 (by decide) [1, 1] []]
theorem compressionTransitionCrossSwaps_prod_mem :
    compressionTransitionCrossSwaps.prod ∈
      prefixElementaryGroup ninePrefixCode := by
  apply (prefixElementaryGroup ninePrefixCode).list_prod_mem
  intro x hx
  simp only [compressionTransitionCrossSwaps, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h <;>
    subst x <;> exact nineCrossSwap_mem _ _ _ _ _
def transpositionValue {A : Type*} [Ring A]
    (sa ta sb tb : A) : A :=
  1 - sa * ta - sb * tb + sa * tb + sb * ta
theorem transpositionValue_refine {A : Type*} [Ring A]
    (sa ta sb tb p₀ q₀ p₁ q₁ : A)
    (haa : ta * sa = 1) (hbb : tb * sb = 1)
    (hab : ta * sb = 0) (hba : tb * sa = 0)
    (h₀₀ : q₀ * p₀ = 1) (h₁₁ : q₁ * p₁ = 1)
    (h₀₁ : q₀ * p₁ = 0) (h₁₀ : q₁ * p₀ = 0)
    (hpartition : p₀ * q₀ + p₁ * q₁ = 1) :
    transpositionValue (sa * p₀) (q₀ * ta) (sb * p₀) (q₀ * tb) *
        transpositionValue (sa * p₁) (q₁ * ta) (sb * p₁) (q₁ * tb) =
      transpositionValue sa ta sb tb := by
  have haa' (x : A) : ta * (sa * x) = x := by
    rw [← mul_assoc, haa, one_mul]
  have hbb' (x : A) : tb * (sb * x) = x := by
    rw [← mul_assoc, hbb, one_mul]
  have hab' (x : A) : ta * (sb * x) = 0 := by
    rw [← mul_assoc, hab, zero_mul]
  have hba' (x : A) : tb * (sa * x) = 0 := by
    rw [← mul_assoc, hba, zero_mul]
  have h₀₀' (x : A) : q₀ * (p₀ * x) = x := by
    rw [← mul_assoc, h₀₀, one_mul]
  have h₁₁' (x : A) : q₁ * (p₁ * x) = x := by
    rw [← mul_assoc, h₁₁, one_mul]
  have h₀₁' (x : A) : q₀ * (p₁ * x) = 0 := by
    rw [← mul_assoc, h₀₁, zero_mul]
  have h₁₀' (x : A) : q₁ * (p₀ * x) = 0 := by
    rw [← mul_assoc, h₁₀, zero_mul]
  have hpartition' (x : A) :
      p₀ * (q₀ * x) + p₁ * (q₁ * x) = x := by
    rw [← mul_assoc, ← mul_assoc, ← add_mul, hpartition, one_mul]
  have hpartition_left (z x : A) :
      z * (p₀ * (q₀ * x)) + z * (p₁ * (q₁ * x)) = z * x := by
    rw [← mul_add, hpartition']
  unfold transpositionValue
  calc
    _ = 1 -
          (sa * (p₀ * (q₀ * ta)) + sa * (p₁ * (q₁ * ta))) -
          (sb * (p₀ * (q₀ * tb)) + sb * (p₁ * (q₁ * tb))) +
          (sa * (p₀ * (q₀ * tb)) + sa * (p₁ * (q₁ * tb))) +
          (sb * (p₀ * (q₀ * ta)) + sb * (p₁ * (q₁ * ta))) := by
            noncomm_ring [haa, hbb, hab, hba, h₀₀, h₁₁, h₀₁, h₁₀,
              haa', hbb', hab', hba', h₀₀', h₁₁', h₀₁', h₁₀']
    _ = _ := by
      rw [hpartition_left sa ta, hpartition_left sb tb,
        hpartition_left sa tb, hpartition_left sb ta]
theorem nineRefinement_orthogonal
    (i j : Fin 9) (hij : i ≠ j) (a b : List (Fin 2)) :
    leavittWordT (nineWord i ++ a) *
      leavittWordS (nineWord j ++ b) = 0 := by
  have hzero :
      leavittWordT (nineWord i) * leavittWordS (nineWord j) = 0 := by
    simpa [ninePrefixCode, hij] using
      binaryPrefixCode_orthogonal ninePrefixCode i j
  rw [leavittWordT_append, leavittWordS_append]
  calc
    (leavittWordT a * leavittWordT (nineWord i)) *
        (leavittWordS (nineWord j) * leavittWordS b) =
      leavittWordT a *
        (leavittWordT (nineWord i) * leavittWordS (nineWord j)) *
        leavittWordS b := by noncomm_ring
    _ = 0 := by rw [hzero]; simp
theorem nineCrossSwap_val (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) :
    (↑(nineCrossSwap i j hij a b) : BinaryLeavitt) =
      transpositionValue
        (leavittWordS (nineWord i ++ a))
        (leavittWordT (nineWord i ++ a))
        (leavittWordS (nineWord j ++ b))
        (leavittWordT (nineWord j ++ b)) := by
  let A : List (Fin 2) := nineWord i ++ a
  let B : List (Fin 2) := nineWord j ++ b
  let P : BinaryLeavitt := leavittWordS A * leavittWordT B
  let Q : BinaryLeavitt := leavittWordS B * leavittWordT A
  have hBA : leavittWordT B * leavittWordS A = 0 :=
    nineRefinement_orthogonal j i hij.symm b a
  have hPP : P * P = 0 := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS A * leavittWordT B) = 0
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = 0 := by rw [hBA]; simp
  have hPQP : P * Q * P = P := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS B * leavittWordT A) *
        (leavittWordS A * leavittWordT B) =
        leavittWordS A * leavittWordT B
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) *
          (leavittWordT A * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = leavittWordS A * leavittWordT B := by
        rw [leavittWordT_mul_wordS_self,
          leavittWordT_mul_wordS_self]
        simp
  have hPQ : P * Q = leavittWordS A * leavittWordT A := by
    dsimp [P, Q]
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) *
          leavittWordT A := by noncomm_ring
      _ = _ := by rw [leavittWordT_mul_wordS_self]; simp
  have hQP : Q * P = leavittWordS B * leavittWordT B := by
    dsimp [P, Q]
    calc
      (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS B *
          (leavittWordT A * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = _ := by rw [leavittWordT_mul_wordS_self]; simp
  change
    (1 + leavittWordS (nineWord i) *
      (leavittWordS a * leavittWordT b) * leavittWordT (nineWord j)) *
      (1 + leavittWordS (nineWord j) *
        (leavittWordS b * leavittWordT a) * leavittWordT (nineWord i)) *
      (1 + leavittWordS (nineWord i) *
        (leavittWordS a * leavittWordT b) * leavittWordT (nineWord j)) = _
  have hleft :
      leavittWordS (nineWord i) *
          (leavittWordS a * leavittWordT b) * leavittWordT (nineWord j) =
        P := by
    dsimp [P, A, B]
    rw [leavittWordS_append, leavittWordT_append]
    noncomm_ring
  have hright :
      leavittWordS (nineWord j) *
          (leavittWordS b * leavittWordT a) * leavittWordT (nineWord i) =
        Q := by
    dsimp [Q, A, B]
    rw [leavittWordS_append, leavittWordT_append]
    noncomm_ring
  rw [hleft, hright,
    SoficGroups.cylinder_transposition_factorization P Q hPP hPQP,
    hPQ, hQP]
  rfl
def wordSwapValue (a b : List (Fin 2)) : BinaryLeavitt :=
  transpositionValue (leavittWordS a) (leavittWordT a)
    (leavittWordS b) (leavittWordT b)
theorem wordSwapValue_refine (a b : List (Fin 2))
    (hab : leavittWordT a * leavittWordS b = 0)
    (hba : leavittWordT b * leavittWordS a = 0) :
    wordSwapValue (a ++ [0]) (b ++ [0]) *
        wordSwapValue (a ++ [1]) (b ++ [1]) =
      wordSwapValue a b := by
  unfold wordSwapValue
  simpa only [leavittWordS_append, leavittWordT_append,
    leavittWordS, leavittWordT, mul_one, one_mul] using
    transpositionValue_refine
      (leavittWordS a) (leavittWordT a)
      (leavittWordS b) (leavittWordT b)
      (leavittS 0) (leavittT 0)
      (leavittS 1) (leavittT 1)
      (leavittWordT_mul_wordS_self a)
      (leavittWordT_mul_wordS_self b)
      hab hba
      (by simpa using leavittT_mul_S 0 0)
      (by simpa using leavittT_mul_S 1 1)
      (by simpa using leavittT_mul_S 0 1)
      (by simpa using leavittT_mul_S 1 0)
      leavitt_partition
theorem compressionTransitionCrossSwaps_prod_val :
    (↑compressionTransitionCrossSwaps.prod : BinaryLeavitt) =
      wordSwapValue (uWord 1) (uWord 2) *
        wordSwapValue (uWord 4) (uWord 5) *
        wordSwapValue (uWord 7) (uWord 8) := by
  have h₀ :
      wordSwapValue [0, 0, 0, 1, 0] [1, 0, 0, 0] *
        wordSwapValue [0, 0, 0, 1, 1] [1, 0, 0, 1] =
        wordSwapValue [0, 0, 0, 1] [1, 0, 0] := by
    simpa using wordSwapValue_refine
      [0, 0, 0, 1] [1, 0, 0]
      (leavittWordT_mul_wordS_of_incomparable _ _ (by decide) (by decide))
      (leavittWordT_mul_wordS_of_incomparable _ _ (by decide) (by decide))
  have h₂₀ :
      wordSwapValue [0, 1, 1, 0, 0] [1, 1, 0, 0] *
        wordSwapValue [0, 1, 1, 0, 1] [1, 1, 0, 1] =
        wordSwapValue [0, 1, 1, 0] [1, 1, 0] := by
    simpa using wordSwapValue_refine
      [0, 1, 1, 0] [1, 1, 0]
      (leavittWordT_mul_wordS_of_incomparable _ _ (by decide) (by decide))
      (leavittWordT_mul_wordS_of_incomparable _ _ (by decide) (by decide))
  have h₂ :
      wordSwapValue [0, 1, 1, 0] [1, 1, 0] *
        wordSwapValue [0, 1, 1, 1] [1, 1, 1] =
        wordSwapValue [0, 1, 1] [1, 1] := by
    simpa using wordSwapValue_refine
      [0, 1, 1] [1, 1]
      (leavittWordT_mul_wordS_of_incomparable _ _ (by decide) (by decide))
      (leavittWordT_mul_wordS_of_incomparable _ _ (by decide) (by decide))
  simp only [compressionTransitionCrossSwaps, List.prod_cons, List.prod_nil,
    Units.val_mul, nineCrossSwap_val, mul_one]
  change
    wordSwapValue [0, 0, 0, 1, 0] [1, 0, 0, 0] *
      (wordSwapValue [0, 0, 0, 1, 1] [1, 0, 0, 1] *
      (wordSwapValue [0, 0, 1, 1] [1, 0, 1] *
      (wordSwapValue [0, 1, 1, 0, 0] [1, 1, 0, 0] *
      (wordSwapValue [0, 1, 1, 0, 1] [1, 1, 0, 1] *
       wordSwapValue [0, 1, 1, 1] [1, 1, 1])))) =
    wordSwapValue [0, 0, 0, 1] [1, 0, 0] *
      wordSwapValue [0, 0, 1, 1] [1, 0, 1] *
      wordSwapValue [0, 1, 1] [1, 1]
  calc
    _ =
      (wordSwapValue [0, 0, 0, 1, 0] [1, 0, 0, 0] *
        wordSwapValue [0, 0, 0, 1, 1] [1, 0, 0, 1]) *
      wordSwapValue [0, 0, 1, 1] [1, 0, 1] *
      ((wordSwapValue [0, 1, 1, 0, 0] [1, 1, 0, 0] *
        wordSwapValue [0, 1, 1, 0, 1] [1, 1, 0, 1]) *
        wordSwapValue [0, 1, 1, 1] [1, 1, 1]) := by
          noncomm_ring
    _ = _ := by rw [h₀, h₂₀, h₂]
theorem transpositionValue_mul_codeWord {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) (i j : ι) (hij : i ≠ j) (k : ι) :
    transpositionValue
        (leavittWordS (E.word i)) (leavittWordT (E.word i))
        (leavittWordS (E.word j)) (leavittWordT (E.word j)) *
        leavittWordS (E.word k) =
      if k = i then leavittWordS (E.word j)
      else if k = j then leavittWordS (E.word i)
      else leavittWordS (E.word k) := by
  by_cases hki : k = i
  · subst k
    simp [transpositionValue, sub_mul, add_mul, mul_assoc,
      binaryPrefixCode_orthogonal, hij.symm]
  · by_cases hkj : k = j
    · subst k
      simp [transpositionValue, sub_mul, add_mul, mul_assoc,
        binaryPrefixCode_orthogonal, hij, hij.symm]
    · simp [transpositionValue, sub_mul, add_mul, mul_assoc,
        binaryPrefixCode_orthogonal,
        hki, Ne.symm hki, hkj, Ne.symm hkj]
theorem uSwap12_mul (k : Fin 9) :
    wordSwapValue (uWord 1) (uWord 2) * leavittWordS (uWord k) =
      if k = 1 then leavittWordS (uWord 2)
      else if k = 2 then leavittWordS (uWord 1)
      else leavittWordS (uWord k) :=
  transpositionValue_mul_codeWord uPrefixCode 1 2 (by decide) k
theorem uSwap45_mul (k : Fin 9) :
    wordSwapValue (uWord 4) (uWord 5) * leavittWordS (uWord k) =
      if k = 4 then leavittWordS (uWord 5)
      else if k = 5 then leavittWordS (uWord 4)
      else leavittWordS (uWord k) :=
  transpositionValue_mul_codeWord uPrefixCode 4 5 (by decide) k
theorem uSwap78_mul (k : Fin 9) :
    wordSwapValue (uWord 7) (uWord 8) * leavittWordS (uWord k) =
      if k = 7 then leavittWordS (uWord 8)
      else if k = 8 then leavittWordS (uWord 7)
      else leavittWordS (uWord k) :=
  transpositionValue_mul_codeWord uPrefixCode 7 8 (by decide) k
theorem compressionTransitionParentSwaps_mul_word (k : Fin 9) :
    (wordSwapValue (uWord 1) (uWord 2) *
      wordSwapValue (uWord 4) (uWord 5) *
      wordSwapValue (uWord 7) (uWord 8)) *
        leavittWordS (uWord k) = leavittWordS (vWord k) := by
  fin_cases k <;>
    simp [mul_assoc, uSwap12_mul, uSwap45_mul, uSwap78_mul] <;>
    rfl
theorem compressionTransitionParentSwaps_eq_table :
    wordSwapValue (uWord 1) (uWord 2) *
        wordSwapValue (uWord 4) (uWord 5) *
        wordSwapValue (uWord 7) (uWord 8) =
      prefixTable uPrefixCode vPrefixCode := by
  let x : BinaryLeavitt :=
    wordSwapValue (uWord 1) (uWord 2) *
      wordSwapValue (uWord 4) (uWord 5) *
      wordSwapValue (uWord 7) (uWord 8)
  change x = prefixTable uPrefixCode vPrefixCode
  calc
    x = x * 1 := (mul_one x).symm
    _ = x * MatrixCorner.codeIdempotent
          (fun i => leavittWordS (uPrefixCode.word i))
          (fun i => leavittWordT (uPrefixCode.word i)) := by
            rw [uPrefixCode_complete]
    _ = ∑ i : Fin 9,
          (x * leavittWordS (uWord i)) * leavittWordT (uWord i) := by
            simp [MatrixCorner.codeIdempotent, Finset.mul_sum, mul_assoc,
              uPrefixCode]
    _ = ∑ i : Fin 9,
          leavittWordS (vWord i) * leavittWordT (uWord i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [show x * leavittWordS (uWord i) =
              leavittWordS (vWord i) from
              compressionTransitionParentSwaps_mul_word i]
    _ = prefixTable uPrefixCode vPrefixCode := rfl
theorem compressionTransitionCrossSwaps_prod_eq :
    compressionTransitionCrossSwaps.prod = compressionTransition := by
  apply Units.ext
  exact compressionTransitionCrossSwaps_prod_val.trans
    compressionTransitionParentSwaps_eq_table
theorem compressionTransition_mem :
    compressionTransition ∈ prefixElementaryGroup ninePrefixCode := by
  rw [← compressionTransitionCrossSwaps_prod_eq]
  exact compressionTransitionCrossSwaps_prod_mem
theorem compressionV_mem_of_compressionU
    (hU : compressionU ∈ prefixElementaryGroup ninePrefixCode) :
    compressionV ∈ prefixElementaryGroup ninePrefixCode := by
  rw [compressionV_eq_transition_mul]
  exact (prefixElementaryGroup ninePrefixCode).mul_mem
    compressionTransition_mem hU
end PrefixCompression
theorem compressionV_mem_ninePrefixElementaryGroup :
    compressionV ∈ prefixElementaryGroup ninePrefixCode :=
  PrefixCompression.compressionV_mem_of_compressionU
    compressionU_mem_ninePrefixElementaryGroup
noncomputable def rankDropCount {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H r : ℝ) : ℝ :=
  Finset.univ.sum (fun i : ι =>
    if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ then (1 : ℝ) else 0)
namespace CheegerPoincare
open scoped BigOperators
noncomputable def positiveSupport {V : Type*} [Fintype V]
    (f : V → ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x => 0 < f x
@[simp] theorem mem_positiveSupport {V : Type*} [Fintype V]
    (f : V → ℝ) (x : V) :
    x ∈ positiveSupport f ↔ 0 < f x := by
  classical
  simp [positiveSupport]
noncomputable def finiteMean {V : Type*} [Fintype V] (f : V → ℝ) : ℝ :=
  (∑ x : V, f x) / (Fintype.card V : ℝ)
noncomputable def lowerLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x => f x < a
noncomputable def upperLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x => a < f x
@[simp] theorem mem_lowerLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) (x : V) :
    x ∈ lowerLevel f a ↔ f x < a := by
  classical
  simp [lowerLevel]
@[simp] theorem mem_upperLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) (x : V) :
    x ∈ upperLevel f a ↔ a < f x := by
  classical
  simp [upperLevel]
def finiteVariance {V : Type*} [Fintype V] (f : V → ℝ) : ℝ :=
  (∑ x : V, (f x - finiteMean f) ^ 2) / (Fintype.card V : ℝ)
end CheegerPoincare
namespace ThompsonPrefixLocal
open scoped BigOperators
theorem idempotentCornerUnitExtensions_commute
    {A : Type*} [Ring A] {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0)
    (u : he.Cornerˣ) (v : hf.Cornerˣ) :
    Commute
      (idempotentCornerUnitExtension he u)
      (idempotentCornerUnitExtension hf v) := by
  apply Units.ext
  have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
  have hv := (Subsemigroup.mem_corner_iff hf).mp v.val.property
  have huv : u.val.val * v.val.val = 0 := by
    calc
      u.val.val * v.val.val =
          (u.val.val * e) * (f * v.val.val) := by rw [hu.2, hv.1]
      _ = u.val.val * (e * f) * v.val.val := by noncomm_ring
      _ = 0 := by rw [hef]; simp
  have hvu : v.val.val * u.val.val = 0 := by
    calc
      v.val.val * u.val.val =
          (v.val.val * f) * (e * u.val.val) := by rw [hv.2, hu.1]
      _ = v.val.val * (f * e) * u.val.val := by noncomm_ring
      _ = 0 := by rw [hfe]; simp
  have hev : e * v.val.val = 0 := by
    calc
      e * v.val.val = e * (f * v.val.val) := by rw [hv.1]
      _ = (e * f) * v.val.val := by rw [mul_assoc]
      _ = 0 := by rw [hef]; simp
  have hve : v.val.val * e = 0 := by
    calc
      v.val.val * e = (v.val.val * f) * e := by rw [hv.2]
      _ = v.val.val * (f * e) := by rw [mul_assoc]
      _ = 0 := by rw [hfe]; simp
  have huf : u.val.val * f = 0 := by
    calc
      u.val.val * f = (u.val.val * e) * f := by rw [hu.2]
      _ = u.val.val * (e * f) := by rw [mul_assoc]
      _ = 0 := by rw [hef]; simp
  have hfu : f * u.val.val = 0 := by
    calc
      f * u.val.val = f * (e * u.val.val) := by rw [hu.1]
      _ = (f * e) * u.val.val := by rw [mul_assoc]
      _ = 0 := by rw [hfe]; simp
  change
    (u.val.val + (1 - e)) * (v.val.val + (1 - f)) =
      (v.val.val + (1 - f)) * (u.val.val + (1 - e))
  noncomm_ring [he.eq, hf.eq, hu.1, hu.2, hv.1, hv.2,
    hef, hfe, huv, hvu, hev, hve, huf, hfu]
theorem idempotentCornerUnitExtensions_eq_one
    {A : Type*} [Ring A] {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0)
    (u : he.Cornerˣ) (v : hf.Cornerˣ)
    (h : idempotentCornerUnitExtension he u =
      idempotentCornerUnitExtension hf v) :
    idempotentCornerUnitExtension he u = 1 := by
  have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
  have hv := (Subsemigroup.mem_corner_iff hf).mp v.val.property
  have hev : e * v.val.val = 0 := by
    calc
      e * v.val.val = e * (f * v.val.val) := by rw [hv.1]
      _ = (e * f) * v.val.val := by rw [mul_assoc]
      _ = 0 := by rw [hef, zero_mul]
  have hval := congrArg (fun z : Aˣ => (z : A)) h
  change u.val.val + (1 - e) = v.val.val + (1 - f) at hval
  have hleft := congrArg (fun z : A => e * z) hval
  have hue : u.val.val = e := by
    simpa [mul_add, mul_sub, hu.1, he.eq, hev, hef] using hleft
  apply Units.ext
  change u.val.val + (1 - e) = 1
  rw [hue]
  noncomm_ring
def idempotentCornerGroup {A : Type*} [Ring A]
    {e : A} (he : IsIdempotentElem e) : Subgroup Aˣ :=
  (idempotentCornerUnitExtension he).range
theorem idempotentCornerGroup_le_centralizer
    {A : Type*} [Ring A] {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0) :
    idempotentCornerGroup hf ≤
      Subgroup.centralizer (idempotentCornerGroup he : Set Aˣ) := by
  intro z hz
  obtain ⟨v, rfl⟩ := hz
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  obtain ⟨u, rfl⟩ := hx
  exact (idempotentCornerUnitExtensions_commute he hf hef hfe u v).eq
theorem idempotentCornerGroup_inf_eq_bot
    {A : Type*} [Ring A] {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) :
    idempotentCornerGroup he ⊓ idempotentCornerGroup hf = ⊥ := by
  apply le_antisymm
  · intro z hz
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hz
    have huv : idempotentCornerUnitExtension he u =
        idempotentCornerUnitExtension hf v := hu.trans hv.symm
    have hone := idempotentCornerUnitExtensions_eq_one he hf hef u v huv
    have hz : z = 1 := hu.symm.trans hone
    simp [hz]
  · exact bot_le
theorem leavittCylinder_isIdempotent (a : List (Fin 2)) :
    IsIdempotentElem (leavittCylinder a) := by
  change
    (leavittWordS a * leavittWordT a) *
        (leavittWordS a * leavittWordT a) =
      leavittWordS a * leavittWordT a
  calc
    (leavittWordS a * leavittWordT a) *
        (leavittWordS a * leavittWordT a) =
      leavittWordS a *
        (leavittWordT a * leavittWordS a) * leavittWordT a := by
          noncomm_ring
    _ = leavittWordS a * leavittWordT a := by
      rw [leavittWordT_mul_wordS_self]
      simp
theorem leavittCylinder_mul_eq_zero_of_incomparable
    (a b : List (Fin 2)) (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    leavittCylinder a * leavittCylinder b = 0 := by
  change
    (leavittWordS a * leavittWordT a) *
      (leavittWordS b * leavittWordT b) = 0
  calc
    (leavittWordS a * leavittWordT a) *
        (leavittWordS b * leavittWordT b) =
      leavittWordS a *
        (leavittWordT a * leavittWordS b) * leavittWordT b := by
          noncomm_ring
    _ = 0 := by
      rw [leavittWordT_mul_wordS_of_incomparable a b hab hba]
      simp
def cylinderCornerGroup (a : List (Fin 2)) : Subgroup BinaryLeavittˣ :=
  idempotentCornerGroup (leavittCylinder_isIdempotent a)
def prefixCodeIdempotent {ι : Type*} [Fintype ι]
    (E : BinaryPrefixCode ι) : BinaryLeavitt :=
  MatrixCorner.codeIdempotent
    (fun i => leavittWordS (E.word i))
    (fun i => leavittWordT (E.word i))
def prefixCodeCornerGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) : Subgroup BinaryLeavittˣ :=
  idempotentCornerGroup
    (MatrixCorner.codeIdempotent_isIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i))
      (binaryPrefixCode_orthogonal E))
theorem prefixElementaryGroup_le_corner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    prefixElementaryGroup E ≤ prefixCodeCornerGroup E := by
  rw [← prefixCornerElementaryGroup_map E]
  rintro _ ⟨u, _, rfl⟩
  exact ⟨(Units.mapEquiv (binaryPrefixCornerEquiv E).toMulEquiv) u, rfl⟩
def sourceLocalWord : List (Fin 2) := [0, 0, 0, 1]
theorem alphaZeroWord_incomparable_local (i : Fin 3) :
    ¬ alphaZeroPrefixCode.word i <+: sourceLocalWord := by
  fin_cases i <;> decide
theorem localWord_incomparable_alphaZero (i : Fin 3) :
    ¬ sourceLocalWord <+: alphaZeroPrefixCode.word i := by
  fin_cases i <;> decide
theorem alphaZeroCode_mul_localCylinder :
    prefixCodeIdempotent alphaZeroPrefixCode *
        leavittCylinder sourceLocalWord = 0 := by
  change
    (∑ i : Fin 3, leavittCylinder (alphaZeroPrefixCode.word i)) *
        leavittCylinder sourceLocalWord = 0
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  exact leavittCylinder_mul_eq_zero_of_incomparable
    (alphaZeroPrefixCode.word i) sourceLocalWord
    (alphaZeroWord_incomparable_local i)
    (localWord_incomparable_alphaZero i)
theorem localCylinder_mul_alphaZeroCode :
    leavittCylinder sourceLocalWord *
        prefixCodeIdempotent alphaZeroPrefixCode = 0 := by
  change
    leavittCylinder sourceLocalWord *
        (∑ i : Fin 3, leavittCylinder (alphaZeroPrefixCode.word i)) = 0
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact leavittCylinder_mul_eq_zero_of_incomparable
    sourceLocalWord (alphaZeroPrefixCode.word i)
    (localWord_incomparable_alphaZero i)
    (alphaZeroWord_incomparable_local i)
theorem localCylinderCorner_le_centralizer_alphaZero :
    cylinderCornerGroup sourceLocalWord ≤
      Subgroup.centralizer
        (prefixElementaryGroup alphaZeroPrefixCode : Set BinaryLeavittˣ) := by
  let he := MatrixCorner.codeIdempotent_isIdempotent
    (fun i => leavittWordS (alphaZeroPrefixCode.word i))
    (fun i => leavittWordT (alphaZeroPrefixCode.word i))
    (binaryPrefixCode_orthogonal alphaZeroPrefixCode)
  let hf := leavittCylinder_isIdempotent sourceLocalWord
  have hef : prefixCodeIdempotent alphaZeroPrefixCode *
      leavittCylinder sourceLocalWord = 0 :=
    alphaZeroCode_mul_localCylinder
  have hfe : leavittCylinder sourceLocalWord *
      prefixCodeIdempotent alphaZeroPrefixCode = 0 :=
    localCylinder_mul_alphaZeroCode
  intro z hz
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  have hx' := prefixElementaryGroup_le_corner alphaZeroPrefixCode hx
  have hz' : z ∈ idempotentCornerGroup hf := hz
  have hc := idempotentCornerGroup_le_centralizer he hf hef hfe hz'
  exact Subgroup.mem_centralizer_iff.mp hc x hx'
theorem alphaZero_inf_localCylinderCorner_eq_bot :
    prefixElementaryGroup alphaZeroPrefixCode ⊓
        cylinderCornerGroup sourceLocalWord = ⊥ := by
  let he := MatrixCorner.codeIdempotent_isIdempotent
    (fun i => leavittWordS (alphaZeroPrefixCode.word i))
    (fun i => leavittWordT (alphaZeroPrefixCode.word i))
    (binaryPrefixCode_orthogonal alphaZeroPrefixCode)
  let hf := leavittCylinder_isIdempotent sourceLocalWord
  have hzero := idempotentCornerGroup_inf_eq_bot he hf
    alphaZeroCode_mul_localCylinder
  apply le_antisymm
  · intro z hz
    have hx := prefixElementaryGroup_le_corner alphaZeroPrefixCode hz.1
    have hz' : z ∈ idempotentCornerGroup he ⊓ idempotentCornerGroup hf :=
      ⟨hx, hz.2⟩
    rw [hzero] at hz'
    exact hz'
  · exact bot_le
end ThompsonPrefixLocal
def matchedRetainedFinpartition
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) : Finpartition (matchedRetainedSupport R) :=
  P.ofSubset hR (Finset.sup_eq_biUnion R id)
def matchedRadiusBad {V ι : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (I : Finset ι) (w : ι → Equiv.Perm V)
    (B : Finset V) : Finset V :=
  B ∪ I.biUnion fun i => partitionWordCrossing P (w i)
namespace ComponentMidrankVariance
open scoped BigOperators
def lowerRankWeight (s : Finset ℤ) (w : ℤ → ℝ) (j : ℤ) : ℝ :=
  (s.filter (fun i => i < j)).sum w
end ComponentMidrankVariance
noncomputable def insufficientOverlapComponents
    {V : Type u} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (eta : ℝ) : Finset (Finset V) := by
  classical
  exact P.parts.filter fun C =>
    ((C ∩ maximumOverlapPart Q C).card : ℝ) <
      (1 - eta) * (C.card : ℝ)
noncomputable def finsetPermutationOrderIso
    {V : Type u} (T : Equiv.Perm V) : Finset V ≃o Finset V where
  toEquiv := T.finsetCongr
  map_rel_iff' := by
    intro A B
    exact Finset.map_subset_map
noncomputable def transportedFinpartition
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (T : Equiv.Perm V) :
    Finpartition (U.map T.toEmbedding) :=
  Q.map (finsetPermutationOrderIso T)
@[simp]
theorem transportedFinpartition_parts
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (T : Equiv.Perm V) :
    (transportedFinpartition Q T).parts =
      Q.parts.image (fun C : Finset V => C.map T.toEmbedding) := by
  classical
  change Q.parts.map (finsetPermutationOrderIso T).toEmbedding =
    Q.parts.image (fun C : Finset V => C.map T.toEmbedding)
  exact Finset.map_eq_image (finsetPermutationOrderIso T).toEmbedding Q.parts
noncomputable def transportedUnivFinpartition
    {V : Type u} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) : Finpartition (Finset.univ : Finset V) :=
  (transportedFinpartition Q T).copy (Finset.map_univ_equiv T)
@[simp]
theorem transportedUnivFinpartition_parts
    {V : Type u} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) :
    (transportedUnivFinpartition Q T).parts =
      Q.parts.image (fun C : Finset V => C.map T.toEmbedding) := by
  exact transportedFinpartition_parts Q T
noncomputable def partitionComponentSize
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (x : V) : ℕ :=
  (Q.part x).card
namespace ThompsonPrefixInsertion
open scoped BigOperators
def singletonPrefixCode (a : List (Fin 2)) : BinaryPrefixCode (Fin 1) where
  word _ := a
  prefix_free := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
theorem singletonPrefixCode_codeIdempotent (a : List (Fin 2)) :
    MatrixCorner.codeIdempotent
        (fun i => leavittWordS ((singletonPrefixCode a).word i))
        (fun i => leavittWordT ((singletonPrefixCode a).word i)) =
      leavittCylinder a := by
  simp [MatrixCorner.codeIdempotent, singletonPrefixCode, leavittCylinder]
def prefixInsertionHom (a : List (Fin 2)) :
    BinaryLeavittˣ →* BinaryLeavittˣ :=
  (prefixCornerUnitHom (singletonPrefixCode a)).comp
    (Units.mapEquiv
      (Matrix.uniqueRingEquiv (m := Fin 1)
        (A := BinaryLeavitt)).symm.toMulEquiv).toMonoidHom
theorem leavittCylinder_isIdempotent (a : List (Fin 2)) :
    IsIdempotentElem (leavittCylinder a) := by
  change
    (leavittWordS a * leavittWordT a) *
        (leavittWordS a * leavittWordT a) =
      leavittWordS a * leavittWordT a
  calc
    (leavittWordS a * leavittWordT a) *
        (leavittWordS a * leavittWordT a) =
      leavittWordS a *
        (leavittWordT a * leavittWordS a) * leavittWordT a := by
          noncomm_ring
    _ = leavittWordS a * leavittWordT a := by
      rw [leavittWordT_mul_wordS_self]
      simp
def cylinderCornerGroup (a : List (Fin 2)) : Subgroup BinaryLeavittˣ :=
  (idempotentCornerUnitExtension (leavittCylinder_isIdempotent a)).range
theorem cylinderCornerGroup_eq_source (a : List (Fin 2)) :
    cylinderCornerGroup a = ThompsonPrefixLocal.cylinderCornerGroup a := by
  rfl
theorem prefixInsertionHom_mem_cylinderCorner
    (a : List (Fin 2)) (u : BinaryLeavittˣ) :
    prefixInsertionHom a u ∈ cylinderCornerGroup a := by
  unfold cylinderCornerGroup
  let he := MatrixCorner.codeIdempotent_isIdempotent
    (fun i => leavittWordS ((singletonPrefixCode a).word i))
    (fun i => leavittWordT ((singletonPrefixCode a).word i))
    (binaryPrefixCode_orthogonal (singletonPrefixCode a))
  have hidem :
      (⟨MatrixCorner.codeIdempotent
        (fun i => leavittWordS ((singletonPrefixCode a).word i))
        (fun i => leavittWordT ((singletonPrefixCode a).word i)), he⟩ :
          {e : BinaryLeavitt // IsIdempotentElem e}) =
        ⟨leavittCylinder a, leavittCylinder_isIdempotent a⟩ :=
    Subtype.ext (singletonPrefixCode_codeIdempotent a)
  have hcorner := congrArg
    (fun p : {e : BinaryLeavitt // IsIdempotentElem e} =>
      (idempotentCornerUnitExtension p.property).range)
    hidem
  rw [← hcorner]
  refine ⟨(Units.mapEquiv
      (binaryPrefixCornerEquiv (singletonPrefixCode a)).toMulEquiv)
    ((Units.mapEquiv
      (Matrix.uniqueRingEquiv (m := Fin 1)
        (A := BinaryLeavitt)).symm.toMulEquiv) u), ?_⟩
  rfl
theorem prefixInsertionHom_val (a : List (Fin 2)) (u : BinaryLeavittˣ) :
    (↑(prefixInsertionHom a u) : BinaryLeavitt) =
      leavittWordS a * (u : BinaryLeavitt) * leavittWordT a +
        (1 - leavittCylinder a) := by
  change
    MatrixCorner.encode
        (fun i => leavittWordS ((singletonPrefixCode a).word i))
        (fun i => leavittWordT ((singletonPrefixCode a).word i))
        ((Matrix.uniqueRingEquiv (m := Fin 1)
          (A := BinaryLeavitt)).symm (u : BinaryLeavitt)) +
      (1 - MatrixCorner.codeIdempotent
        (fun i => leavittWordS ((singletonPrefixCode a).word i))
        (fun i => leavittWordT ((singletonPrefixCode a).word i))) = _
  simp [MatrixCorner.encode, MatrixCorner.codeIdempotent,
    singletonPrefixCode, leavittCylinder]
theorem transpositionValue_mul_self {A : Type*} [Ring A]
    (sa ta sb tb : A)
    (haa : ta * sa = 1) (hbb : tb * sb = 1)
    (hab : ta * sb = 0) (hba : tb * sa = 0) :
    PrefixCompression.transpositionValue sa ta sb tb *
      PrefixCompression.transpositionValue sa ta sb tb = 1 := by
  have haa' (x : A) : ta * (sa * x) = x := by
    rw [← mul_assoc, haa, one_mul]
  have hbb' (x : A) : tb * (sb * x) = x := by
    rw [← mul_assoc, hbb, one_mul]
  have hab' (x : A) : ta * (sb * x) = 0 := by
    rw [← mul_assoc, hab, zero_mul]
  have hba' (x : A) : tb * (sa * x) = 0 := by
    rw [← mul_assoc, hba, zero_mul]
  unfold PrefixCompression.transpositionValue
  noncomm_ring [haa, hbb, hab, hba, haa', hbb', hab', hba']
def cylinderSwap (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) : BinaryLeavittˣ where
  val := PrefixCompression.wordSwapValue a b
  inv := PrefixCompression.wordSwapValue a b
  val_inv := transpositionValue_mul_self
    (leavittWordS a) (leavittWordT a)
    (leavittWordS b) (leavittWordT b)
    (leavittWordT_mul_wordS_self a)
    (leavittWordT_mul_wordS_self b)
    (leavittWordT_mul_wordS_of_incomparable a b hab hba)
    (leavittWordT_mul_wordS_of_incomparable b a hba hab)
  inv_val := transpositionValue_mul_self
    (leavittWordS a) (leavittWordT a)
    (leavittWordS b) (leavittWordT b)
    (leavittWordT_mul_wordS_self a)
    (leavittWordT_mul_wordS_self b)
    (leavittWordT_mul_wordS_of_incomparable a b hab hba)
    (leavittWordT_mul_wordS_of_incomparable b a hba hab)
theorem append_not_prefix_append (a b x y : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    ¬ a ++ x <+: b ++ y := by
  intro h
  have ha : a <+: b ++ y := (List.prefix_append a x).trans h
  by_cases hle : a.length ≤ b.length
  · exact hab ((List.isPrefix_append_of_length hle).mp ha)
  · apply hba
    rw [List.prefix_iff_eq_take]
    have hea := List.prefix_iff_eq_take.mp ha
    rw [hea, List.take_take, Nat.min_eq_left (Nat.le_of_not_ge hle)]
    simp
theorem prepend_not_prefix_prepend (l a b : List (Fin 2))
    (hab : ¬ a <+: b) :
    ¬ l ++ a <+: l ++ b := by
  intro h
  apply hab
  simpa using h
theorem prefixInsertionHom_cylinderSwap
    (l a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    prefixInsertionHom l (cylinderSwap a b hab hba) =
      cylinderSwap (l ++ a) (l ++ b)
        (prepend_not_prefix_prepend l a b hab)
        (prepend_not_prefix_prepend l b a hba) := by
  apply Units.ext
  rw [prefixInsertionHom_val]
  change
    leavittWordS l *
        (1 - leavittWordS a * leavittWordT a -
          leavittWordS b * leavittWordT b +
          leavittWordS a * leavittWordT b +
          leavittWordS b * leavittWordT a) * leavittWordT l +
        (1 - leavittWordS l * leavittWordT l) =
      1 - leavittWordS (l ++ a) * leavittWordT (l ++ a) -
        leavittWordS (l ++ b) * leavittWordT (l ++ b) +
        leavittWordS (l ++ a) * leavittWordT (l ++ b) +
        leavittWordS (l ++ b) * leavittWordT (l ++ a)
  rw [leavittWordS_append, leavittWordT_append,
    leavittWordS_append, leavittWordT_append]
  simp only [CharTwo.sub_eq_add]
  noncomm_ring
  simp [CharTwo.two_eq_zero]
theorem transpositionValue_braid {A : Type*} [Ring A]
    (sa ta sb tb sc tc : A)
    (haa : ta * sa = 1) (hbb : tb * sb = 1) (hcc : tc * sc = 1)
    (hab : ta * sb = 0) (hba : tb * sa = 0)
    (hac : ta * sc = 0) (hca : tc * sa = 0)
    (hbc : tb * sc = 0) (hcb : tc * sb = 0) :
    PrefixCompression.transpositionValue sa ta sc tc *
        PrefixCompression.transpositionValue sb tb sc tc *
        PrefixCompression.transpositionValue sa ta sc tc =
      PrefixCompression.transpositionValue sa ta sb tb := by
  have haa' (x : A) : ta * (sa * x) = x := by
    rw [← mul_assoc, haa, one_mul]
  have hbb' (x : A) : tb * (sb * x) = x := by
    rw [← mul_assoc, hbb, one_mul]
  have hcc' (x : A) : tc * (sc * x) = x := by
    rw [← mul_assoc, hcc, one_mul]
  have hab' (x : A) : ta * (sb * x) = 0 := by
    rw [← mul_assoc, hab, zero_mul]
  have hba' (x : A) : tb * (sa * x) = 0 := by
    rw [← mul_assoc, hba, zero_mul]
  have hac' (x : A) : ta * (sc * x) = 0 := by
    rw [← mul_assoc, hac, zero_mul]
  have hca' (x : A) : tc * (sa * x) = 0 := by
    rw [← mul_assoc, hca, zero_mul]
  have hbc' (x : A) : tb * (sc * x) = 0 := by
    rw [← mul_assoc, hbc, zero_mul]
  have hcb' (x : A) : tc * (sb * x) = 0 := by
    rw [← mul_assoc, hcb, zero_mul]
  unfold PrefixCompression.transpositionValue
  noncomm_ring [haa, hbb, hcc, hab, hba, hac, hca, hbc, hcb,
    haa', hbb', hcc', hab', hba', hac', hca', hbc', hcb']
def prefixCrossRoot {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) : BinaryLeavittˣ :=
  prefixElementaryUnit E i j hij
    (leavittWordS a * leavittWordT b)
theorem prefixCrossRoot_mem {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) :
    prefixCrossRoot E i j hij a b ∈ prefixElementaryGroup E :=
  Subgroup.subset_closure
    ⟨i, j, hij, leavittWordS a * leavittWordT b, rfl⟩
def prefixCrossSwap {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) : BinaryLeavittˣ :=
  prefixCrossRoot E i j hij a b *
    prefixCrossRoot E j i hij.symm b a *
    prefixCrossRoot E i j hij a b
theorem prefixCrossSwap_mem {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) :
    prefixCrossSwap E i j hij a b ∈ prefixElementaryGroup E :=
  (prefixElementaryGroup E).mul_mem
    ((prefixElementaryGroup E).mul_mem
      (prefixCrossRoot_mem E i j hij a b)
      (prefixCrossRoot_mem E j i hij.symm b a))
    (prefixCrossRoot_mem E i j hij a b)
theorem prefixCrossSwap_val {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) :
    (↑(prefixCrossSwap E i j hij a b) : BinaryLeavitt) =
      PrefixCompression.wordSwapValue
        (E.word i ++ a) (E.word j ++ b) := by
  let A : List (Fin 2) := E.word i ++ a
  let B : List (Fin 2) := E.word j ++ b
  let P : BinaryLeavitt := leavittWordS A * leavittWordT B
  let Q : BinaryLeavitt := leavittWordS B * leavittWordT A
  have hBA : leavittWordT B * leavittWordS A = 0 := by
    apply leavittWordT_mul_wordS_of_incomparable B A
    · exact append_not_prefix_append (E.word j) (E.word i)
        b a (E.prefix_free hij.symm) (E.prefix_free hij)
    · exact append_not_prefix_append (E.word i) (E.word j)
        a b (E.prefix_free hij) (E.prefix_free hij.symm)
  have hPP : P * P = 0 := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS A * leavittWordT B) = 0
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = 0 := by rw [hBA]; simp
  have hPQP : P * Q * P = P := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS B * leavittWordT A) *
        (leavittWordS A * leavittWordT B) =
        leavittWordS A * leavittWordT B
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) *
          (leavittWordT A * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = leavittWordS A * leavittWordT B := by
        rw [leavittWordT_mul_wordS_self,
          leavittWordT_mul_wordS_self]
        simp
  have hPQ : P * Q = leavittWordS A * leavittWordT A := by
    dsimp [P, Q]
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) *
          leavittWordT A := by noncomm_ring
      _ = _ := by rw [leavittWordT_mul_wordS_self]; simp
  have hQP : Q * P = leavittWordS B * leavittWordT B := by
    dsimp [P, Q]
    calc
      (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS B *
          (leavittWordT A * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = _ := by rw [leavittWordT_mul_wordS_self]; simp
  change
    (1 + leavittWordS (E.word i) *
      (leavittWordS a * leavittWordT b) * leavittWordT (E.word j)) *
      (1 + leavittWordS (E.word j) *
        (leavittWordS b * leavittWordT a) * leavittWordT (E.word i)) *
      (1 + leavittWordS (E.word i) *
        (leavittWordS a * leavittWordT b) * leavittWordT (E.word j)) = _
  have hleft :
      leavittWordS (E.word i) *
          (leavittWordS a * leavittWordT b) * leavittWordT (E.word j) =
        P := by
    dsimp [P, A, B]
    rw [leavittWordS_append, leavittWordT_append]
    noncomm_ring
  have hright :
      leavittWordS (E.word j) *
          (leavittWordS b * leavittWordT a) * leavittWordT (E.word i) =
        Q := by
    dsimp [Q, A, B]
    rw [leavittWordS_append, leavittWordT_append]
    noncomm_ring
  rw [hleft, hright,
    cylinder_transposition_factorization P Q hPP hPQP,
    hPQ, hQP]
  rfl
theorem samePrefixCylinderSwap_mem {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j)
    (a b c : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    cylinderSwap (E.word i ++ a) (E.word i ++ b)
        (prepend_not_prefix_prepend (E.word i) a b hab)
        (prepend_not_prefix_prepend (E.word i) b a hba) ∈
      prefixElementaryGroup E := by
  let x := prefixCrossSwap E i j hij a c
  let y := prefixCrossSwap E i j hij b c
  have hx : x ∈ prefixElementaryGroup E :=
    prefixCrossSwap_mem E i j hij a c
  have hy : y ∈ prefixElementaryGroup E :=
    prefixCrossSwap_mem E i j hij b c
  have hfactor : x * y * x =
      cylinderSwap (E.word i ++ a) (E.word i ++ b)
        (prepend_not_prefix_prepend (E.word i) a b hab)
        (prepend_not_prefix_prepend (E.word i) b a hba) := by
    apply Units.ext
    change
      (↑(prefixCrossSwap E i j hij a c) : BinaryLeavitt) *
          (↑(prefixCrossSwap E i j hij b c) : BinaryLeavitt) *
          (↑(prefixCrossSwap E i j hij a c) : BinaryLeavitt) =
        PrefixCompression.wordSwapValue (E.word i ++ a) (E.word i ++ b)
    rw [prefixCrossSwap_val, prefixCrossSwap_val]
    exact transpositionValue_braid
      (leavittWordS (E.word i ++ a))
      (leavittWordT (E.word i ++ a))
      (leavittWordS (E.word i ++ b))
      (leavittWordT (E.word i ++ b))
      (leavittWordS (E.word j ++ c))
      (leavittWordT (E.word j ++ c))
      (leavittWordT_mul_wordS_self (E.word i ++ a))
      (leavittWordT_mul_wordS_self (E.word i ++ b))
      (leavittWordT_mul_wordS_self (E.word j ++ c))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word i ++ a) (E.word i ++ b)
        (prepend_not_prefix_prepend (E.word i) a b hab)
        (prepend_not_prefix_prepend (E.word i) b a hba))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word i ++ b) (E.word i ++ a)
        (prepend_not_prefix_prepend (E.word i) b a hba)
        (prepend_not_prefix_prepend (E.word i) a b hab))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word i ++ a) (E.word j ++ c)
        (append_not_prefix_append (E.word i) (E.word j) a c
          (E.prefix_free hij) (E.prefix_free hij.symm))
        (append_not_prefix_append (E.word j) (E.word i) c a
          (E.prefix_free hij.symm) (E.prefix_free hij)))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word j ++ c) (E.word i ++ a)
        (append_not_prefix_append (E.word j) (E.word i) c a
          (E.prefix_free hij.symm) (E.prefix_free hij))
        (append_not_prefix_append (E.word i) (E.word j) a c
          (E.prefix_free hij) (E.prefix_free hij.symm)))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word i ++ b) (E.word j ++ c)
        (append_not_prefix_append (E.word i) (E.word j) b c
          (E.prefix_free hij) (E.prefix_free hij.symm))
        (append_not_prefix_append (E.word j) (E.word i) c b
          (E.prefix_free hij.symm) (E.prefix_free hij)))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word j ++ c) (E.word i ++ b)
        (append_not_prefix_append (E.word j) (E.word i) c b
          (E.prefix_free hij.symm) (E.prefix_free hij))
        (append_not_prefix_append (E.word i) (E.word j) b c
          (E.prefix_free hij) (E.prefix_free hij.symm)))
  rw [← hfactor]
  exact (prefixElementaryGroup E).mul_mem
    ((prefixElementaryGroup E).mul_mem hx hy) hx
theorem sourceLocal_cylinderSwap_mem_alpha
    (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    prefixInsertionHom [0, 0, 0, 1] (cylinderSwap a b hab hba) ∈
      prefixElementaryGroup alphaPrefixCode := by
  rw [prefixInsertionHom_cylinderSwap]
  have h := samePrefixCylinderSwap_mem alphaPrefixCode
    (0 : Fin 3) (1 : Fin 3) (by decide)
    ([1] ++ a) ([1] ++ b) []
    (prepend_not_prefix_prepend [1] a b hab)
    (prepend_not_prefix_prepend [1] b a hba)
  simpa [alphaPrefixCode, alphaWord, List.append_assoc] using h
def binaryPrefixTranspositionGroup : Subgroup BinaryLeavittˣ :=
  Subgroup.closure
    {z | ∃ (a b : List (Fin 2))
      (hab : ¬ a <+: b) (hba : ¬ b <+: a),
      cylinderSwap a b hab hba = z}
def localPrefixTranspositionGroup
    (l : List (Fin 2)) : Subgroup BinaryLeavittˣ :=
  binaryPrefixTranspositionGroup.map (prefixInsertionHom l)
theorem localPrefixTranspositionGroup_le_cylinderCorner
    (l : List (Fin 2)) :
    localPrefixTranspositionGroup l ≤ cylinderCornerGroup l := by
  rintro _ ⟨u, _, rfl⟩
  exact prefixInsertionHom_mem_cylinderCorner l u
theorem localPrefixTranspositionGroup_le_sourceCylinderCorner
    (l : List (Fin 2)) :
    localPrefixTranspositionGroup l ≤
      ThompsonPrefixLocal.cylinderCornerGroup l := by
  rw [← cylinderCornerGroup_eq_source]
  exact localPrefixTranspositionGroup_le_cylinderCorner l
theorem sourceLocalPrefixTranspositionGroup_le_alpha :
    localPrefixTranspositionGroup [0, 0, 0, 1] ≤
      prefixElementaryGroup alphaPrefixCode := by
  apply (Subgroup.map_le_iff_le_comap).2
  apply (Subgroup.closure_le _).2
  rintro _ ⟨a, b, hab, hba, rfl⟩
  exact sourceLocal_cylinderSwap_mem_alpha a b hab hba
theorem sourceLocalPrefixTranspositionGroup_le_alpha_sourceWord :
    localPrefixTranspositionGroup ThompsonPrefixLocal.sourceLocalWord ≤
      prefixElementaryGroup alphaPrefixCode := by
  exact sourceLocalPrefixTranspositionGroup_le_alpha
theorem sourceLocalPrefixTranspositionGroup_le_nine :
    localPrefixTranspositionGroup ThompsonPrefixLocal.sourceLocalWord ≤
      prefixElementaryGroup ninePrefixCode :=
  sourceLocalPrefixTranspositionGroup_le_alpha_sourceWord.trans
    SourceGeneration.alphaPrefixElementaryGroup_le_nine
theorem sourceLocalPrefixTranspositionGroup_le_centralizer_alphaZero :
    localPrefixTranspositionGroup ThompsonPrefixLocal.sourceLocalWord ≤
      Subgroup.centralizer
        (prefixElementaryGroup alphaZeroPrefixCode : Set BinaryLeavittˣ) :=
  (localPrefixTranspositionGroup_le_sourceCylinderCorner
    ThompsonPrefixLocal.sourceLocalWord).trans
    ThompsonPrefixLocal.localCylinderCorner_le_centralizer_alphaZero
theorem alphaZero_inf_sourceLocalPrefixTranspositionGroup_eq_bot :
    prefixElementaryGroup alphaZeroPrefixCode ⊓
        localPrefixTranspositionGroup ThompsonPrefixLocal.sourceLocalWord = ⊥ := by
  apply le_antisymm
  · calc
      prefixElementaryGroup alphaZeroPrefixCode ⊓
          localPrefixTranspositionGroup ThompsonPrefixLocal.sourceLocalWord ≤
        prefixElementaryGroup alphaZeroPrefixCode ⊓
          ThompsonPrefixLocal.cylinderCornerGroup
            ThompsonPrefixLocal.sourceLocalWord :=
          inf_le_inf_left _
            (localPrefixTranspositionGroup_le_sourceCylinderCorner
              ThompsonPrefixLocal.sourceLocalWord)
      _ = ⊥ := ThompsonPrefixLocal.alphaZero_inf_localCylinderCorner_eq_bot
  · exact bot_le
def sourceCompressedLocalProductHom :
    (prefixElementaryGroup alphaZeroPrefixCode ×
      localPrefixTranspositionGroup ThompsonPrefixLocal.sourceLocalWord) →*
        BinaryLeavittˣ where
  toFun x := (x.1 : BinaryLeavittˣ) * (x.2 : BinaryLeavittˣ)
  map_one' := by simp
  map_mul' p q := by
    have hcomm :
        (q.1 : BinaryLeavittˣ) * (p.2 : BinaryLeavittˣ) =
          (p.2 : BinaryLeavittˣ) * (q.1 : BinaryLeavittˣ) :=
      Subgroup.mem_centralizer_iff.mp
        (sourceLocalPrefixTranspositionGroup_le_centralizer_alphaZero
          p.2.property)
        (q.1 : BinaryLeavittˣ) q.1.property
    change
      ((p.1 : BinaryLeavittˣ) * (q.1 : BinaryLeavittˣ)) *
          ((p.2 : BinaryLeavittˣ) * (q.2 : BinaryLeavittˣ)) =
        ((p.1 : BinaryLeavittˣ) * (p.2 : BinaryLeavittˣ)) *
          ((q.1 : BinaryLeavittˣ) * (q.2 : BinaryLeavittˣ))
    calc
      ((p.1 : BinaryLeavittˣ) * (q.1 : BinaryLeavittˣ)) *
          ((p.2 : BinaryLeavittˣ) * (q.2 : BinaryLeavittˣ)) =
        (p.1 : BinaryLeavittˣ) *
          (((q.1 : BinaryLeavittˣ) * (p.2 : BinaryLeavittˣ)) *
            (q.2 : BinaryLeavittˣ)) := by simp [mul_assoc]
      _ = (p.1 : BinaryLeavittˣ) *
          (((p.2 : BinaryLeavittˣ) * (q.1 : BinaryLeavittˣ)) *
            (q.2 : BinaryLeavittˣ)) := by rw [hcomm]
      _ = ((p.1 : BinaryLeavittˣ) * (p.2 : BinaryLeavittˣ)) *
          ((q.1 : BinaryLeavittˣ) * (q.2 : BinaryLeavittˣ)) := by
            simp [mul_assoc]
theorem sourceCompressedLocalProductHom_injective :
    Function.Injective sourceCompressedLocalProductHom := by
  apply (injective_iff_map_eq_one sourceCompressedLocalProductHom).2
  rintro ⟨k, j⟩ hone
  change (k : BinaryLeavittˣ) * (j : BinaryLeavittˣ) = 1 at hone
  have hkinv : (k : BinaryLeavittˣ) = (j : BinaryLeavittˣ)⁻¹ :=
    eq_inv_of_mul_eq_one_left hone
  have hkJ :
      (k : BinaryLeavittˣ) ∈
        localPrefixTranspositionGroup ThompsonPrefixLocal.sourceLocalWord := by
    rw [hkinv]
    exact (localPrefixTranspositionGroup
      ThompsonPrefixLocal.sourceLocalWord).inv_mem j.property
  have hkbot :
      (k : BinaryLeavittˣ) ∈
        prefixElementaryGroup alphaZeroPrefixCode ⊓
          localPrefixTranspositionGroup
            ThompsonPrefixLocal.sourceLocalWord :=
    ⟨k.property, hkJ⟩
  rw [alphaZero_inf_sourceLocalPrefixTranspositionGroup_eq_bot] at hkbot
  have hkone : (k : BinaryLeavittˣ) = 1 := by
    simpa using hkbot
  have hjone : (j : BinaryLeavittˣ) = 1 := by
    simpa [hkone] using hone
  apply Prod.ext
  · exact Subtype.ext hkone
  · exact Subtype.ext hjone
theorem sourceCompressedLocalProductHom_range_le_nine :
    sourceCompressedLocalProductHom.range ≤
      prefixElementaryGroup ninePrefixCode := by
  rintro _ ⟨⟨k, j⟩, rfl⟩
  exact (prefixElementaryGroup ninePrefixCode).mul_mem
    (SourceGeneration.alphaPrefixElementaryGroup_le_nine
      (alphaZero_prefixElementaryGroup_le k.property))
    (sourceLocalPrefixTranspositionGroup_le_nine j.property)
def sourceCompressedLocalProductEmbedding :
    (prefixElementaryGroup alphaZeroPrefixCode ×
      localPrefixTranspositionGroup ThompsonPrefixLocal.sourceLocalWord) →*
        prefixElementaryGroup ninePrefixCode :=
  sourceCompressedLocalProductHom.codRestrict
    (prefixElementaryGroup ninePrefixCode)
    (fun x => sourceCompressedLocalProductHom_range_le_nine ⟨x, rfl⟩)
theorem sourceCompressedLocalProductEmbedding_injective :
    Function.Injective sourceCompressedLocalProductEmbedding := by
  intro x y hxy
  apply sourceCompressedLocalProductHom_injective
  exact congrArg Subtype.val hxy
end ThompsonPrefixInsertion
namespace MidrankPermutationEnergy
def partitionVertexMidrank {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U) (b : V → ℤ) (x : V) : ℝ :=
  componentVertexMidrank (P.part x) b x
def rankDecreasingVertices {V : Type*}
    (U : Finset V) (b : V → ℤ) (p : Equiv.Perm V) : Finset V :=
  U.filter (fun x => b (p x) < b x)
def offsetFloorRank {V : Type*} (u : V → ℝ) (H r : ℝ) : V → ℤ :=
  fun x => ⌊(u x + r) / H⌋
def midpointDecreasingVertices {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U) (b : V → ℤ)
    (p : Equiv.Perm V) : Finset V :=
  U.filter (fun x => partitionVertexMidrank P b (p x) <
    partitionVertexMidrank P b x)
end MidrankPermutationEnergy
namespace RankArcCharging
open scoped BigOperators
def selectedRankSupport
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ) : Finset V :=
  P.parts.biUnion (fun C => C.filter (fun x => b x = j C))
def rankChangingArc
    {V : Type*}
    (U : Finset V) (b : V → ℤ) (w : Equiv.Perm V) : Finset V :=
  U.filter (fun x => b (w x) ≠ b x)
def rankSupportPreimageBad
    {V : Type*} [DecidableEq V]
    (U S : Finset V) (w : Equiv.Perm V) : Finset V :=
  U.filter (fun x => w x ∈ U \ S)
end RankArcCharging
def permutationDistance {V : Type*} [Fintype V] [DecidableEq V]
    (p q : Equiv.Perm V) : ℕ :=
  hammingDist (fun x => p x) (fun x => q x)
@[simp]
theorem permutationDistance_self {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) : permutationDistance p p = 0 := by
  simp [permutationDistance]
theorem permutationDistance_comm {V : Type*} [Fintype V] [DecidableEq V]
    (p q : Equiv.Perm V) : permutationDistance p q = permutationDistance q p := by
  exact hammingDist_comm _ _
theorem permutationDistance_triangle {V : Type*}
    [Fintype V] [DecidableEq V] (p q r : Equiv.Perm V) :
    permutationDistance p r ≤ permutationDistance p q + permutationDistance q r :=
  hammingDist_triangle _ _ _
theorem permutationDistance_mul_left {V : Type*}
    [Fintype V] [DecidableEq V] (s p q : Equiv.Perm V) :
    permutationDistance (s * p) (s * q) = permutationDistance p q := by
  have h := hammingDist_comp (fun (_ : V) (x : V) => s x)
    (x := fun x => p x) (y := fun x => q x) (fun _ => s.injective)
  simpa [permutationDistance, Equiv.Perm.mul_apply] using h
theorem permutationDistance_mul_right {V : Type*}
    [Fintype V] [DecidableEq V] (s p q : Equiv.Perm V) :
    permutationDistance (p * s) (q * s) = permutationDistance p q := by
  unfold permutationDistance hammingDist
  apply Finset.card_bij (fun x _ => s x)
  · intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [Equiv.Perm.mul_apply] using (Finset.mem_filter.mp hx).2
  · intro x hx y hy h
    exact s.injective h
  · intro y hy
    refine ⟨s.symm y, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using
      (Finset.mem_filter.mp hy).2
theorem permutationDistance_mul_le {V : Type*}
    [Fintype V] [DecidableEq V] (p p' q q' : Equiv.Perm V) :
    permutationDistance (p * q) (p' * q') ≤
      permutationDistance p p' + permutationDistance q q' := by
  calc
    permutationDistance (p * q) (p' * q') ≤
        permutationDistance (p * q) (p' * q) +
          permutationDistance (p' * q) (p' * q') :=
      permutationDistance_triangle _ _ _
    _ = permutationDistance p p' + permutationDistance q q' := by
      rw [permutationDistance_mul_right, permutationDistance_mul_left]
theorem permutationDistance_inv {V : Type*}
    [Fintype V] [DecidableEq V] (p q : Equiv.Perm V) :
    permutationDistance p⁻¹ q⁻¹ = permutationDistance p q := by
  calc
    permutationDistance p⁻¹ q⁻¹ =
        permutationDistance (q * p⁻¹) (q * q⁻¹) :=
      (permutationDistance_mul_left q p⁻¹ q⁻¹).symm
    _ = permutationDistance (q * p⁻¹) 1 := by simp
    _ = permutationDistance ((q * p⁻¹) * p) (1 * p) :=
      (permutationDistance_mul_right p (q * p⁻¹) 1).symm
    _ = permutationDistance q p := by simp
    _ = permutationDistance p q := permutationDistance_comm q p
@[simp]
theorem permutationCommutationDefect_one {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) :
    permutationCommutationDefect σ 1 = 0 := by
  simp [permutationCommutationDefect]
theorem permutationCommutationDefect_inv {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (c : Equiv.Perm V) :
    permutationCommutationDefect σ c⁻¹ = permutationCommutationDefect σ c := by
  classical
  unfold permutationCommutationDefect
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.card_bij (fun x _ => c⁻¹ x)
  · intro x hx
    have hbad := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro heq
    apply hbad
    apply c.injective
    simpa using heq.symm
  · intro x hx y hy heq
    exact (c⁻¹).injective heq
  · intro y hy
    have hbad := (Finset.mem_filter.mp hy).2
    refine ⟨c y, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro heq
    apply hbad
    have heq' := congrArg c heq
    simpa using heq'.symm
theorem permutationCommutationDefect_mul_le {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (p q : Equiv.Perm V) :
    permutationCommutationDefect σ (p * q) ≤
      permutationCommutationDefect σ p + permutationCommutationDefect σ q := by
  classical
  unfold permutationCommutationDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  let Bp : Finset V :=
    Finset.univ.filter fun x => p (σ i x) ≠ σ i (p x)
  let Bq : Finset V :=
    Finset.univ.filter fun x => q (σ i x) ≠ σ i (q x)
  let C : Finset V :=
    Finset.univ.filter fun x => q x ∈ Bp
  have hC : C.card = Bp.card := by
    apply Finset.card_bij (fun x _ => q x)
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy hxy
      exact q.injective hxy
    · intro y hy
      refine ⟨q.symm y, ?_, by simp⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simpa using hy⟩
  have hsub :
      (Finset.univ.filter fun x =>
        (p * q) (σ i x) ≠ σ i ((p * q) x)) ⊆ Bq ∪ C := by
    intro x hx
    have hbad := (Finset.mem_filter.mp hx).2
    by_cases hq : q (σ i x) = σ i (q x)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hp
      apply hbad
      simpa [Equiv.Perm.mul_apply, hq] using hp
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
  calc
    (Finset.univ.filter fun x =>
      (p * q) (σ i x) ≠ σ i ((p * q) x)).card ≤
        (Bq ∪ C).card := Finset.card_le_card hsub
    _ ≤ Bq.card + C.card := Finset.card_union_le Bq C
    _ = Bp.card + Bq.card := by rw [hC, Nat.add_comm]
structure AlmostCentralizerElement {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) where
  permutation : Equiv.Perm V
  defect_le : permutationCommutationDefect σ permutation ≤ tolerance
@[ext (iff := false)]
theorem AlmostCentralizerElement.ext {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (p q : AlmostCentralizerElement σ tolerance)
    (h : p.permutation = q.permutation) : p = q := by
  cases p with
  | mk p hp =>
    cases q with
    | mk q hq =>
      cases h
      rfl
instance almostCentralizerElementFinite {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) :
    Finite (AlmostCentralizerElement σ tolerance) :=
  Finite.of_injective (fun p => p.permutation)
    (fun p q hpq => AlmostCentralizerElement.ext p q hpq)
structure AlmostCentralizerGap {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) : Prop where
  dichotomy : ∀ p q : AlmostCentralizerElement σ tolerance,
    5 * permutationDistance p.permutation q.permutation ≤ Fintype.card V ∨
      4 * Fintype.card V <
        5 * permutationDistance p.permutation q.permutation
def almostCentralizerSetoid {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ)
    (hgap : AlmostCentralizerGap σ tolerance) :
    Setoid (AlmostCentralizerElement σ tolerance) where
  r p q := 5 * permutationDistance p.permutation q.permutation ≤ Fintype.card V
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      simp
    · intro p q hpq
      simpa [permutationDistance_comm q.permutation p.permutation] using hpq
    · intro p q r hpq hqr
      rcases hgap.dichotomy p r with hclose | hfar
      · exact hclose
      · have htri := permutationDistance_triangle
          p.permutation q.permutation r.permutation
        omega
abbrev AlmostCentralizerClusters {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ)
    (hgap : AlmostCentralizerGap σ tolerance) :=
  Quotient (almostCentralizerSetoid σ tolerance hgap)
def almostCentralizerCluster {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (p : AlmostCentralizerElement σ tolerance) :
    AlmostCentralizerClusters σ tolerance hgap :=
  Quotient.mk (almostCentralizerSetoid σ tolerance hgap) p
structure AlmostCentralizerRepair {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) where
  correct : Equiv.Perm V → Equiv.Perm V
  corrected_defect : ∀ p q : AlmostCentralizerElement σ tolerance,
    permutationCommutationDefect σ
      (correct (p.permutation * q.permutation)) ≤ tolerance
  corrected_distance : ∀ p q : AlmostCentralizerElement σ tolerance,
    5 * permutationDistance
      (correct (p.permutation * q.permutation))
      (p.permutation * q.permutation) ≤ Fintype.card V
structure HasAlmostCentralizerImprovement {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) : Prop where
  improve : ∀ p : Equiv.Perm V,
    permutationCommutationDefect σ p ≤ 2 * tolerance →
      ∃ q : Equiv.Perm V,
        permutationCommutationDefect σ q ≤ tolerance ∧
          5 * permutationDistance q p ≤ Fintype.card V
def almostCentralizerRepairOfImprovement {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (h : HasAlmostCentralizerImprovement σ tolerance) :
    AlmostCentralizerRepair σ tolerance := by
  classical
  let correction : Equiv.Perm V → Equiv.Perm V := fun p =>
    if hp : permutationCommutationDefect σ p ≤ 2 * tolerance then
      (h.improve p hp).choose
    else p
  refine ⟨correction, ?_, ?_⟩
  · intro p q
    have hprod := permutationCommutationDefect_mul_le σ
      p.permutation q.permutation
    have hp := p.defect_le
    have hq := q.defect_le
    have hgood : permutationCommutationDefect σ
        (p.permutation * q.permutation) ≤ 2 * tolerance := by
      omega
    change permutationCommutationDefect σ
      (correction (p.permutation * q.permutation)) ≤ tolerance
    simpa [correction, hgood] using
      (h.improve (p.permutation * q.permutation) hgood).choose_spec.1
  · intro p q
    have hprod := permutationCommutationDefect_mul_le σ
      p.permutation q.permutation
    have hp := p.defect_le
    have hq := q.defect_le
    have hgood : permutationCommutationDefect σ
        (p.permutation * q.permutation) ≤ 2 * tolerance := by
      omega
    change 5 * permutationDistance
      (correction (p.permutation * q.permutation))
      (p.permutation * q.permutation) ≤ Fintype.card V
    simpa [correction, hgood] using
      (h.improve (p.permutation * q.permutation) hgood).choose_spec.2
def correctedAlmostCentralizerProduct {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (R : AlmostCentralizerRepair σ tolerance)
    (p q : AlmostCentralizerElement σ tolerance) :
    AlmostCentralizerElement σ tolerance :=
  ⟨R.correct (p.permutation * q.permutation), R.corrected_defect p q⟩
theorem correctedAlmostCentralizerProduct_congr {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (R : AlmostCentralizerRepair σ tolerance)
    {p p' q q' : AlmostCentralizerElement σ tolerance}
    (hp : 5 * permutationDistance p.permutation p'.permutation ≤
      Fintype.card V)
    (hq : 5 * permutationDistance q.permutation q'.permutation ≤
      Fintype.card V) :
    5 * permutationDistance
      (correctedAlmostCentralizerProduct R p q).permutation
      (correctedAlmostCentralizerProduct R p' q').permutation ≤
        Fintype.card V := by
  let a := correctedAlmostCentralizerProduct R p q
  let b := correctedAlmostCentralizerProduct R p' q'
  have ha := R.corrected_distance p q
  have hb := R.corrected_distance p' q'
  have hmul := permutationDistance_mul_le
    p.permutation p'.permutation q.permutation q'.permutation
  have htri₁ := permutationDistance_triangle a.permutation
    (p.permutation * q.permutation) b.permutation
  have htri₂ := permutationDistance_triangle
    (p.permutation * q.permutation)
    (p'.permutation * q'.permutation) b.permutation
  have hsym :
      permutationDistance (p'.permutation * q'.permutation) b.permutation =
        permutationDistance b.permutation
          (p'.permutation * q'.permutation) :=
    permutationDistance_comm _ _
  change 5 * permutationDistance a.permutation b.permutation ≤
    Fintype.card V
  rcases hgap.dichotomy a b with hclose | hfar
  · exact hclose
  · change 4 * Fintype.card V <
      5 * permutationDistance a.permutation b.permutation at hfar
    change 5 * permutationDistance a.permutation
      (p.permutation * q.permutation) ≤ Fintype.card V at ha
    change 5 * permutationDistance b.permutation
      (p'.permutation * q'.permutation) ≤ Fintype.card V at hb
    omega
def almostCentralizerClusterMul {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (R : AlmostCentralizerRepair σ tolerance) :
    AlmostCentralizerClusters σ tolerance hgap →
      AlmostCentralizerClusters σ tolerance hgap →
        AlmostCentralizerClusters σ tolerance hgap :=
  Quotient.map₂ (correctedAlmostCentralizerProduct R)
    (fun _ _ hp _ _ hq =>
      correctedAlmostCentralizerProduct_congr hgap R hp hq)
def almostCentralizerOne {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) :
    AlmostCentralizerElement σ tolerance :=
  ⟨1, by simp⟩
def almostCentralizerInverse {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (p : AlmostCentralizerElement σ tolerance) :
    AlmostCentralizerElement σ tolerance :=
  ⟨p.permutation⁻¹, by
    rw [permutationCommutationDefect_inv]
    exact p.defect_le⟩
def almostCentralizerClusterInv {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance) :
    AlmostCentralizerClusters σ tolerance hgap →
      AlmostCentralizerClusters σ tolerance hgap :=
  Quotient.map almostCentralizerInverse (by
    intro p q hpq
    change 5 * permutationDistance p.permutation⁻¹ q.permutation⁻¹ ≤
      Fintype.card V
    rwa [permutationDistance_inv])
theorem correctedAlmostCentralizerProduct_assoc {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (R : AlmostCentralizerRepair σ tolerance)
    (p q r : AlmostCentralizerElement σ tolerance) :
    5 * permutationDistance
      (correctedAlmostCentralizerProduct R
        (correctedAlmostCentralizerProduct R p q) r).permutation
      (correctedAlmostCentralizerProduct R p
        (correctedAlmostCentralizerProduct R q r)).permutation ≤
        Fintype.card V := by
  let a := correctedAlmostCentralizerProduct R p q
  let b := correctedAlmostCentralizerProduct R q r
  let l := correctedAlmostCentralizerProduct R a r
  let t := correctedAlmostCentralizerProduct R p b
  have hl := R.corrected_distance a r
  have ht := R.corrected_distance p b
  have ha := R.corrected_distance p q
  have hb := R.corrected_distance q r
  have ha' :
      5 * permutationDistance
        (a.permutation * r.permutation)
        ((p.permutation * q.permutation) * r.permutation) ≤
          Fintype.card V := by
    rw [permutationDistance_mul_right]
    exact ha
  have hb' :
      5 * permutationDistance
        ((p.permutation * q.permutation) * r.permutation)
        (p.permutation * b.permutation) ≤ Fintype.card V := by
    rw [mul_assoc, permutationDistance_mul_left,
      permutationDistance_comm]
    exact hb
  have ht' :
      5 * permutationDistance
        (p.permutation * b.permutation) t.permutation ≤
          Fintype.card V := by
    rw [permutationDistance_comm]
    exact ht
  have htri₁ := permutationDistance_triangle l.permutation
    (a.permutation * r.permutation) t.permutation
  have htri₂ := permutationDistance_triangle
    (a.permutation * r.permutation)
    ((p.permutation * q.permutation) * r.permutation) t.permutation
  have htri₃ := permutationDistance_triangle
    ((p.permutation * q.permutation) * r.permutation)
    (p.permutation * b.permutation) t.permutation
  change 5 * permutationDistance l.permutation t.permutation ≤
    Fintype.card V
  rcases hgap.dichotomy l t with hclose | hfar
  · exact hclose
  · change 4 * Fintype.card V <
      5 * permutationDistance l.permutation t.permutation at hfar
    change 5 * permutationDistance l.permutation
      (a.permutation * r.permutation) ≤ Fintype.card V at hl
    omega
@[instance_reducible]
def almostCentralizerClusterGroup {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (R : AlmostCentralizerRepair σ tolerance) :
    Group (AlmostCentralizerClusters σ tolerance hgap) := by
  letI : One (AlmostCentralizerClusters σ tolerance hgap) :=
    ⟨almostCentralizerCluster hgap (almostCentralizerOne σ tolerance)⟩
  letI : Mul (AlmostCentralizerClusters σ tolerance hgap) :=
    ⟨almostCentralizerClusterMul hgap R⟩
  letI : Inv (AlmostCentralizerClusters σ tolerance hgap) :=
    ⟨almostCentralizerClusterInv hgap⟩
  apply Group.ofLeftAxioms
  · intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ p q r =>
      apply Quotient.sound
      exact correctedAlmostCentralizerProduct_assoc hgap R p q r
  · intro x
    induction x using Quotient.inductionOn with
    | _ p =>
      apply Quotient.sound
      change 5 * permutationDistance
        (R.correct (1 * p.permutation)) p.permutation ≤ Fintype.card V
      simpa [almostCentralizerOne] using
        R.corrected_distance (almostCentralizerOne σ tolerance) p
  · intro x
    induction x using Quotient.inductionOn with
    | _ p =>
      apply Quotient.sound
      change 5 * permutationDistance
        (R.correct (p.permutation⁻¹ * p.permutation)) 1 ≤ Fintype.card V
      simpa [almostCentralizerInverse] using
        R.corrected_distance (almostCentralizerInverse p) p
structure ExpandingCentralizerFiniteModel (G : Type*) [Group G]
    (F : Finset G) where
  vertices : Type
  [verticesFintype : Fintype vertices]
  [verticesDecidableEq : DecidableEq vertices]
  generatorIndex : Type
  [generatorFintype : Fintype generatorIndex]
  generators : generatorIndex → Equiv.Perm vertices
  tolerance : ℕ
  cheeger : ℝ
  cheeger_positive : 0 < cheeger
  expansion : ∀ A : Finset vertices,
    cheeger * min (A.card : ℝ)
        ((Fintype.card vertices : ℝ) - A.card) ≤
      (boundary generators A : ℝ)
  small : (10 : ℝ) * tolerance < cheeger * Fintype.card vertices
  repair : AlmostCentralizerRepair generators tolerance
  approximation : G → AlmostCentralizerElement generators tolerance
  map_one : (approximation 1).permutation = 1
  multiplicative : ∀ x ∈ F, ∀ y ∈ F,
    5 * permutationDistance (approximation (x * y)).permutation
      ((approximation x).permutation * (approximation y).permutation) ≤
        Fintype.card vertices
  separated : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
    Fintype.card vertices <
      5 * permutationDistance
        (approximation x).permutation (approximation y).permutation
instance expandingCentralizerFiniteModelVerticesFintype
    {G : Type*} [Group G] {F : Finset G}
    (M : ExpandingCentralizerFiniteModel G F) : Fintype M.vertices :=
  M.verticesFintype
instance expandingCentralizerFiniteModelVerticesDecidableEq
    {G : Type*} [Group G] {F : Finset G}
    (M : ExpandingCentralizerFiniteModel G F) : DecidableEq M.vertices :=
  M.verticesDecidableEq
instance expandingCentralizerFiniteModelGeneratorFintype
    {G : Type*} [Group G] {F : Finset G}
    (M : ExpandingCentralizerFiniteModel G F) : Fintype M.generatorIndex :=
  M.generatorFintype
def expandingCentralizerFiniteModelOfImprovement
    {G : Type*} [Group G] (F : Finset G)
    {V ι : Type} [Fintype V] [DecidableEq V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) (h : ℝ)
    (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤ (boundary σ A : ℝ))
    (hsmall : (10 : ℝ) * tolerance < h * Fintype.card V)
    (himprove : HasAlmostCentralizerImprovement σ tolerance)
    (f : G → AlmostCentralizerElement σ tolerance)
    (hone : (f 1).permutation = 1)
    (hmul : ∀ x ∈ F, ∀ y ∈ F,
      5 * permutationDistance (f (x * y)).permutation
        ((f x).permutation * (f y).permutation) ≤ Fintype.card V)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Fintype.card V < 5 * permutationDistance
        (f x).permutation (f y).permutation) :
    ExpandingCentralizerFiniteModel G F where
  vertices := V
  verticesFintype := inferInstance
  verticesDecidableEq := inferInstance
  generatorIndex := ι
  generatorFintype := inferInstance
  generators := σ
  tolerance := tolerance
  cheeger := h
  cheeger_positive := hpositive
  expansion := hexp
  small := hsmall
  repair := almostCentralizerRepairOfImprovement himprove
  approximation := f
  map_one := hone
  multiplicative := hmul
  separated := hsep
namespace ExceptionalRankOffset
open Filter Topology
open scoped BigOperators
end ExceptionalRankOffset
namespace ThompsonPrefixInsertion
end ThompsonPrefixInsertion
universe u₁ u₂ u₃
section ElementaryRingQuotient
variable {ι : Type u₁} {R : Type u₂} {S : Type u₃}
  [Fintype ι] [DecidableEq ι]
  [Ring R] [Ring S]
def elementaryMatrixUnitMap (f : R →+* S) :
    (Matrix ι ι R)ˣ →* (Matrix ι ι S)ˣ :=
  Units.map f.mapMatrix.toMonoidHom
theorem elementaryMatrixUnitMap_elementaryUnit
    (f : R →+* S) (i j : ι) (hij : i ≠ j) (a : R) :
    elementaryMatrixUnitMap f (elementaryUnit i j hij a) =
      elementaryUnit i j hij (f a) := by
  apply Units.ext
  change f.mapMatrix (1 + Matrix.single i j a) =
    1 + Matrix.single i j (f a)
  rw [map_add, map_one]
  congr 1
  ext k l
  change f (if i = k ∧ j = l then a else 0) =
    if i = k ∧ j = l then f a else 0
  split_ifs <;> simp
theorem elementaryGroup_map_le (f : R →+* S) :
    (elementaryGroup ι R).map (elementaryMatrixUnitMap f) ≤
      elementaryGroup ι S := by
  rw [Subgroup.map_le_iff_le_comap, elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  change elementaryMatrixUnitMap f (elementaryUnit i j hij a) ∈
    elementaryGroup ι S
  rw [elementaryMatrixUnitMap_elementaryUnit]
  exact elementaryUnit_mem i j hij (f a)
theorem elementaryGroup_map_eq_of_surjective
    (f : R →+* S) (hf : Function.Surjective f) :
    (elementaryGroup ι R).map (elementaryMatrixUnitMap f) =
      elementaryGroup ι S := by
  apply le_antisymm (elementaryGroup_map_le f)
  rw [elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, b, rfl⟩
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨elementaryUnit i j hij a,
    elementaryUnit_mem i j hij a, ?_⟩
  exact elementaryMatrixUnitMap_elementaryUnit f i j hij a
end ElementaryRingQuotient
def binaryPrefixElementaryGroupEquiv
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    elementaryGroup ι BinaryLeavitt ≃* prefixElementaryGroup E :=
  ((elementaryGroup ι BinaryLeavitt).equivMapOfInjective
      (prefixCornerUnitHom E) (prefixCornerUnitHom_injective E)).trans
    (MulEquiv.subgroupCongr (prefixCornerElementaryGroup_map E))
namespace CompressionCriterion
open Filter Topology
def productTrackedTable {J : Type*} [Group J]
    (F : Finset J) : Finset J := by
  classical
  exact SoficGroups.multiplicationTable (insert 1 F)
end CompressionCriterion
def permutationGraph {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) : Finset (V × V) :=
  Finset.univ.image fun x => (x, p x)
namespace ThompsonPrefixInsertion
open scoped commutatorElement
structure PrefixWordAction (g : BinaryLeavittˣ)
    (a b : List (Fin 2)) : Prop where
  prefixing : (↑g : BinaryLeavitt) * leavittWordS a = leavittWordS b
  deletion :
    leavittWordT a * (↑(g⁻¹) : BinaryLeavitt) = leavittWordT b
theorem prefixInsertionHom_mem_binaryPrefixTranspositionGroup
    (a : List (Fin 2)) (u : BinaryLeavittˣ)
    (hu : u ∈ binaryPrefixTranspositionGroup) :
    prefixInsertionHom a u ∈ binaryPrefixTranspositionGroup := by
  have hle :
      binaryPrefixTranspositionGroup ≤
        binaryPrefixTranspositionGroup.comap (prefixInsertionHom a) := by
    change Subgroup.closure _ ≤ _
    apply (Subgroup.closure_le _).2
    rintro _ ⟨x, y, hxy, hyx, rfl⟩
    change prefixInsertionHom a (cylinderSwap x y hxy hyx) ∈
      binaryPrefixTranspositionGroup
    rw [prefixInsertionHom_cylinderSwap]
    exact Subgroup.subset_closure
      ⟨a ++ x, a ++ y,
        prepend_not_prefix_prepend a x y hxy,
        prepend_not_prefix_prepend a y x hyx, rfl⟩
  exact hle hu
end ThompsonPrefixInsertion
namespace LeavittElementaryMorita
open scoped BigOperators commutatorElement
section ElementaryBlockFlattening
variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Ring R]
def elementaryBlockMatrixEquiv :
    Matrix ι ι (Matrix κ κ R) ≃+*
      Matrix (ι × κ) (ι × κ) R :=
  Matrix.compRingEquiv ι κ R
def elementaryBlockUnitEquiv :
    (Matrix ι ι (Matrix κ κ R))ˣ ≃*
      (Matrix (ι × κ) (ι × κ) R)ˣ :=
  Units.mapEquiv (elementaryBlockMatrixEquiv (ι := ι)
    (κ := κ) (R := R)).toMulEquiv
theorem elementaryBlockUnitEquiv_elementaryUnit_single
    (i j : ι) (hij : i ≠ j) (k l : κ) (a : R) :
    elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)
        (elementaryUnit i j hij (Matrix.single k l a)) =
      elementaryUnit (i, k) (j, l)
        (fun h => hij (congrArg Prod.fst h)) a := by
  apply Units.ext
  change
    elementaryBlockMatrixEquiv (ι := ι) (κ := κ) (R := R)
        (1 + Matrix.single i j (Matrix.single k l a)) =
      1 + Matrix.single (i, k) (j, l) a
  rw [map_add, map_one]
  congr 1
  exact Matrix.comp_single_single i j k l a
theorem elementaryBlockUnitEquiv_elementaryUnit_mem
    (i j : ι) (hij : i ≠ j) (A : Matrix κ κ R) :
    elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)
        (elementaryUnit i j hij A) ∈
      elementaryGroup (ι × κ) R := by
  induction A using Matrix.induction_on' with
  | h_zero =>
      simp [elementaryUnit_zero]
  | h_add A B hA hB =>
      rw [← elementaryUnit_mul, map_mul]
      exact (elementaryGroup (ι × κ) R).mul_mem hA hB
  | h_std_basis k l a =>
      rw [elementaryBlockUnitEquiv_elementaryUnit_single i j hij k l a]
      exact elementaryUnit_mem (i, k) (j, l)
        (fun h => hij (congrArg Prod.fst h)) a
theorem elementaryBlockGroup_map [Nontrivial ι] :
    (elementaryGroup ι (Matrix κ κ R)).map
        (elementaryBlockUnitEquiv
          (ι := ι) (κ := κ) (R := R)).toMonoidHom =
      elementaryGroup (ι × κ) R := by
  let B : Subgroup (Matrix (ι × κ) (ι × κ) R)ˣ :=
    (elementaryGroup ι (Matrix κ κ R)).map
      (elementaryBlockUnitEquiv
        (ι := ι) (κ := κ) (R := R)).toMonoidHom
  have hcross (i j : ι) (hij : i ≠ j) (k l : κ) (a : R) :
      elementaryUnit (i, k) (j, l)
          (fun h => hij (congrArg Prod.fst h)) a ∈ B := by
    refine ⟨elementaryUnit i j hij (Matrix.single k l a),
      elementaryUnit_mem i j hij (Matrix.single k l a), ?_⟩
    exact elementaryBlockUnitEquiv_elementaryUnit_single
      i j hij k l a
  change B = elementaryGroup (ι × κ) R
  apply le_antisymm
  · change
      (elementaryGroup ι (Matrix κ κ R)).map
          (elementaryBlockUnitEquiv
            (ι := ι) (κ := κ) (R := R)).toMonoidHom ≤
        elementaryGroup (ι × κ) R
    rw [elementaryGroup, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, hij, A, rfl⟩, rfl⟩
    change
      elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)
          (elementaryUnit i j hij A) ∈
        elementaryGroup (ι × κ) R
    exact elementaryBlockUnitEquiv_elementaryUnit_mem
      i j hij A
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, k⟩, ⟨j, l⟩, hne, a, rfl⟩
    by_cases hij : i = j
    · subst j
      obtain ⟨j, hji⟩ := exists_ne i
      exact elementaryUnit_mem_of_two_step B
        (i, k) (j, k) (i, l)
        (fun h => hji (congrArg Prod.fst h).symm)
        (fun h => hji (congrArg Prod.fst h))
        hne a
        (hcross i j hji.symm k k a)
        (hcross j i hji k l 1)
    · exact hcross i j hij k l a
def elementaryBlockGroupEquiv [Nontrivial ι] :
    elementaryGroup ι (Matrix κ κ R) ≃*
      elementaryGroup (ι × κ) R :=
  ((elementaryBlockUnitEquiv
      (ι := ι) (κ := κ) (R := R)).subgroupMap
    (elementaryGroup ι (Matrix κ κ R))).trans
    (MulEquiv.subgroupCongr
      (elementaryBlockGroup_map (ι := ι) (κ := κ) (R := R)))
end ElementaryBlockFlattening
section ElementaryReindexing
variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Ring R]
def elementaryReindexUnitEquiv (e : ι ≃ κ) :
    (Matrix ι ι R)ˣ ≃* (Matrix κ κ R)ˣ :=
  Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv
theorem elementaryReindexUnitEquiv_elementaryUnit
    (e : ι ≃ κ) (i j : ι) (hij : i ≠ j) (a : R) :
    elementaryReindexUnitEquiv (R := R) e
        (elementaryUnit i j hij a) =
      elementaryUnit (e i) (e j) (e.injective.ne hij) a := by
  apply Units.ext
  change
    (Matrix.reindexRingEquiv R e)
        (1 + Matrix.single i j a) =
      1 + Matrix.single (e i) (e j) a
  rw [map_add, map_one]
  congr 1
  change
    Matrix.reindex e e (Matrix.single i j a) =
      Matrix.single (e i) (e j) a
  simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
    (Matrix.submatrix_single_equiv e.symm e.symm i j a)
theorem elementaryReindexGroup_map (e : ι ≃ κ) :
    (elementaryGroup ι R).map
        (elementaryReindexUnitEquiv (R := R) e).toMonoidHom =
      elementaryGroup κ R := by
  apply le_antisymm
  · rw [elementaryGroup, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, hij, a, rfl⟩, rfl⟩
    change
      elementaryReindexUnitEquiv (R := R) e
          (elementaryUnit i j hij a) ∈ elementaryGroup κ R
    rw [elementaryReindexUnitEquiv_elementaryUnit]
    exact elementaryUnit_mem (e i) (e j) (e.injective.ne hij) a
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨k, l, hkl, a, rfl⟩
    have hij : e.symm k ≠ e.symm l := e.symm.injective.ne hkl
    refine ⟨elementaryUnit (e.symm k) (e.symm l) hij a,
      elementaryUnit_mem (e.symm k) (e.symm l) hij a, ?_⟩
    simpa using elementaryReindexUnitEquiv_elementaryUnit
      e (e.symm k) (e.symm l) hij a
def elementaryReindexGroupEquiv (e : ι ≃ κ) :
    elementaryGroup ι R ≃* elementaryGroup κ R :=
  ((elementaryReindexUnitEquiv (R := R) e).subgroupMap
    (elementaryGroup ι R)).trans
    (MulEquiv.subgroupCongr (elementaryReindexGroup_map e))
end ElementaryReindexing
section ElementaryCoefficientEquivalence
variable {ι R S : Type*} [Fintype ι] [DecidableEq ι]
  [Ring R] [Ring S]
def elementaryCoefficientGroupEquiv (f : R ≃+* S) :
    elementaryGroup ι R ≃* elementaryGroup ι S :=
  ((Units.mapEquiv f.mapMatrix.toMulEquiv).subgroupMap
    (elementaryGroup ι R)).trans
    (MulEquiv.subgroupCongr (by
      change
        (elementaryGroup ι R).map
          (elementaryMatrixUnitMap f.toRingHom) =
            elementaryGroup ι S
      exact elementaryGroup_map_eq_of_surjective
        f.toRingHom f.surjective))
end ElementaryCoefficientEquivalence
def ternaryLeavittWord : Fin 3 → List (Fin 2)
  | 0 => [0, 0]
  | 1 => [0, 1]
  | _ => [1]
def ternaryLeavittPrefixCode : BinaryPrefixCode (Fin 3) where
  word := ternaryLeavittWord
  prefix_free := by decide
theorem ternaryLeavittPrefixCode_complete :
    MatrixCorner.codeIdempotent
        (fun i => leavittWordS (ternaryLeavittPrefixCode.word i))
        (fun i => leavittWordT (ternaryLeavittPrefixCode.word i)) =
      1 := by
  have hzero :
      leavittCylinder [0, 0] + leavittCylinder [0, 1] =
        leavittCylinder [0] := by
    simpa using (leavittCylinder_split [0]).symm
  have hroot :
      leavittCylinder [0] + leavittCylinder [1] = 1 := by
    simpa [leavittCylinder, leavittWordS, leavittWordT] using
      (leavittCylinder_split ([] : List (Fin 2))).symm
  have hsum :
      leavittCylinder [0, 0] + leavittCylinder [0, 1] +
          leavittCylinder [1] = 1 := by
    rw [hzero]
    exact hroot
  simpa [MatrixCorner.codeIdempotent, ternaryLeavittPrefixCode,
    ternaryLeavittWord, leavittCylinder, Fin.sum_univ_succ,
    add_assoc] using hsum
def binaryLeavittMatrixThreeEquiv :
    BinaryLeavitt ≃+* Matrix (Fin 3) (Fin 3) BinaryLeavitt :=
  (completePrefixMatrixEquiv ternaryLeavittPrefixCode
    ternaryLeavittPrefixCode_complete).symm
def binaryLeavittElementaryThreeEquivNine :
    binaryLeavittElementaryGroup 3 ≃*
      binaryLeavittElementaryGroup 9 :=
  (elementaryCoefficientGroupEquiv
    (ι := Fin 3) binaryLeavittMatrixThreeEquiv).trans
    ((elementaryBlockGroupEquiv
      (ι := Fin 3) (κ := Fin 3) (R := BinaryLeavitt)).trans
      (elementaryReindexGroupEquiv
        (R := BinaryLeavitt) (finProdFinEquiv :
          Fin 3 × Fin 3 ≃ Fin 9)))
end LeavittElementaryMorita
namespace ThompsonFiniteGeneration
open ThompsonPrefixInsertion
end ThompsonFiniteGeneration
end
section
open Filter Topology
section ThreeProjectionSumOfSquares
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end ThreeProjectionSumOfSquares
section TwoOrthogonalSectors
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end TwoOrthogonalSectors
section ThreeOrthogonalProjections
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
def ejResidualProjection (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] : H →L[ℂ] H :=
  Vᗮ.starProjection
@[simp]
theorem ejResidualProjection_apply (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] (x : H) :
    ejResidualProjection V x = x - V.starProjection x :=
  Submodule.starProjection_orthogonal_val x
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
def ejThreeResidualMap : H →L[ℂ] H :=
  ejResidualProjection (V 0) + ejResidualProjection (V 1) +
    ejResidualProjection (V 2)
def ejThreeResidualEnergy (x : H) : ℝ :=
  ‖ejResidualProjection (V 0) x‖ ^ 2 +
    ‖ejResidualProjection (V 1) x‖ ^ 2 +
    ‖ejResidualProjection (V 2) x‖ ^ 2
def ejThreeProjectionAverage : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H -
    (3 : ℂ)⁻¹ • ejThreeResidualMap V
@[simp]
theorem ejThreeResidualMap_apply (x : H) :
    ejThreeResidualMap V x =
      ejResidualProjection (V 0) x +
        ejResidualProjection (V 1) x +
        ejResidualProjection (V 2) x := by
  rfl
@[simp]
theorem ejThreeProjectionAverage_apply (x : H) :
    ejThreeProjectionAverage V x =
      x - (3 : ℂ)⁻¹ • ejThreeResidualMap V x := by
  rfl
end ThreeOrthogonalProjections
section ThreeFiniteUnitaryFixedSpaces
universe u₂ v₂
def ejUnitaryFixedSubmodule
    {G : Type u₂} {H : Type v₂} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) :
    Submodule ℂ H where
  carrier := {x : H | ∀ k : K, π (k : G) x = x}
  zero_mem' k := by simp
  add_mem' hx hy k := by
    simp [map_add, hx k, hy k]
  smul_mem' c x hx k := by
    simp [map_smul, hx k]
@[simp]
theorem mem_ejUnitaryFixedSubmodule
    {G : Type u₂} {H : Type v₂} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) (x : H) :
    x ∈ ejUnitaryFixedSubmodule π K ↔
      ∀ k : K, π (k : G) x = x :=
  Iff.rfl
theorem ejUnitaryFixedSubmodule_isClosed
    {G : Type u₂} {H : Type v₂} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) :
    IsClosed (ejUnitaryFixedSubmodule π K : Set H) := by
  have hset :
      (ejUnitaryFixedSubmodule π K : Set H) =
        ⋂ k : K, {x : H | π (k : G) x = x} := by
    ext x
    simp
  rw [hset]
  exact isClosed_iInter fun k =>
    isClosed_eq (π (k : G)).continuous continuous_id
theorem ejUnitaryFixedSubmodule_inf_isClosed
    {G : Type u₂} {H : Type v₂} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K J : Subgroup G) :
    IsClosed
      ((ejUnitaryFixedSubmodule π K ⊓
        ejUnitaryFixedSubmodule π J : Submodule ℂ H) : Set H) := by
  change IsClosed
    ((ejUnitaryFixedSubmodule π K : Set H) ∩
      (ejUnitaryFixedSubmodule π J : Set H))
  exact (ejUnitaryFixedSubmodule_isClosed π K).inter
    (ejUnitaryFixedSubmodule_isClosed π J)
instance ejUnitaryFixedSubmodule_completeSpace
    {G : Type u₂} {H : Type v₂} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) :
    CompleteSpace (ejUnitaryFixedSubmodule π K) :=
  (ejUnitaryFixedSubmodule_isClosed π K).isComplete.completeSpace_coe
instance ejUnitaryFixedSubmodule_inf_completeSpace
    {G : Type u₂} {H : Type v₂} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K J : Subgroup G) :
    CompleteSpace
      (↑(ejUnitaryFixedSubmodule π K ⊓
        ejUnitaryFixedSubmodule π J : Submodule ℂ H) : Type v₂) :=
  (ejUnitaryFixedSubmodule_inf_isClosed π K J).isComplete.completeSpace_coe
end ThreeFiniteUnitaryFixedSpaces
end
namespace ErshovJaikinFiniteSpectral
open Filter Topology
universe u v
section FiniteUnitaryAveraging
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def finiteUnitarySubgroupAverage
    (π : SoficGroups.UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K] (x : H) : H :=
  (Fintype.card K : ℂ)⁻¹ • ∑ k : K, π (k : G) x
end FiniteUnitaryAveraging
def threeFiniteSubgroupGenerators
    {G : Type u} [Group G] (K : Fin 3 → Subgroup G)
    [∀ i, Fintype (K i)] : Finset G := by
  classical
  exact Finset.univ.biUnion fun i : Fin 3 =>
    Finset.univ.image fun g : K i => (g : G)
def unitaryVectorStabilizer
    {G : Type u} {H : Type v} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : SoficGroups.UnitaryRepresentation G H)
    (x : H) : Subgroup G where
  carrier := {g : G | π g x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change π g x = x at hg
    change π h x = x at hh
    change π (g * h) x = x
    simpa [map_mul, hh] using hg
  inv_mem' := by
    intro g hg
    change π g x = x at hg
    change π g⁻¹ x = x
    have h := congrArg (fun z : H => π g⁻¹ z) hg
    simpa [← map_mul] using h.symm
end ErshovJaikinFiniteSpectral
section
open scoped BigOperators commutatorElement
abbrev finiteBlockGaloisField : Type := GaloisField 2 3
def finiteBlockGaloisBasis :
    Module.Basis (Fin 3) (ZMod 2) finiteBlockGaloisField :=
  Module.finBasisOfFinrankEq (ZMod 2) finiteBlockGaloisField
    (GaloisField.finrank 2 (by decide))
def finiteBlockGaloisMatrix :
    finiteBlockGaloisField →ₐ[ZMod 2]
      Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Algebra.leftMulMatrix finiteBlockGaloisBasis
def finiteBlockGaloisMatrixOver (R : Type*) [Ring R]
    [Algebra (ZMod 2) R] :
    finiteBlockGaloisField →+* Matrix (Fin 3) (Fin 3) R :=
  (RingHom.mapMatrix (algebraMap (ZMod 2) R)).comp
    finiteBlockGaloisMatrix.toRingHom
section ActualBlockRoots
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
theorem finiteBlockCoefficientMatrix_mul_binary_mem
    (W : Submodule (ZMod 2) R)
    (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ i j, A i j ∈ W)
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    ∀ i j,
      (A * RingHom.mapMatrix (algebraMap (ZMod 2) R) B) i j ∈ W := by
  intro i j
  rw [Matrix.mul_apply]
  apply Submodule.sum_mem
  intro k _
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [← Algebra.commutes, ← Algebra.smul_def]
  exact W.smul_mem (B k j) (hA i k)
theorem finiteBlockCoefficientMatrix_binary_mul_mem
    (W : Submodule (ZMod 2) R)
    (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ i j, A i j ∈ W)
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    ∀ i j,
      (RingHom.mapMatrix (algebraMap (ZMod 2) R) B * A) i j ∈ W := by
  intro i j
  rw [Matrix.mul_apply]
  apply Submodule.sum_mem
  intro k _
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← Algebra.smul_def]
  exact W.smul_mem (B i k) (hA k j)
theorem finiteBlockCoefficientMatrix_mul_galois_mem
    (W : Submodule (ZMod 2) R)
    (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ i j, A i j ∈ W)
    (t : finiteBlockGaloisField) :
    ∀ i j, (A * finiteBlockGaloisMatrixOver R t) i j ∈ W := by
  change ∀ i j,
    (A * RingHom.mapMatrix (algebraMap (ZMod 2) R)
      (finiteBlockGaloisMatrix t)) i j ∈ W
  exact finiteBlockCoefficientMatrix_mul_binary_mem W A hA
    (finiteBlockGaloisMatrix t)
theorem finiteBlockCoefficientMatrix_galois_mul_mem
    (W : Submodule (ZMod 2) R)
    (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ i j, A i j ∈ W)
    (t : finiteBlockGaloisField) :
    ∀ i j, (finiteBlockGaloisMatrixOver R t * A) i j ∈ W := by
  change ∀ i j,
    (RingHom.mapMatrix (algebraMap (ZMod 2) R)
      (finiteBlockGaloisMatrix t) * A) i j ∈ W
  exact finiteBlockCoefficientMatrix_binary_mul_mem W A hA
    (finiteBlockGaloisMatrix t)
def finiteBlockCoefficientMatrixHom
    (W : Submodule (ZMod 2) R) :
    Matrix (Fin 3) (Fin 3) W →+
      Matrix (Fin 3) (Fin 3) R :=
  W.subtype.toAddMonoidHom.mapMatrix
def finiteOuterBlockRootHom
    (W : Submodule (ZMod 2) R) (i j : Fin 3) (hij : i ≠ j) :
    Multiplicative (Matrix (Fin 3) (Fin 3) W) →*
      elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
  (elementaryRootHom (R := Matrix (Fin 3) (Fin 3) R) i j hij).comp
    (finiteBlockCoefficientMatrixHom W).toMultiplicative
def finiteOuterBlockRootSubgroup
    (W : Submodule (ZMod 2) R) (i j : Fin 3) (hij : i ≠ j) :
    Subgroup (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) :=
  (finiteOuterBlockRootHom W i j hij).range
def finiteBlockCoefficientMatrixRightMul
    (W : Submodule (ZMod 2) R)
    (B : Matrix (Fin 3) (Fin 3) W) :
    Matrix (Fin 3) (Fin 3) W →+
      Matrix (Fin 3) (Fin 3) R where
  toFun A :=
    finiteBlockCoefficientMatrixHom W A *
      finiteBlockCoefficientMatrixHom W B
  map_zero' := by simp
  map_add' A C := by simp [add_mul]
def finiteOuterBlockProductCentralRootHom
    (W : Submodule (ZMod 2) R)
    (i k : Fin 3) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W) :
    Multiplicative (Matrix (Fin 3) (Fin 3) W) →*
      elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
  (elementaryRootHom
    (R := Matrix (Fin 3) (Fin 3) R) i k hik).comp
      (finiteBlockCoefficientMatrixRightMul W B).toMultiplicative
def finiteOuterBlockProductCentralRootSubgroup
    (W : Submodule (ZMod 2) R)
    (i k : Fin 3) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W) :
    Subgroup (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) :=
  (finiteOuterBlockProductCentralRootHom W i k hik B).range
def finiteBlockGaloisLeftProductCoefficientMatrix
    (W : Submodule (ZMod 2) R)
    (B : Matrix (Fin 3) (Fin 3) W)
    (t : finiteBlockGaloisField) :
    Matrix (Fin 3) (Fin 3) W :=
  fun p q =>
    ⟨(finiteBlockGaloisMatrixOver R t *
        finiteBlockCoefficientMatrixHom W B) p q,
      finiteBlockCoefficientMatrix_galois_mul_mem W
        (finiteBlockCoefficientMatrixHom W B)
        (fun i j => (B i j).property) t p q⟩
def finiteOuterBlockGaloisConjugatorWithCoefficient
    (W : Submodule (ZMod 2) R)
    (j k : Fin 3) (hjk : j ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (t : finiteBlockGaloisField) :
    elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
  elementaryRootHom j k hjk
    (Multiplicative.ofAdd
      (finiteBlockGaloisMatrixOver R t *
        finiteBlockCoefficientMatrixHom W B))
def finiteOuterBlockGaloisConjugateRootWithCoefficient
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (t : finiteBlockGaloisField) :
    Subgroup (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) :=
  (finiteOuterBlockRootSubgroup W i j hij).map
    (MulAut.conj
      (finiteOuterBlockGaloisConjugatorWithCoefficient
        W j k hjk B t)).toMonoidHom
def finiteBlockGaloisRightInverseCoefficientMatrix
    (W : Submodule (ZMod 2) R)
    (A : Matrix (Fin 3) (Fin 3) W)
    (s t : finiteBlockGaloisField) :
    Matrix (Fin 3) (Fin 3) W :=
  fun p q =>
    ⟨(finiteBlockCoefficientMatrixHom W A *
        finiteBlockGaloisMatrixOver R (t - s)⁻¹) p q,
      finiteBlockCoefficientMatrix_mul_galois_mem W
        (finiteBlockCoefficientMatrixHom W A)
        (fun i j => (A i j).property) (t - s)⁻¹ p q⟩
end ActualBlockRoots
universe u₁ v₁
def UnitaryRepresentation.toRepresentation
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) : Representation ℂ G H where
  toFun g := (π g).toLinearEquiv.toLinearMap
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [map_mul, Module.End.mul_apply]
def unitaryFixedSubmodule
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) : Submodule ℂ H :=
  Representation.invariants (π.toRepresentation.comp K.subtype)
@[simp] theorem mem_unitaryFixedSubmodule
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) (x : H) :
    x ∈ unitaryFixedSubmodule π K ↔ ∀ g : K, π (g : G) x = x :=
  Iff.rfl
def unitaryVectorStabilizer
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (x : H) : Subgroup G where
  carrier := {g : G | π g x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change π g x = x at hg
    change π h x = x at hh
    change π (g * h) x = x
    simpa [map_mul, hh] using hg
  inv_mem' := by
    intro g hg
    change π g x = x at hg
    change π g⁻¹ x = x
    have heq := congrArg (fun y : H => π g⁻¹ y) hg
    simpa [← map_mul] using heq.symm
theorem unitaryFixedSubmodule_isClosed
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) :
    IsClosed (unitaryFixedSubmodule π K : Set H) := by
  have hset :
      (unitaryFixedSubmodule π K : Set H) =
        ⋂ g : K, {x : H | π (g : G) x = x} := by
    ext x
    simp
  rw [hset]
  exact isClosed_iInter fun g =>
    isClosed_eq (π (g : G)).continuous continuous_id
instance unitaryFixedSubmodule_completeSpace
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) :
    CompleteSpace (unitaryFixedSubmodule π K) :=
  (unitaryFixedSubmodule_isClosed π K).isComplete.completeSpace_coe
def heisenbergConjugateSubgroup
    {G : Type*} [Group G] (X : Subgroup G) (g : G) :
    Subgroup G :=
  X.map (MulAut.conj g).toMonoidHom
section FiniteSubgroupAveraging
variable {G : Type*} {H : Type*} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def finiteUnitarySubgroupAverage
    (π : UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K] (x : H) : H :=
  (Fintype.card K : ℂ)⁻¹ • ∑ k : K, π (k : G) x
end FiniteSubgroupAveraging
def finiteOuterBlockCyclicRootFamily
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    (W : Submodule (ZMod 2) R) (i : Fin 3) :
    Subgroup (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) :=
  finiteOuterBlockRootSubgroup W i (i + 1) (by
    fin_cases i <;> decide)
end
section
open scoped BigOperators commutatorElement
universe u
section BinaryCoefficientSpan
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]
def finiteBlockCoefficientSpan (s : Finset R) : Submodule (ZMod 2) R :=
  Submodule.span (ZMod 2) ({1} ∪ (↑s : Set R))
instance finiteBlockCoefficientSpan_finite (s : Finset R) :
    Finite (finiteBlockCoefficientSpan s) := by
  letI : Module.Finite (ZMod 2) (finiteBlockCoefficientSpan s) :=
    Module.Finite.span_of_finite (ZMod 2)
      (Set.finite_singleton 1 |>.union s.finite_toSet)
  exact Module.finite_of_finite (ZMod 2)
end BinaryCoefficientSpan
section FiniteBlockRoots
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]
def finiteBlockIndex (i p : Fin 3) : Fin 9 :=
  finProdFinEquiv (i, p)
theorem finiteBlockIndex_ne_of_ne
    {i j : Fin 3} (hij : i ≠ j) (p q : Fin 3) :
    finiteBlockIndex i p ≠ finiteBlockIndex j q := by
  intro h
  exact hij (congrArg Prod.fst (finProdFinEquiv.injective h))
def finiteBlockFlattenRingEquiv :
    Matrix (Fin 3) (Fin 3) (Matrix (Fin 3) (Fin 3) R) ≃+*
      Matrix (Fin 9) (Fin 9) R :=
  (Matrix.compRingEquiv (Fin 3) (Fin 3) R).trans
    (Matrix.reindexRingEquiv R finProdFinEquiv)
def finiteBlockRootHom
    (W : Submodule (ZMod 2) R) (i j : Fin 3) (hij : i ≠ j) :
    Multiplicative (Matrix (Fin 3) (Fin 3) W) →*
      (Matrix (Fin 9) (Fin 9) R)ˣ :=
  (Units.mapEquiv (finiteBlockFlattenRingEquiv (R := R)).toMulEquiv).toMonoidHom.comp
    (((elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)).subtype.comp
      (elementaryRootHom (R := Matrix (Fin 3) (Fin 3) R) i j hij)).comp
        (finiteBlockCoefficientMatrixHom W).toMultiplicative)
def finiteBlockRootSubgroup
    (W : Submodule (ZMod 2) R) (i j : Fin 3) (hij : i ≠ j) :
    Subgroup (Matrix (Fin 9) (Fin 9) R)ˣ :=
  (finiteBlockRootHom W i j hij).range
def cyclicFiniteBlockRootSubgroup
    (W : Submodule (ZMod 2) R) :
    Subgroup (Matrix (Fin 9) (Fin 9) R)ˣ :=
  finiteBlockRootSubgroup W 0 1 (by decide) ⊔
    finiteBlockRootSubgroup W 1 2 (by decide) ⊔
      finiteBlockRootSubgroup W 2 0 (by decide)
end FiniteBlockRoots
end
section
open scoped BigOperators
universe vSharp
end
section
open scoped BigOperators
def finiteOuterBlockFlattenHom
    {R : Type*} [Ring R] :
    elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) →*
      (Matrix (Fin 9) (Fin 9) R)ˣ :=
  (Units.mapEquiv (finiteBlockFlattenRingEquiv (R := R)).toMulEquiv).toMonoidHom.comp
    (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)).subtype
end
namespace KunThomFiberCoarea
def firstFiber {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) (x : V) : Finset (V × V) :=
  U.filter (fun z => z.1 = x)
def secondFiber {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) (x : V) : Finset (V × V) :=
  U.filter (fun z => z.2 = x)
def firstMultiplicity {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) (x : V) : ℕ :=
  (firstFiber U x).card
def secondMultiplicity {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) (x : V) : ℕ :=
  (secondFiber U x).card
def diagonalImage {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) : Finset (V × V) :=
  U.image (p.prodCongr p)
def diagonalExit {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) : ℕ :=
  (U.filter fun z => (p.prodCongr p) z ∉ U).card
def permutationVariation {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℕ) : ℕ :=
  ∑ i : ι, ∑ x : V, Nat.dist (f (σ i x)) (f x)
def positiveNatSupport {V : Type*} [Fintype V]
    (f : V → ℕ) : Finset V :=
  Finset.univ.filter (fun x => 0 < f x)
@[simp]
theorem mem_positiveNatSupport {V : Type*} [Fintype V]
    (f : V → ℕ) (x : V) :
    x ∈ positiveNatSupport f ↔ 0 < f x := by
  simp [positiveNatSupport]
def singletonSupport {V : Type*} [Fintype V]
    (f : V → ℕ) : Finset V :=
  Finset.univ.filter (fun x => f x = 1)
@[simp]
theorem mem_singletonSupport {V : Type*} [Fintype V]
    (f : V → ℕ) (x : V) :
    x ∈ singletonSupport f ↔ f x = 1 := by
  simp [singletonSupport]
def nonSingletonFirstEdges {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) : Finset (V × V) :=
  U.filter (fun z => firstMultiplicity U z.1 ≠ 1)
def nonSingletonSecondEdges {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) : Finset (V × V) :=
  U.filter (fun z => secondMultiplicity U z.2 ≠ 1)
def matchedFiberEdges {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) : Finset (V × V) :=
  U.filter (fun z =>
    firstMultiplicity U z.1 = 1 ∧ secondMultiplicity U z.2 = 1)
def singletonFirstEdges {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) : Finset (V × V) :=
  U.filter (fun z => firstMultiplicity U z.1 = 1)
end KunThomFiberCoarea
namespace KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
def permutationUnitary {V : Type*} [Fintype V] (p : Equiv.Perm V) :
    EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ p
@[simp]
theorem permutationUnitary_one {V : Type*} [Fintype V]
    (ξ : EuclideanSpace ℂ V) :
    permutationUnitary (1 : Equiv.Perm V) ξ = ξ := by
  ext x
  change ξ x = ξ x
  rfl
def indicatorVector {V : Type*}
    (f : V → ℝ) : EuclideanSpace ℂ V :=
  WithLp.toLp 2 fun x => (f x : ℂ)
def permutationMarkov {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (ξ : EuclideanSpace ℂ V) :
    EuclideanSpace ℂ V :=
  (Fintype.card ι : ℂ)⁻¹ • ∑ i, permutationUnitary (p i) ξ
@[simp]
theorem permutationMarkov_apply {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (ξ : EuclideanSpace ℂ V) (x : V) :
    permutationMarkov p ξ x =
      (∑ i, ξ ((p i).symm x)) / (Fintype.card ι : ℂ) := by
  simp [permutationMarkov, permutationUnitary, div_eq_mul_inv, mul_comm]
def normalizedIndicatorDisplacement
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) (q : Equiv.Perm V) :
    EuclideanSpace ℂ V :=
  ((‖permutationMarkov p (indicatorVector f) -
      indicatorVector f‖ : ℝ) : ℂ)⁻¹ •
    (permutationUnitary q (indicatorVector f) - indicatorVector f)
def normalizedIndicatorDefect
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) :
    EuclideanSpace ℂ V :=
  ((‖permutationMarkov p (indicatorVector f) -
      indicatorVector f‖ : ℝ) : ℂ)⁻¹ •
    (permutationMarkov p (indicatorVector f) - indicatorVector f)
def normalizedPairDisplacement
    {G ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (q : G × G) :
    EuclideanSpace ℂ V :=
  normalizedIndicatorDisplacement p f (σ q.1) -
    normalizedIndicatorDisplacement p f (σ q.2)
def scalarOperatorKernel {I : Type u} (K : Matrix I I ℂ) :
    Matrix I I (ℂ →L[ℂ] ℂ) :=
  fun g h => ContinuousLinearMap.toSpanSingleton ℂ (K g h)
theorem preKernel_inner_single {I : Type u}
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (i j : I × ℂ) (z w : ℂ) :
    ⟪(Finsupp.single i z : RKHS.H₀ (scalarOperatorKernel K)),
      (Finsupp.single j w : RKHS.H₀ (scalarOperatorKernel K))⟫_ℂ =
      star z * w *
        ⟪scalarOperatorKernel K j.1 i.1 i.2, j.2⟫_ℂ := by
  change
    (Finsupp.single i z).sum (fun yu c =>
      (Finsupp.single j w).sum (fun xv d =>
        star c * d *
          ⟪scalarOperatorKernel K xv.1 yu.1 yu.2, xv.2⟫_ℂ)) = _
  simp
def actionPreKernelTranslation {G I : Type u} [Group G]
    (K : Matrix I I ℂ) (ρ : G →* Equiv.Perm I) (a : G) :
    RKHS.H₀ (scalarOperatorKernel K) ≃ₗ[ℂ]
      RKHS.H₀ (scalarOperatorKernel K) :=
  Finsupp.domLCongr ((ρ a).prodCongr (Equiv.refl ℂ))
theorem actionPreKernelTranslation_inner {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) (f g : RKHS.H₀ (scalarOperatorKernel K)) :
    ⟪actionPreKernelTranslation K ρ a f,
      actionPreKernelTranslation K ρ a g⟫_ℂ = ⟪f, g⟫_ℂ := by
  induction f using Finsupp.induction_linear generalizing g with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ =>
    simp [map_add, inner_add_left, ih₁ g, ih₂ g]
  | single i z =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ ih₁ ih₂ =>
      simp [map_add, inner_add_right, ih₁, ih₂]
    | single j w =>
      simp only [actionPreKernelTranslation,
        Finsupp.domLCongr_single, preKernel_inner_single,
        scalarOperatorKernel,
        ContinuousLinearMap.toSpanSingleton_apply]
      change
        star z * w * ⟪i.2 • K (ρ a j.1) (ρ a i.1), j.2⟫_ℂ =
          star z * w * ⟪i.2 • K j.1 i.1, j.2⟫_ℂ
      rw [hinv]
def actionPreKernelTranslationIsometry {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) :
    RKHS.H₀ (scalarOperatorKernel K) ≃ₗᵢ[ℂ]
      RKHS.H₀ (scalarOperatorKernel K) :=
  (actionPreKernelTranslation K ρ a).isometryOfInner
    (actionPreKernelTranslation_inner K ρ hinv a)
def actionKernelTranslationMap {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) :
    RKHS.OfKernel (scalarOperatorKernel K) →L[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K) :=
  ContinuousLinearMap.completion
    ((actionPreKernelTranslationIsometry K ρ hinv a).toLinearIsometry.toContinuousLinearMap)
@[simp]
theorem actionKernelTranslationMap_coe {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) (f : RKHS.H₀ (scalarOperatorKernel K)) :
    actionKernelTranslationMap K ρ hinv a
      (f : RKHS.OfKernel (scalarOperatorKernel K)) =
        (actionPreKernelTranslation K ρ a f :
          RKHS.OfKernel (scalarOperatorKernel K)) := by
  exact ContinuousLinearMap.completion_apply_coe
    ((actionPreKernelTranslationIsometry K ρ hinv a).toLinearIsometry.toContinuousLinearMap) f
theorem actionKernelTranslationMap_isometry {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) : Isometry (actionKernelTranslationMap K ρ hinv a) := by
  change Isometry (UniformSpace.Completion.map
    (actionPreKernelTranslationIsometry K ρ hinv a))
  exact (actionPreKernelTranslationIsometry K ρ hinv a).isometry.completion_map
theorem actionPreKernelTranslation_mul_apply {G I : Type u} [Group G]
    (K : Matrix I I ℂ) (ρ : G →* Equiv.Perm I)
    (a b : G) (f : RKHS.H₀ (scalarOperatorKernel K)) :
    actionPreKernelTranslation K ρ (a * b) f =
      actionPreKernelTranslation K ρ a
        (actionPreKernelTranslation K ρ b f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single i z =>
    simp only [actionPreKernelTranslation,
      Finsupp.domLCongr_single]
    change Finsupp.single (ρ (a * b) i.1, i.2) z =
      Finsupp.single (ρ a (ρ b i.1), i.2) z
    rw [map_mul]
    rfl
@[simp]
theorem actionPreKernelTranslation_one_apply {G I : Type u} [Group G]
    (K : Matrix I I ℂ) (ρ : G →* Equiv.Perm I)
    (f : RKHS.H₀ (scalarOperatorKernel K)) :
    actionPreKernelTranslation K ρ 1 f = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single i z =>
    simp only [actionPreKernelTranslation,
      Finsupp.domLCongr_single]
    change Finsupp.single (ρ 1 i.1, i.2) z =
      Finsupp.single (i.1, i.2) z
    simp
theorem actionKernelTranslationMap_mul_apply {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a b : G) (x : RKHS.OfKernel (scalarOperatorKernel K)) :
    actionKernelTranslationMap K ρ hinv (a * b) x =
      actionKernelTranslationMap K ρ hinv a
        (actionKernelTranslationMap K ρ hinv b x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (actionKernelTranslationMap K ρ hinv (a * b)).continuous
      ((actionKernelTranslationMap K ρ hinv a).continuous.comp
        (actionKernelTranslationMap K ρ hinv b).continuous)
  | ih f =>
    simp only [actionKernelTranslationMap_coe,
      actionPreKernelTranslation_mul_apply]
@[simp]
theorem actionKernelTranslationMap_one_apply {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (x : RKHS.OfKernel (scalarOperatorKernel K)) :
    actionKernelTranslationMap K ρ hinv 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (actionKernelTranslationMap K ρ hinv 1).continuous
      continuous_id
  | ih f =>
    simp only [actionKernelTranslationMap_coe,
      actionPreKernelTranslation_one_apply]
def actionKernelTranslationLinearEquiv {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) :
    RKHS.OfKernel (scalarOperatorKernel K) ≃ₗ[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K) where
  toLinearMap := (actionKernelTranslationMap K ρ hinv a).toLinearMap
  invFun := actionKernelTranslationMap K ρ hinv a⁻¹
  left_inv x := by
    calc
      actionKernelTranslationMap K ρ hinv a⁻¹
        (actionKernelTranslationMap K ρ hinv a x) =
          actionKernelTranslationMap K ρ hinv (a⁻¹ * a) x :=
            (actionKernelTranslationMap_mul_apply
              K ρ hinv a⁻¹ a x).symm
      _ = x := by simp
  right_inv x := by
    calc
      actionKernelTranslationMap K ρ hinv a
        (actionKernelTranslationMap K ρ hinv a⁻¹ x) =
          actionKernelTranslationMap K ρ hinv (a * a⁻¹) x :=
            (actionKernelTranslationMap_mul_apply
              K ρ hinv a a⁻¹ x).symm
      _ = x := by simp
def actionKernelTranslationUnitary {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j)
    (a : G) :
    RKHS.OfKernel (scalarOperatorKernel K) ≃ₗᵢ[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K) where
  toLinearEquiv := actionKernelTranslationLinearEquiv K ρ hinv a
  norm_map' :=
    (actionKernelTranslationMap_isometry K ρ hinv a).norm_map_of_map_zero
      (map_zero (actionKernelTranslationMap K ρ hinv a))
def actionKernelUnitaryRepresentation {G I : Type u} [Group G]
    (K : Matrix I I ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (ρ : G →* Equiv.Perm I)
    (hinv : ∀ a i j, K (ρ a i) (ρ a j) = K i j) :
    G →* (RKHS.OfKernel (scalarOperatorKernel K) ≃ₗᵢ[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K)) where
  toFun := actionKernelTranslationUnitary K ρ hinv
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    change actionKernelTranslationMap K ρ hinv 1 x = x
    exact actionKernelTranslationMap_one_apply K ρ hinv x
  map_mul' a b := by
    apply LinearIsometryEquiv.ext
    intro x
    change actionKernelTranslationMap K ρ hinv (a * b) x =
      actionKernelTranslationMap K ρ hinv a
        (actionKernelTranslationMap K ρ hinv b x)
    exact actionKernelTranslationMap_mul_apply K ρ hinv a b x
def diagonalPairAction (G : Type u) [Group G] :
    G →* Equiv.Perm (G × G) where
  toFun a := (Equiv.mulLeft a).prodCongr (Equiv.mulLeft a)
  map_one' := by
    apply Equiv.ext
    intro x
    exact Prod.ext (one_mul x.1) (one_mul x.2)
  map_mul' a b := by
    apply Equiv.ext
    intro x
    apply Prod.ext
    · exact mul_assoc a b x.1
    · exact mul_assoc a b x.2
def diagonalPairKernelUnitaryRepresentation {G : Type u} [Group G]
    (K : Matrix (G × G) (G × G) ℂ)
    [Fact (scalarOperatorKernel K).PosSemidef]
    (hinv : ∀ a g h j k : G,
      K (a * g, a * h) (a * j, a * k) = K (g, h) (j, k)) :
    G →* (RKHS.OfKernel (scalarOperatorKernel K) ≃ₗᵢ[ℂ]
      RKHS.OfKernel (scalarOperatorKernel K)) :=
  actionKernelUnitaryRepresentation K (diagonalPairAction G)
    (fun a x y => hinv a x.1 x.2 y.1 y.2)
structure HilbertKernelRealization {I : Type u}
    (K : Matrix I I ℂ) where
  carrier : Type u
  [normed : NormedAddCommGroup carrier]
  [inner : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]
  vector : I → carrier
  gram : ∀ g h, ⟪vector g, vector h⟫_ℂ = K g h
instance hilbertKernelRealizationNormedAddCommGroup
    {I : Type u} {K : Matrix I I ℂ}
    (R : HilbertKernelRealization K) : NormedAddCommGroup R.carrier :=
  R.normed
instance hilbertKernelRealizationInnerProductSpace
    {I : Type u} {K : Matrix I I ℂ}
    (R : HilbertKernelRealization K) : InnerProductSpace ℂ R.carrier :=
  R.inner
instance hilbertKernelRealizationCompleteSpace
    {I : Type u} {K : Matrix I I ℂ}
    (R : HilbertKernelRealization K) : CompleteSpace R.carrier :=
  R.complete
structure EquivariantHilbertKernelRealization
    {G : Type u} [Group G]
    (K : Matrix (G × G) (G × G) ℂ) where
  realization : HilbertKernelRealization K
  representation : G →*
    (realization.carrier ≃ₗᵢ[ℂ] realization.carrier)
  equivariant : ∀ a g h : G,
    representation a (realization.vector (g, h)) =
      realization.vector (a * g, a * h)
def equivariantPairCocycle {G : Type u} [Group G]
    {K : Matrix (G × G) (G × G) ℂ}
    (R : EquivariantHilbertKernelRealization K) (g : G) :
    R.realization.carrier :=
  R.realization.vector (g, 1)
end KunRootedIndicatorCrossing
namespace KunThomInvariantOrthogonal
section
open Filter Topology
open scoped ComplexConjugate Pointwise
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def invariantSubmodule (π : SoficGroups.UnitaryRepresentation G H) :
    Submodule ℂ H where
  carrier := {x | ∀ g : G, π g x = x}
  zero_mem' := by
    intro g
    exact map_zero (π g)
  add_mem' := by
    intro x y hx hy g
    rw [map_add, hx g, hy g]
  smul_mem' := by
    intro c x hx g
    rw [map_smul, hx g]
theorem map_mem_invariantSubmodule_orthogonal
    (π : SoficGroups.UnitaryRepresentation G H) (g : G) {x : H}
    (hx : x ∈ (invariantSubmodule π)ᗮ) :
    π g x ∈ (invariantSubmodule π)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hysymm : (π g).symm y = y := by
    have hyinv : π g⁻¹ y = y := hy g⁻¹
    simpa [map_inv, LinearIsometryEquiv.inv_def] using hyinv
  calc
    @inner ℂ H _ y (π g x) =
        @inner ℂ H _ ((π g).symm y) x := by
          simpa using ((π g).symm.inner_map_map y (π g x)).symm
    _ = @inner ℂ H _ y x := by rw [hysymm]
    _ = 0 := (Submodule.mem_orthogonal _ _).mp hx y hy
def orthogonalLinearIsometryEquiv
    (π : SoficGroups.UnitaryRepresentation G H) (g : G) :
    (invariantSubmodule π)ᗮ ≃ₗᵢ[ℂ] (invariantSubmodule π)ᗮ where
  toFun x := ⟨π g x, map_mem_invariantSubmodule_orthogonal π g x.property⟩
  invFun x :=
    ⟨π g⁻¹ x, map_mem_invariantSubmodule_orthogonal π g⁻¹ x.property⟩
  left_inv x := by
    apply Subtype.ext
    change π g⁻¹ (π g (x : H)) = x
    simp [map_inv, LinearIsometryEquiv.inv_def]
  right_inv x := by
    apply Subtype.ext
    change π g (π g⁻¹ (x : H)) = x
    simp [map_inv, LinearIsometryEquiv.inv_def]
  map_add' x y := by
    apply Subtype.ext
    exact map_add (π g) (x : H) (y : H)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (π g) c (x : H)
  norm_map' x := (π g).norm_map (x : H)
def orthogonalRepresentation (π : SoficGroups.UnitaryRepresentation G H) :
    SoficGroups.UnitaryRepresentation G ((invariantSubmodule π)ᗮ) where
  toFun := orthogonalLinearIsometryEquiv π
  map_one' := by
    ext x
    change π 1 (x : H) = x
    simp
  map_mul' g h := by
    ext x
    change π (g * h) (x : H) = π g (π h (x : H))
    rw [map_mul]
    rfl
end
section
open Filter Topology
open scoped ComplexConjugate Pointwise
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def unitaryFinsetMarkov
    (π : SoficGroups.UnitaryRepresentation G H)
    (S : Finset G) (x : H) : H :=
  ((S.card : ℂ)⁻¹) • S.sum (fun g => π g x)
def kazhdanMarkovContractionFactor
    (P : SoficGroups.KazhdanPair.{u, v} G) (S : Finset G) : ℝ :=
  max 0 (1 - P.kazhdanConstant ^ 2 / (4 * (S.card : ℝ)))
end
end KunThomInvariantOrthogonal
namespace KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w
def pairedWordAverage
    {G ι E : Type*} [Group G] [Fintype ι]
    [AddCommMonoid E] [Module ℂ E]
    (s : ι → G) (z : G × G → E) :
    ℕ → G × G → E
  | 0, q => z q
  | k + 1, q =>
      (Fintype.card ι : ℂ)⁻¹ •
        ∑ i, pairedWordAverage s z k (s i * q.1, s i * q.2)
def pairedDefectWordAverage
    {G ι E : Type*} [Group G] [Fintype ι]
    [AddCommMonoid E] [Module ℂ E]
    (s : ι → G) (z : G × G → E) (k : ℕ) : E :=
  (Fintype.card ι : ℂ)⁻¹ •
    ∑ i, pairedWordAverage s z k (s i, 1)
def permutationMarkovLinear
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) :
    EuclideanSpace ℂ V →ₗ[ℂ] EuclideanSpace ℂ V :=
  (Fintype.card ι : ℂ)⁻¹ •
    ∑ i, (permutationUnitary (p i)).toLinearEquiv.toLinearMap
@[simp]
theorem permutationMarkovLinear_apply
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (x : EuclideanSpace ℂ V) :
    permutationMarkovLinear p x = permutationMarkov p x := by
  simp [permutationMarkovLinear, permutationMarkov]
def representationFamilyMarkovLinear
    {G ι H : Type*} [Group G] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : SoficGroups.UnitaryRepresentation G H) (s : ι → G) :
    H →ₗ[ℂ] H :=
  (Fintype.card ι : ℂ)⁻¹ •
    ∑ i, (π (s i)).toLinearEquiv.toLinearMap
structure RootedIndicatorMarkovModel (G ι : Type u) where
  carrier : Type u
  [fintype : Fintype carrier]
  generator : ι → Equiv.Perm carrier
  indicator : carrier → ℝ
  evaluation : G → Equiv.Perm carrier
instance rootedIndicatorMarkovModelFintype
    {G ι : Type u} (X : RootedIndicatorMarkovModel G ι) : Fintype X.carrier :=
  X.fintype
structure RootedIndicatorMarkovModel.IsGenerated
    {G ι : Type u} [Group G] [Fintype ι]
    (X : RootedIndicatorMarkovModel G ι)
    (s : ι → G) (w : G → List ι) : Prop where
  indicator_mem : ∀ x, X.indicator x = 0 ∨ X.indicator x = 1
  word_evaluation : ∀ g,
    X.evaluation g = ((w g).map X.generator).prod
  identity_evaluation : X.evaluation 1 = 1
  generator_evaluation : ∀ i, X.evaluation (s i) = X.generator i
structure RootedIndicatorMarkovModel.IsRootedAtRadius
    {G ι : Type u} [Group G]
    (X : RootedIndicatorMarkovModel G ι)
    (w : G → List ι) (r : ℕ) : Prop where
  out : ∀ a g : G,
    (w a).length + (w g).length + (w (a * g)).length ≤ r →
      ∀ x : X.carrier, indicatorVector X.indicator x ≠ 0 →
        X.evaluation (a * g) x =
          (X.evaluation a * X.evaluation g) x
end KunRootedWordPower
namespace KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
def modelMultiplicationBad {G : Type*} [Group G]
    (M : SoficGroups.PermutationModel G) (g h : G) :
    Finset (Fin M.size) :=
  Finset.univ.filter (fun x =>
    M.action (g * h) x ≠ (M.action g * M.action h) x)
@[simp]
theorem mem_modelMultiplicationBad {G : Type*} [Group G]
    (M : SoficGroups.PermutationModel G) (g h : G)
    (x : Fin M.size) :
    x ∈ modelMultiplicationBad M g h ↔
      M.action (g * h) x ≠ (M.action g * M.action h) x := by
  simp only [modelMultiplicationBad, Finset.mem_filter,
    Finset.mem_univ, true_and]
def modelSeparationBad {G : Type*} [Group G]
    (M : SoficGroups.PermutationModel G) (g h : G) :
    Finset (Fin M.size) :=
  SoficGroups.agreementSet (M.action g) (M.action h)
@[simp]
theorem mem_modelSeparationBad {G : Type*} [Group G]
    (M : SoficGroups.PermutationModel G) (g h : G)
    (x : Fin M.size) :
    x ∈ modelSeparationBad M g h ↔ M.action g x = M.action h x := by
  simp [modelSeparationBad, SoficGroups.agreementSet]
def finiteMultiplicationBad {G : Type*} [Group G]
    (M : SoficGroups.PermutationModel G) (F : Finset G) :
    Finset (Fin M.size) := by
  classical
  exact (F.product F).biUnion fun q =>
    modelMultiplicationBad M q.1 q.2
def finiteSeparationBad {G : Type*} [Group G]
    (M : SoficGroups.PermutationModel G) (F : Finset G) :
    Finset (Fin M.size) := by
  classical
  exact ((F.product F).filter fun q => q.1 ≠ q.2).biUnion fun q =>
    modelSeparationBad M q.1 q.2
def finiteRootBad {G : Type*} [Group G]
    (M : SoficGroups.PermutationModel G) (F : Finset G) :
    Finset (Fin M.size) :=
  finiteMultiplicationBad M F ∪ finiteSeparationBad M F
def chosenWordEvaluation
    {G ι : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (s : ι → G) (w : G → List ι) (n : ℕ) (g : G) :
    Equiv.Perm (Fin (A.model n).size) :=
  ((w g).map fun i => (A.model n).action (s i)).prod
def chosenWordMultiplicationBad
    {G ι : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (s : ι → G) (w : G → List ι) (n : ℕ) (g h : G) :
    Finset (Fin (A.model n).size) :=
  Finset.univ.filter (fun x =>
    chosenWordEvaluation A s w n (g * h) x ≠
      (chosenWordEvaluation A s w n g *
        chosenWordEvaluation A s w n h) x)
@[simp]
theorem mem_chosenWordMultiplicationBad
    {G ι : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (s : ι → G) (w : G → List ι) (n : ℕ) (g h : G)
    (x : Fin (A.model n).size) :
    x ∈ chosenWordMultiplicationBad A s w n g h ↔
      chosenWordEvaluation A s w n (g * h) x ≠
        (chosenWordEvaluation A s w n g *
          chosenWordEvaluation A s w n h) x := by
  simp only [chosenWordMultiplicationBad, Finset.mem_filter,
    Finset.mem_univ, true_and]
def chosenFiniteMultiplicationBad
    {G ι : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (F : Finset G) (n : ℕ) : Finset (Fin (A.model n).size) := by
  classical
  exact (F.product F).biUnion fun q =>
    chosenWordMultiplicationBad A s w n q.1 q.2
def chosenFiniteRootBad
    {G ι : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (F : Finset G) (n : ℕ) : Finset (Fin (A.model n).size) :=
  finiteRootBad (A.model n) F ∪
    chosenFiniteMultiplicationBad A s w F n
theorem exists_generator_word_of_symmetric_generates
    {G : Type*} [Group G]
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (g : G) :
    ∃ l : List ↥S,
      ((l.map fun i : ↥S => (i : G)).prod) = g := by
  classical
  have hg : g ∈ Subgroup.closure (S : Set G) := by
    rw [hgenerates]
    simp
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      exact ⟨[⟨x, hx⟩], by simp⟩
  | one =>
      exact ⟨[], by simp⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨lx, hlx⟩ := ihx
      obtain ⟨ly, hly⟩ := ihy
      refine ⟨lx ++ ly, ?_⟩
      rw [List.map_append, List.prod_append, hlx, hly]
  | inv x _ ih =>
      obtain ⟨l, hl⟩ := ih
      let invLetter : ↥S → ↥S :=
        fun i => ⟨(i : G)⁻¹, hsymmetric (i : G) i.property⟩
      refine ⟨(l.map invLetter).reverse, ?_⟩
      rw [List.map_reverse, List.map_map]
      change ((l.map fun i : ↥S => (i : G)⁻¹).reverse).prod = x⁻¹
      have hmap :
          (l.map fun i : ↥S => (i : G)⁻¹) =
            (l.map (fun i : ↥S => (i : G))).map
              (fun x : G => x⁻¹) := by
        rw [List.map_map]
        rfl
      rw [hmap, ← List.prod_inv_reverse, hl]
def symmetricGeneratorWord
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (g : G) : List ↥S := by
  classical
  by_cases hone : g = 1
  · exact []
  · by_cases hg : g ∈ S
    · exact [⟨g, hg⟩]
    · exact (exists_generator_word_of_symmetric_generates
        S hsymmetric hgenerates g).choose
@[simp]
theorem symmetricGeneratorWord_one
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) :
    symmetricGeneratorWord S hsymmetric hgenerates (1 : G) = [] := by
  simp [symmetricGeneratorWord]
def chosenCayleyRadiusBad
    {G : Type*} [Group G] [DecidableEq G]
    (A : SoficGroups.SoficApproximation G)
    (S : Finset G) (w : G → List ↥S) (n r : ℕ) :
    Finset (Fin (A.model n).size) :=
  chosenFiniteRootBad A (fun i : ↥S => (i : G)) w (S ^ r) n
end KunActualSoficRootRadius
namespace KunDirectedIndicatorJensen
open scoped BigOperators
def realIndicator {V : Type*} [DecidableEq V]
    (T : Finset V) (x : V) : ℝ :=
  if x ∈ T then 1 else 0
def realPermutationMarkov {V ι : Type*} [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (x : V) : ℝ :=
  (∑ i : ι, f ((σ i).symm x)) / Fintype.card ι
end KunDirectedIndicatorJensen
namespace KunFinitePermutationMarkovMass
open scoped BigOperators
def realIndicator {V : Type*} [DecidableEq V]
    (T : Finset V) (x : V) : ℝ :=
  if x ∈ T then 1 else 0
def realPermutationMarkov {V ι : Type*} [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (x : V) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, f ((σ i).symm x)
end KunFinitePermutationMarkovMass
namespace KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
noncomputable def completeCleanFinpartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (P : Finpartition (Finset.univ \ B)) :
    Finpartition (Finset.univ : Finset V) := by
  classical
  let parts : Finset (Finset V) :=
    P.parts ∪ (⊥ : Finpartition B).parts
  refine Finpartition.ofExistsUnique parts ?_ ?_ ?_
  · intro C _
    exact Finset.subset_univ C
  · intro x _
    by_cases hx : x ∈ B
    · refine ⟨{x}, ⟨?_, by simp⟩, ?_⟩
      · exact Finset.mem_union_right _
          (Finpartition.mem_bot_iff.mpr ⟨x, hx, rfl⟩)
      · intro C hC
        obtain ⟨hpart, hxC⟩ := hC
        rcases Finset.mem_union.mp hpart with hclean | hbad
        · have hxc := P.subset hclean hxC
          exact ((Finset.mem_sdiff.mp hxc).2 hx).elim
        · obtain ⟨y, _, hy⟩ := Finpartition.mem_bot_iff.mp hbad
          subst C
          simp only [Finset.mem_singleton] at hxC
          subst y
          rfl
    · have hxclean : x ∈ (Finset.univ \ B : Finset V) := by
        simp [hx]
      obtain ⟨C, ⟨hCP, hxC⟩, hunique⟩ :=
        P.existsUnique_mem hxclean
      refine ⟨C, ⟨Finset.mem_union_left _ hCP, hxC⟩, ?_⟩
      intro D hD
      obtain ⟨hpart, hxD⟩ := hD
      rcases Finset.mem_union.mp hpart with hclean | hbad
      · exact hunique D ⟨hclean, hxD⟩
      · obtain ⟨y, hyB, hy⟩ := Finpartition.mem_bot_iff.mp hbad
        subst D
        simp only [Finset.mem_singleton] at hxD
        exact (hx (hxD.symm ▸ hyB)).elim
  · intro hempty
    rcases Finset.mem_union.mp hempty with hclean | hbad
    · exact P.empty_notMem_parts hclean
    · obtain ⟨x, _, hx⟩ := Finpartition.mem_bot_iff.mp hbad
      simp at hx
@[simp]
theorem completeCleanFinpartition_parts
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (P : Finpartition (Finset.univ \ B)) :
    (completeCleanFinpartition B P).parts =
      P.parts ∪ (⊥ : Finpartition B).parts := by
  rfl
end KunResidualExpanderDecomposition
namespace KunDiagonalGoodRootGraphLoss
open scoped BigOperators symmDiff
def goodPermutationGraph {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) : Finset (V × V) :=
  (SoficGroups.permutationGraph p).filter
    (fun z => z.1 ∉ B ∧ z.2 ∉ B)
end KunDiagonalGoodRootGraphLoss
namespace KunCompletedPrunedComponent
open scoped BigOperators
end KunCompletedPrunedComponent
namespace MatchedComponentCompletion
open scoped BigOperators
noncomputable def completedRestriction {V : Type*} [Fintype V]
    (p : Equiv.Perm V) (Z : Finset V) :
    Equiv.Perm (↥Z) :=
  Classical.choose (SoficGroups.exists_completion_of_internal_permutation p Z)
theorem completedRestriction_apply_of_mem
    {V : Type*} [Fintype V]
    (p : Equiv.Perm V) (Z : Finset V)
    (x : V) (hx : x ∈ Z) (hp : p x ∈ Z) :
    ((completedRestriction p Z ⟨x, hx⟩ : {x : V // x ∈ Z}) : V) = p x :=
  (Classical.choose_spec
    (SoficGroups.exists_completion_of_internal_permutation p Z)) x hx hp
@[simp] theorem completedRestriction_one
    {V : Type*} [Fintype V] (Z : Finset V) :
    completedRestriction (1 : Equiv.Perm V) Z = 1 := by
  ext x
  simpa using completedRestriction_apply_of_mem
    (1 : Equiv.Perm V) Z x x.property x.property
def subtypeBad {V : Type*} [DecidableEq V]
    (Z E : Finset V) : Finset (↥Z) :=
  Finset.univ.filter (fun x => (x : V) ∈ E)
@[simp] theorem mem_subtypeBad
    {V : Type*} [DecidableEq V]
    (Z E : Finset V) (x : {x : V // x ∈ Z}) :
    x ∈ subtypeBad Z E ↔ (x : V) ∈ E := by
  simp [subtypeBad]
noncomputable def sourceCompletionBad
    {V ι J : Type*} [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) : Finset V := by
  classical
  let T := SoficGroups.CompressionCriterion.productTrackedTable F
  exact
    (Finset.univ.biUnion fun i : ι =>
      Z.filter fun z => σ i z ∉ Z) ∪
    (T.biUnion fun j =>
      Z.filter fun z => p j z ∉ Z) ∪
    (Finset.univ.biUnion fun i : ι =>
      T.biUnion fun j =>
        Z.filter fun z => p j (σ i z) ≠ σ i (p j z)) ∪
    (Finset.univ.biUnion fun i : ι =>
      T.biUnion fun j =>
        Z.filter fun z => p j (σ i z) ∉ Z) ∪
    (F.biUnion fun j =>
      F.biUnion fun k =>
        Z.filter fun z => p (j * k) z ≠ p j (p k z)) ∪
    (F.biUnion fun j =>
      F.biUnion fun k =>
        Z.filter fun z => j ≠ k ∧ p j z = p k z)
end MatchedComponentCompletion
namespace MatchedComponentExitBudget
open Filter Topology
open scoped BigOperators
noncomputable def sourceWordTestBad
    {V ι J : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) : Finset V := by
  classical
  let T := SoficGroups.CompressionCriterion.productTrackedTable F
  exact
    (Finset.univ.biUnion fun i : ι =>
      T.biUnion fun j =>
        Finset.univ.filter fun z => p j (σ i z) ≠ σ i (p j z)) ∪
    (F.biUnion fun j =>
      F.biUnion fun k =>
        Finset.univ.filter fun z => p (j * k) z ≠ p j (p k z)) ∪
    (F.biUnion fun j =>
      F.biUnion fun k =>
        Finset.univ.filter fun z => j ≠ k ∧ p j z = p k z)
end MatchedComponentExitBudget
namespace KunRealComplexMarkovBridge
open scoped BigOperators ComplexOrder InnerProductSpace Topology
def realMarkov {ι V : Type*} [Fintype ι]
    (p : ι → Equiv.Perm V) (f : V → ℝ) (x : V) : ℝ :=
  (∑ i, f ((p i).symm x)) / (Fintype.card ι : ℝ)
def permutationUnitary {V : Type*} [Fintype V] (p : Equiv.Perm V) :
    EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ p
def indicatorVector {V : Type*}
    (f : V → ℝ) : EuclideanSpace ℂ V :=
  WithLp.toLp 2 fun x => (f x : ℂ)
@[simp]
theorem indicatorVector_apply {V : Type*}
    (f : V → ℝ) (x : V) :
    indicatorVector f x = (f x : ℂ) := rfl
def permutationMarkov {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (ξ : EuclideanSpace ℂ V) :
    EuclideanSpace ℂ V :=
  (Fintype.card ι : ℂ)⁻¹ • ∑ i, permutationUnitary (p i) ξ
@[simp]
theorem permutationMarkov_apply {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (ξ : EuclideanSpace ℂ V) (x : V) :
    permutationMarkov p ξ x =
      (∑ i, ξ ((p i).symm x)) / (Fintype.card ι : ℂ) := by
  simp [permutationMarkov, permutationUnitary, div_eq_mul_inv, mul_comm]
end KunRealComplexMarkovBridge
namespace KunRootedWordPower
section
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v
end
section
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u
end
end KunRootedWordPower
namespace KunActualRootedModelBridge
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators
universe u
def sourceFiniteIndicator
    {V : Type*} [DecidableEq V] (T : Finset V) (x : V) : ℝ :=
  if x ∈ T then 1 else 0
def sourceRootedIndicatorMarkovModel
    {G : Type} [Group G] [DecidableEq G]
    (A : SoficGroups.SoficApproximation G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (n : ℕ) (T : Finset (Fin (A.model n).size)) :
    RootedIndicatorMarkovModel G ↥S where
  carrier := Fin (A.model n).size
  fintype := inferInstance
  generator i := (A.model n).action (i : G)
  indicator := sourceFiniteIndicator T
  evaluation :=
    chosenWordEvaluation A (fun i : ↥S => (i : G))
      (symmetricGeneratorWord S hsymmetric hgenerates) n
end KunActualRootedModelBridge
namespace KunSharpThresholdCut
open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff
def upperLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (t : ℝ) : Finset V :=
  Finset.univ.filter (fun x => t < f x)
def highCrossingProfile {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (a t : ℝ) : ℝ :=
  Finset.univ.sum (fun i : ι =>
    (Finset.univ.filter (fun x : V => a < f x)).sum (fun x =>
      (Ico (f (σ i x)) (f x)).indicator (fun _ => (1 : ℝ)) t))
end KunSharpThresholdCut
namespace KunActualFinalRestrictedVariation
open scoped BigOperators
def realMarkov {V ι : Type*} [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (x : V) : ℝ :=
  (∑ i : ι, f ((σ i).symm x)) / (Fintype.card ι : ℝ)
end KunActualFinalRestrictedVariation
namespace MatchedFirstStageWordRadiusTransfer
open Filter Topology
open scoped BigOperators
end MatchedFirstStageWordRadiusTransfer
namespace SourceCompressionMatching
open Filter Topology
open scoped BigOperators symmDiff
end SourceCompressionMatching
namespace SourceCompressionTransportCrossing
open Filter Topology
open scoped BigOperators
end SourceCompressionTransportCrossing
namespace KunResidualRetainedSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff
end KunResidualRetainedSelection
namespace KunUniversalGoodRootReferenceCuts
open scoped symmDiff
end KunUniversalGoodRootReferenceCuts
namespace KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise symmDiff
universe u
local instance rootedSparseModelDecidableEq
    {G ι : Type u} (X : RootedIndicatorMarkovModel G ι) :
    DecidableEq X.carrier :=
  Classical.decEq X.carrier
end KunRootedWordPower
namespace SourceCompressionRetainedDiscard
open Filter Topology
open scoped BigOperators symmDiff
noncomputable def witnesslessComponents
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ) (eta : ℝ) :
    Finset (Finset V) :=
  (P.parts \ SoficGroups.insufficientOverlapComponents P Q eta).filter
    (fun C => ∀ y ∈ C ∩ SoficGroups.maximumOverlapPart Q C,
      b (T.symm y) ≠ b y)
noncomputable def retainedComponents
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ) (eta : ℝ) :
    Finset (Finset V) :=
  P.parts \ (SoficGroups.insufficientOverlapComponents P Q eta ∪
    witnesslessComponents P Q T b eta)
end SourceCompressionRetainedDiscard
namespace SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators
def sourceAlphaInclusion :
    SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode →*
      SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode where
  toFun g :=
    ⟨g.val,
      SoficGroups.SourceGeneration.alphaPrefixElementaryGroup_le_nine
        g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
end SourceGeneratedWordCrossing
namespace KunRootedUniversalToleranceNumerics
end KunRootedUniversalToleranceNumerics
namespace SourceBothCompressionNormalization
def sourceCompressionUElement :
    SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode :=
  ⟨SoficGroups.compressionU,
    SoficGroups.compressionU_mem_ninePrefixElementaryGroup⟩
def sourceCompressionVElement :
    SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode :=
  ⟨SoficGroups.compressionV,
    SoficGroups.compressionV_mem_ninePrefixElementaryGroup⟩
def sourceAlphaElement
    (g : SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode) :
    SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode :=
  ⟨g.val,
    SoficGroups.SourceGeneration.alphaPrefixElementaryGroup_le_nine
      g.property⟩
def sourceConjugatedAlphaUElement
    (g : SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode) :
    SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode := by
  refine ⟨SoficGroups.compressionU * g.val *
    SoficGroups.compressionU⁻¹, ?_⟩
  apply SoficGroups.alphaZero_prefixElementaryGroup_le
  rw [← SoficGroups.compressionU_map_alphaPrefixElementaryGroup]
  refine ⟨g.val, g.property, ?_⟩
  simp [MulAut.conj_apply]
def sourceConjugatedAlphaVElement
    (g : SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode) :
    SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode := by
  refine ⟨SoficGroups.compressionV * g.val *
    SoficGroups.compressionV⁻¹, ?_⟩
  apply SoficGroups.alphaZero_prefixElementaryGroup_le
  rw [← SoficGroups.compressionV_map_alphaPrefixElementaryGroup]
  refine ⟨g.val, g.property, ?_⟩
  simp [MulAut.conj_apply]
def sourceCompressionTable :
    Fin 2 → SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode :=
  ![sourceCompressionUElement, sourceCompressionVElement]
end SourceBothCompressionNormalization
namespace KunCompletedProductDiagonalSparseCut
open SoficGroups.KunDiagonalGoodRootGraphLoss
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
universe u
def completedDiagonalPermutationHom {V : Type*} :
    Equiv.Perm V →* Equiv.Perm (V × V) where
  toFun p := p.prodCongr p
  map_one' := by
    ext z <;> rfl
  map_mul' := by
    intro p q
    ext z <;> rfl
def completedGoodPermutationGraphIndicator
    {V : Type*} [DecidableEq V]
    (T : Finset (V × V)) (z : V × V) : ℝ :=
  if z ∈ T then 1 else 0
def completedGoodPermutationGraphRootedModel
    {G ι V : Type u} [Fintype V] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (φ : G → Equiv.Perm V)
    (p : Equiv.Perm V) (B : Finset V) :
    RootedIndicatorMarkovModel G ι where
  carrier := V × V
  fintype := inferInstance
  generator i := completedDiagonalPermutationHom (σ i)
  indicator := completedGoodPermutationGraphIndicator
    (goodPermutationGraph p B)
  evaluation g := completedDiagonalPermutationHom (φ g)
end KunCompletedProductDiagonalSparseCut
namespace KunTransportedAmbientOverlap
open Filter Topology
open scoped BigOperators symmDiff
end KunTransportedAmbientOverlap
namespace KunUniformCompletedRootRadiusImprovement
open SoficGroups.KunDiagonalGoodRootGraphLoss
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
universe u
end KunUniformCompletedRootRadiusImprovement
namespace CompletedChosenWordLocalRoot
open Filter Topology
open scoped BigOperators
def chosenWordEvaluation
    {G ι V : Type*}
    (σ : ι → Equiv.Perm V) (w : G → List ι) (g : G) :
    Equiv.Perm V :=
  ((w g).map σ).prod
end CompletedChosenWordLocalRoot
namespace CompletedSourceChosenWordRestrictionTransfer
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open SoficGroups.MatchedFirstStageWordRadiusTransfer
open scoped BigOperators
end CompletedSourceChosenWordRestrictionTransfer
namespace CompletedSourceFinalGeneratorTransfer
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CompletedSourceChosenWordRestrictionTransfer
end CompletedSourceFinalGeneratorTransfer
namespace CompletedPrescribedSpectralRadiusSchedule
open Filter Topology
open scoped Pointwise
def multiplicationBad
    {G V : Type*} [Group G] [Fintype V] [DecidableEq V]
    (φ : G → Equiv.Perm V) (a g : G) : Finset V :=
  Finset.univ.filter (fun x => φ (a * g) x ≠ (φ a * φ g) x)
def fixedRadiusRootBad
    {G V : Type*} [Group G] [DecidableEq G]
    [Fintype V] [DecidableEq V]
    (φ : G → Equiv.Perm V) (S : Finset G) (r : ℕ) : Finset V :=
  ((S ^ r).product (S ^ r)).biUnion fun ag =>
    multiplicationBad φ ag.1 ag.2
end CompletedPrescribedSpectralRadiusSchedule
namespace KunSourceUnconditionalFullDecomposition
section
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.KunActualRootedModelBridge
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
end
section
open Filter Topology
end
end KunSourceUnconditionalFullDecomposition
namespace KunActualCompressedSourceGroupFoundations
universe v
end KunActualCompressedSourceGroupFoundations
namespace KunExactKazhdanGeneratorChange
universe u v
theorem unitary_word_displacement_le
    {G : Type u} {H : Type v} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : SoficGroups.UnitaryRepresentation G H)
    (ξ : H) (l : List G) (δ : ℝ)
    (hletters : ∀ g ∈ l, ‖π g ξ - ξ‖ ≤ δ) :
    ‖π l.prod ξ - ξ‖ ≤ (l.length : ℝ) * δ := by
  induction l with
  | nil =>
      simp
  | cons g l ih =>
      have hg : ‖π g ξ - ξ‖ ≤ δ :=
        hletters g (by simp)
      have htail :
          ∀ a ∈ l, ‖π a ξ - ξ‖ ≤ δ := by
        intro a ha
        exact hletters a (by simp [ha])
      have hword := ih htail
      calc
        ‖π (g :: l).prod ξ - ξ‖ =
            ‖π g (π l.prod ξ - ξ) + (π g ξ - ξ)‖ := by
              congr 1
              simp [map_mul, map_sub]
        _ ≤ ‖π g (π l.prod ξ - ξ)‖ +
              ‖π g ξ - ξ‖ := norm_add_le _ _
        _ = ‖π l.prod ξ - ξ‖ + ‖π g ξ - ξ‖ := by
              rw [LinearIsometryEquiv.norm_map]
        _ ≤ (l.length : ℝ) * δ + δ := by linarith
        _ = ((g :: l).length : ℝ) * δ := by
              simp
              ring
theorem exists_word_of_symmetric_generating_finset
    {G : Type u} [Group G] (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    ∃ l : List ↥S, ((l.map fun i : ↥S => (i : G)).prod) = g := by
  classical
  have hg : g ∈ Subgroup.closure (S : Set G) := by
    rw [hgenerates]
    simp
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      exact ⟨[⟨x, hx⟩], by simp⟩
  | one =>
      exact ⟨[], by simp⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨lx, hlx⟩ := ihx
      obtain ⟨ly, hly⟩ := ihy
      refine ⟨lx ++ ly, ?_⟩
      rw [List.map_append, List.prod_append, hlx, hly]
  | inv x _ ih =>
      obtain ⟨l, hl⟩ := ih
      let invLetter : ↥S → ↥S :=
        fun i => ⟨(i : G)⁻¹, hsymmetric (i : G) i.property⟩
      refine ⟨(l.map invLetter).reverse, ?_⟩
      rw [List.map_reverse, List.map_map]
      change ((l.map fun i : ↥S => (i : G)⁻¹).reverse).prod = x⁻¹
      have hmap :
          (l.map fun i : ↥S => (i : G)⁻¹) =
            (l.map fun i : ↥S => (i : G)).map
              (fun z : G => z⁻¹) := by
        rw [List.map_map]
        rfl
      rw [hmap, ← List.prod_inv_reverse, hl]
def symmetricGeneratingWord
    {G : Type u} [Group G] (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    List ↥S :=
  (exists_word_of_symmetric_generating_finset
    S hsymmetric hgenerates g).choose
theorem symmetricGeneratingWord_prod
    {G : Type u} [Group G] (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    (((symmetricGeneratingWord S hsymmetric hgenerates g).map
      fun i : ↥S => (i : G)).prod) = g :=
  (exists_word_of_symmetric_generating_finset
    S hsymmetric hgenerates g).choose_spec
def kazhdanPairOnSymmetricGeneratingFinset
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, v} G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) :
    SoficGroups.KazhdanPair.{u, v} G := by
  classical
  let w : G → List ↥S :=
    symmetricGeneratingWord S hsymmetric hgenerates
  let L : ℕ := 1 + ∑ g ∈ P.generators, (w g).length
  have hL : 0 < L := by
    dsimp [L]
    omega
  have hLreal : 0 < (L : ℝ) := by
    exact_mod_cast hL
  refine
    { generators := S
      kazhdanConstant := P.kazhdanConstant / (L : ℝ)
      positive := div_pos P.positive hLreal
      invariant := ?_ }
  intro H _ _ _ π ξ hξ hS
  apply P.invariant H π ξ hξ
  intro g hg
  have hlength :
      (w g).length < L := by
    have hsingle :
        (w g).length ≤
          ∑ a ∈ P.generators, (w a).length :=
      Finset.single_le_sum
        (fun a _ => Nat.zero_le (w a).length) hg
    dsimp [L]
    omega
  have hlengthreal :
      ((w g).length : ℝ) < (L : ℝ) := by
    exact_mod_cast hlength
  have hδ : 0 < P.kazhdanConstant / (L : ℝ) :=
    div_pos P.positive hLreal
  have hword :
      ‖π (((w g).map fun i : ↥S => (i : G)).prod) ξ - ξ‖ ≤
        ((w g).length : ℝ) *
          (P.kazhdanConstant / (L : ℝ)) := by
    have hbound :=
      unitary_word_displacement_le π ξ
        ((w g).map fun i : ↥S => (i : G))
        (P.kazhdanConstant / (L : ℝ))
        (by
          intro a ha
          obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp ha
          exact (hS (i : G) i.property).le)
    simpa only [List.length_map] using hbound
  calc
    ‖π g ξ - ξ‖ =
        ‖π (((w g).map fun i : ↥S => (i : G)).prod) ξ - ξ‖ := by
          rw [show
            (((w g).map fun i : ↥S => (i : G)).prod) = g from
              symmetricGeneratingWord_prod
                S hsymmetric hgenerates g]
    _ ≤ ((w g).length : ℝ) *
          (P.kazhdanConstant / (L : ℝ)) := hword
    _ < (L : ℝ) * (P.kazhdanConstant / (L : ℝ)) :=
      mul_lt_mul_of_pos_right hlengthreal hδ
    _ = P.kazhdanConstant := by
      field_simp [Nat.cast_ne_zero.mpr hL.ne']
end KunExactKazhdanGeneratorChange
namespace KunExactActualSourceAmbientGenerators
section
open SoficGroups.KunExactKazhdanGeneratorChange
def sourceAlphaInclusion :
    SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode →*
      SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode where
  toFun g :=
    ⟨g.val,
      SoficGroups.SourceGeneration.alphaPrefixElementaryGroup_le_nine
        g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
def sourceCompressionU :
    SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode :=
  ⟨SoficGroups.compressionU,
    SoficGroups.compressionU_mem_ninePrefixElementaryGroup⟩
def sourceCompressionV :
    SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode :=
  ⟨SoficGroups.compressionV,
    SoficGroups.compressionV_mem_ninePrefixElementaryGroup⟩
noncomputable def sourcePositiveGenerators
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) :
    Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode) := by
  classical
  exact SΓ.image sourceAlphaInclusion ∪
    {sourceCompressionU, sourceCompressionV}
noncomputable def sourceAmbientSymmetricGenerators
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) :
    Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode) := by
  classical
  exact insert 1
    (sourcePositiveGenerators SΓ ∪
      (sourcePositiveGenerators SΓ).image fun g => g⁻¹)
end
section
def sourceCompressionTable :
    Fin 2 →
      SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode :=
  ![sourceCompressionU, sourceCompressionV]
def sourcePositiveGeneratorMap
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) :
    (↥SΓ ⊕ Fin 2) →
      SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode :=
  Sum.elim (fun i : ↥SΓ => sourceAlphaInclusion (i :
    SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    sourceCompressionTable
end
end KunExactActualSourceAmbientGenerators
namespace KunUnconditionalActualSourceGeneratorData
open SoficGroups.KunExactKazhdanGeneratorChange
open SoficGroups.KunExactActualSourceAmbientGenerators
end KunUnconditionalActualSourceGeneratorData
namespace SourceCommonComponentComparisonBad
open Filter Topology
open scoped BigOperators
noncomputable def comparisonBad
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : Equiv.Perm V) (eta : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    ¬ (1 - eta) * (SoficGroups.partitionComponentSize Q x : ℝ) ≤
      (SoficGroups.partitionComponentSize Q (p x) : ℝ)
noncomputable def familyComparisonBad
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : ι → Equiv.Perm V) (eta : ℝ) : Finset (ι × V) := by
  classical
  exact Finset.univ.filter fun e =>
    ¬ (1 - eta) * (SoficGroups.partitionComponentSize Q e.2 : ℝ) ≤
      (SoficGroups.partitionComponentSize Q (p e.1 e.2) : ℝ)
noncomputable def overlapRetainedComponents
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (eta : ℝ) : Finset (Finset V) :=
  (SoficGroups.transportedUnivFinpartition Q T).parts \
    SoficGroups.insufficientOverlapComponents
      (SoficGroups.transportedUnivFinpartition Q T) Q eta
end SourceCommonComponentComparisonBad
namespace SourceCommonOffsetMidrankEnergy
open Filter Topology
open scoped BigOperators
noncomputable def realComponentSize
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V)) (x : V) : ℝ :=
  (SoficGroups.partitionComponentSize Q x : ℝ)
noncomputable def componentLogRank
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (H r : ℝ) : V → ℤ :=
  SoficGroups.MidrankPermutationEnergy.offsetFloorRank
    (fun x => Real.log (realComponentSize Q x)) H r
noncomputable def componentSizeComparisonBad
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : ι → Equiv.Perm V) (eta : ℝ) : Finset (ι × V) := by
  classical
  exact Finset.univ.filter fun e =>
    ¬ (1 - eta) * realComponentSize Q e.2 ≤
      realComponentSize Q (p e.1 e.2)
end SourceCommonOffsetMidrankEnergy
namespace SourceCommonComponentRankNoBad
open Filter Topology
open scoped BigOperators
end SourceCommonComponentRankNoBad
namespace KunPositiveWordMidrankEnergy
open Filter Topology
open scoped BigOperators
noncomputable def squaredPermutationEnergy
    {V : Type*} [Fintype V] (f : V → ℝ) (p : Equiv.Perm V) : ℝ :=
  ∑ x : V, (f (p x) - f x) ^ 2
end KunPositiveWordMidrankEnergy
namespace KunAdditiveMedianPoincare
open SoficGroups.CheegerPoincare
open Filter Topology
open scoped BigOperators
def permutationRealVariation
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) : ℝ :=
  ∑ i : ι, ∑ x : V, |f (σ i x) - f x|
end KunAdditiveMedianPoincare
namespace KunCompletedComponentMidrankVariation
open Filter Topology
open scoped BigOperators
def permutationRealVariation
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) : ℝ :=
  ∑ i : ι, ∑ x : V, |f (σ i x) - f x|
end KunCompletedComponentMidrankVariation
namespace KunGlobalActualAdditiveMidrankVariance
open Filter Topology
open scoped BigOperators
end KunGlobalActualAdditiveMidrankVariance
namespace KunCommonRankArcInvariance
open Filter Topology
open scoped BigOperators
end KunCommonRankArcInvariance
namespace ChosenCayleyMatchedComponentRealization
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.KunResidualRetainedSelection
open scoped BigOperators Pointwise symmDiff
def sourceFirstFactorApproximation
    {K J : Type*} [Group K] [Group J]
    (A : SoficGroups.SoficApproximation (K × J)) :
    SoficGroups.SoficApproximation K :=
  SoficGroups.pullbackSoficApproximation
    (MonoidHom.inl K J)
    (fun _ _ h => congrArg Prod.fst h)
    A
def sourceFirstFactorCayleyRadiusBad
    {K J : Type*} [Group K] [Group J] [DecidableEq K]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (n k : ℕ) : Finset (Fin (A.model n).size) :=
  chosenCayleyRadiusBad
    (sourceFirstFactorApproximation A)
    S (symmetricGeneratorWord S hsymmetric hgenerates) n k
end ChosenCayleyMatchedComponentRealization
namespace CanonicalProductRadiusBadMatchedCapture
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.ChosenCayleyMatchedComponentRealization
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open scoped BigOperators Pointwise symmDiff
def sourceProductRadiusLabels
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (S : Finset K) (F : Finset J) (k : ℕ) :
    Finset (K × J) :=
  ((S ^ k).image fun a : K => (a, (1 : J))) ∪
    (((SoficGroups.CompressionCriterion.productTrackedTable F).image
      fun j : J => ((1 : K), j)) ∪
      (S.biUnion fun a =>
        (SoficGroups.CompressionCriterion.productTrackedTable F).image
          fun j : J => (a, j)))
def canonicalProductRadiusBad
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (n k : ℕ) :
    Finset (Fin (A.model n).size) :=
  sourceFirstFactorCayleyRadiusBad
    A S hsymmetric hgenerates n k ∪
      finiteRootBad (A.model n)
        (sourceProductRadiusLabels S F k)
end CanonicalProductRadiusBadMatchedCapture
namespace CompletedSelectedCentralizerPairwiseSource
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedFirstStageWordRadiusTransfer
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open scoped BigOperators Pointwise
end CompletedSelectedCentralizerPairwiseSource
namespace KunActualSelectedCentralizerFiniteModel
open Filter Topology
noncomputable def trackedCompletedAlmostCentralizer
    {V ι J : Type} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V)
    (p : J → Equiv.Perm V)
    (F : Finset J) (t : ℕ)
    (hdefect : ∀ j ∈ SoficGroups.CompressionCriterion.productTrackedTable F,
      SoficGroups.permutationCommutationDefect σ (p j) ≤ t) :
    J → SoficGroups.AlmostCentralizerElement σ t := by
  classical
  intro j
  by_cases hj : j ∈ SoficGroups.CompressionCriterion.productTrackedTable F
  · exact ⟨p j, hdefect j hj⟩
  · exact ⟨1, by simp⟩
end KunActualSelectedCentralizerFiniteModel
namespace SourceTopLevelCompression
open Filter
end SourceTopLevelCompression
namespace ThompsonFFiniteQuotient
variable {G : Type*} [Group G]
def conjugateTerm (a b : G) (n : ℕ) : G :=
  (a ^ n)⁻¹ * b * a ^ n
end ThompsonFFiniteQuotient
namespace ThompsonFTwoRelatorLEF
open scoped commutatorElement
def thompsonFRelator (n : ℕ) : FreeGroup (Fin 2) :=
  ⁅FreeGroup.of (0 : Fin 2) * (FreeGroup.of (1 : Fin 2))⁻¹,
    ((FreeGroup.of (0 : Fin 2)) ^ n)⁻¹ *
      FreeGroup.of (1 : Fin 2) * (FreeGroup.of (0 : Fin 2)) ^ n⁆
def thompsonFGeneratorCommutator : FreeGroup (Fin 2) :=
  ⁅FreeGroup.of (0 : Fin 2), FreeGroup.of (1 : Fin 2)⁆
end ThompsonFTwoRelatorLEF
namespace ThompsonFLocalWitness
open ThompsonPrefixInsertion
def rootRotation : BinaryLeavittˣ :=
  cylinderSwap [0] [1, 0] (by decide) (by decide) *
    cylinderSwap [0] [1, 1] (by decide) (by decide) *
    cylinderSwap [0] [1] (by decide) (by decide)
def rightRotation : BinaryLeavittˣ :=
  prefixInsertionHom [1] rootRotation
def generatorA : BinaryLeavittˣ := rootRotation⁻¹
def generatorB : BinaryLeavittˣ := rightRotation⁻¹
theorem generatorB_eq_prefixInsertion :
    generatorB = prefixInsertionHom [1] generatorA := by
  change
    (prefixInsertionHom [1] rootRotation)⁻¹ =
      prefixInsertionHom [1] rootRotation⁻¹
  exact ((prefixInsertionHom [1]).map_inv rootRotation).symm
theorem cylinderSwap_mem_binaryPrefixTranspositionGroup
    (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    cylinderSwap a b hab hba ∈ binaryPrefixTranspositionGroup :=
  Subgroup.subset_closure ⟨a, b, hab, hba, rfl⟩
theorem rootRotation_mem_binaryPrefixTranspositionGroup :
    rootRotation ∈ binaryPrefixTranspositionGroup := by
  unfold rootRotation
  exact binaryPrefixTranspositionGroup.mul_mem
    (binaryPrefixTranspositionGroup.mul_mem
      (cylinderSwap_mem_binaryPrefixTranspositionGroup
        [0] [1, 0] (by decide) (by decide))
      (cylinderSwap_mem_binaryPrefixTranspositionGroup
        [0] [1, 1] (by decide) (by decide)))
    (cylinderSwap_mem_binaryPrefixTranspositionGroup
      [0] [1] (by decide) (by decide))
theorem generatorA_mem_binaryPrefixTranspositionGroup :
    generatorA ∈ binaryPrefixTranspositionGroup :=
  binaryPrefixTranspositionGroup.inv_mem
    rootRotation_mem_binaryPrefixTranspositionGroup
theorem generatorB_mem_binaryPrefixTranspositionGroup :
    generatorB ∈ binaryPrefixTranspositionGroup := by
  rw [generatorB_eq_prefixInsertion]
  exact prefixInsertionHom_mem_binaryPrefixTranspositionGroup
    [1] generatorA generatorA_mem_binaryPrefixTranspositionGroup
def sourceGeneratorA :
    localPrefixTranspositionGroup ThompsonPrefixLocal.sourceLocalWord :=
  ⟨prefixInsertionHom ThompsonPrefixLocal.sourceLocalWord generatorA,
    ⟨generatorA, generatorA_mem_binaryPrefixTranspositionGroup, rfl⟩⟩
def sourceGeneratorB :
    localPrefixTranspositionGroup ThompsonPrefixLocal.sourceLocalWord :=
  ⟨prefixInsertionHom ThompsonPrefixLocal.sourceLocalWord generatorB,
    ⟨generatorB, generatorB_mem_binaryPrefixTranspositionGroup, rfl⟩⟩
end ThompsonFLocalWitness
section
end
namespace KunUnconditionalActualSourceDecomposition
open Filter Topology
open SoficGroups.KunSourceUnconditionalFullDecomposition
open SoficGroups.KunExactActualSourceAmbientGenerators
open SoficGroups.KunUnconditionalActualSourceGeneratorData
end KunUnconditionalActualSourceDecomposition
namespace KunCombinedPrescribedRootSourceTolerance
open Filter Topology
end KunCombinedPrescribedRootSourceTolerance
namespace KunLiteralSourceSelectedComponents
open Filter Topology
open scoped BigOperators Pointwise
def sourceConjugacyDisagreementBad
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (u g : G) (n : ℕ) : Finset (Fin (A.model n).size) := by
  classical
  exact Finset.univ.filter fun x =>
    (A.model n).action (u * g * u⁻¹) x ≠
      ((A.model n).action u * (A.model n).action g *
        ((A.model n).action u)⁻¹) x
end KunLiteralSourceSelectedComponents
namespace KunActualBothTransportedOverlapScales
open Filter Topology
open scoped BigOperators
end KunActualBothTransportedOverlapScales
namespace SourceProductThroughAlpha
open Filter Topology
open scoped BigOperators
universe v
def sourceCompressionUAlphaHom :
    SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode →*
      SoficGroups.prefixElementaryGroup SoficGroups.alphaZeroPrefixCode :=
  ((MulAut.conj SoficGroups.compressionU).toMonoidHom.comp
    (SoficGroups.prefixElementaryGroup
      SoficGroups.alphaPrefixCode).subtype).codRestrict
        (SoficGroups.prefixElementaryGroup
          SoficGroups.alphaZeroPrefixCode)
        (by
          intro g
          rw [← SoficGroups.compressionU_map_alphaPrefixElementaryGroup]
          exact ⟨g.val, g.property, rfl⟩)
noncomputable def sourceCompressionUAlphaEquiv :
    SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode ≃*
      SoficGroups.prefixElementaryGroup SoficGroups.alphaZeroPrefixCode := by
  apply MulEquiv.ofBijective sourceCompressionUAlphaHom
  constructor
  · intro g g' heq
    apply Subtype.ext
    apply (MulAut.conj SoficGroups.compressionU).injective
    exact congrArg
      (fun k : SoficGroups.prefixElementaryGroup
          SoficGroups.alphaZeroPrefixCode =>
        (k : SoficGroups.BinaryLeavittˣ)) heq
  · intro k
    have hk :
        (k : SoficGroups.BinaryLeavittˣ) ∈
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode).map
              (MulAut.conj SoficGroups.compressionU).toMonoidHom := by
      rw [SoficGroups.compressionU_map_alphaPrefixElementaryGroup]
      exact k.property
    obtain ⟨g, hg, heq⟩ := hk
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Subtype.ext
    exact heq
noncomputable def sourceCompressedGeneratingFinset
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) :
    Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaZeroPrefixCode) := by
  classical
  exact SΓ.image sourceCompressionUAlphaEquiv
theorem sourceCompressedGeneratingFinset_inv_mem
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (k : SoficGroups.prefixElementaryGroup
      SoficGroups.alphaZeroPrefixCode)
    (hk : k ∈ sourceCompressedGeneratingFinset SΓ) :
    k⁻¹ ∈ sourceCompressedGeneratingFinset SΓ := by
  classical
  change k ∈ SΓ.image sourceCompressionUAlphaEquiv at hk
  change k⁻¹ ∈ SΓ.image sourceCompressionUAlphaEquiv
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hk
  exact Finset.mem_image.mpr
    ⟨g⁻¹, hsymmetric g hg,
      map_inv sourceCompressionUAlphaEquiv g⟩
theorem sourceCompressedGeneratingFinset_closure
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) =
          ⊤) :
    Subgroup.closure
      (sourceCompressedGeneratingFinset SΓ : Set
        (SoficGroups.prefixElementaryGroup
          SoficGroups.alphaZeroPrefixCode)) = ⊤ := by
  classical
  change Subgroup.closure
    ((SΓ.image sourceCompressionUAlphaEquiv : Finset
      (SoficGroups.prefixElementaryGroup
        SoficGroups.alphaZeroPrefixCode)) : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaZeroPrefixCode)) = ⊤
  rw [Finset.coe_image]
  change
    Subgroup.closure
      (sourceCompressionUAlphaEquiv.toMonoidHom ''
        (SΓ : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode))) = ⊤
  rw [← MonoidHom.map_closure, hgenerates,
    Subgroup.map_top_of_surjective
      sourceCompressionUAlphaEquiv.toMonoidHom
      sourceCompressionUAlphaEquiv.surjective]
def sourceCompressedLocalProductToAlpha :
    (SoficGroups.prefixElementaryGroup SoficGroups.alphaZeroPrefixCode ×
      SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
        SoficGroups.ThompsonPrefixLocal.sourceLocalWord) →*
      SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode :=
  SoficGroups.ThompsonPrefixInsertion.sourceCompressedLocalProductHom.codRestrict
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)
      (by
        intro x
        change
          (x.1 : SoficGroups.BinaryLeavittˣ) *
            (x.2 : SoficGroups.BinaryLeavittˣ) ∈
              SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode
        exact
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode).mul_mem
              (SoficGroups.alphaZero_prefixElementaryGroup_le x.1.property)
              (SoficGroups.ThompsonPrefixInsertion.sourceLocalPrefixTranspositionGroup_le_alpha_sourceWord
                  x.2.property))
def sourceCompressedLocalProductApproximation
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode)) :
    SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup
          SoficGroups.alphaZeroPrefixCode ×
        SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
            SoficGroups.ThompsonPrefixLocal.sourceLocalWord) :=
  SoficGroups.pullbackSoficApproximation
    SoficGroups.ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
    SoficGroups.ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding_injective
    A
@[simp]
theorem sourceCompressedLocalProductApproximation_model_size
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (n : ℕ) :
    ((sourceCompressedLocalProductApproximation A).model n).size =
      (A.model n).size := by
  rfl
end SourceProductThroughAlpha
namespace SourceRetainedActualMatching
open Filter Topology
open scoped BigOperators symmDiff
noncomputable def logarithmicComponentRank
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (H r : ℝ) : V → ℤ :=
  SoficGroups.MidrankPermutationEnergy.offsetFloorRank
    (fun x => Real.log (SoficGroups.partitionComponentSize Q x : ℝ))
    H r
noncomputable def retainedTransportedComponents
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (H r eta : ℝ) : Finset (Finset V) :=
  SoficGroups.SourceCompressionRetainedDiscard.retainedComponents
    (SoficGroups.transportedUnivFinpartition Q T) Q T
    (logarithmicComponentRank Q H r) eta
end SourceRetainedActualMatching
namespace KunActualBothTransportedOverlapScales
open Filter Topology
open scoped BigOperators
end KunActualBothTransportedOverlapScales
namespace KunLiteralNineSourceCompletedCentralizerModels
open Filter Topology
open scoped BigOperators
end KunLiteralNineSourceCompletedCentralizerModels
namespace KunActualFirstStageReferenceExpansion
open Filter Topology
open scoped BigOperators
def componentGeneratorDisagreement
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (C : Finset V)
    (σref σact : ι → Equiv.Perm V) : ℕ :=
  ∑ i : ι, (C.filter fun x => σref i x ≠ σact i x).card
def normalizedReferenceCompletionError
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (C : Finset V) (σref σact : ι → Equiv.Perm V) : ℝ :=
  ((SoficGroups.boundary σref C : ℝ) +
    2 * (componentGeneratorDisagreement C σref σact : ℝ)) /
      (C.card : ℝ)
end KunActualFirstStageReferenceExpansion
namespace SourceProductThroughAlpha
open Filter Topology
open scoped BigOperators
end SourceProductThroughAlpha
namespace KunLiteralSourceSelectedComponents
open Filter Topology
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open SoficGroups.SourceProductThroughAlpha
open scoped BigOperators Pointwise
def sourceCompressionPermutation
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (n : ℕ) : Equiv.Perm (Fin (A.model n).size) :=
  (A.model n).action
    SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement
def sourceTransportedReferenceGenerators
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (n : ℕ) : ↥S → Equiv.Perm (Fin (A.model n).size) :=
  fun g => sourceCompressionPermutation A n *
    (A.model n).action
      (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion g) *
    (sourceCompressionPermutation A n)⁻¹
def sourceTransportedPartition
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (Q : (n : ℕ) →
      Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
    (n : ℕ) :
    Finpartition (Finset.univ : Finset (Fin (A.model n).size)) :=
  SoficGroups.transportedUnivFinpartition
    (Q n) (sourceCompressionPermutation A n)
noncomputable def sourceGeneratorFamilyConjugacyBad
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (n : ℕ) : Finset (Fin (A.model n).size) :=
  S.biUnion fun g => sourceConjugacyDisagreementBad A
    SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement
    (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion g) n
noncomputable def sourceSelectedRadiusBad
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (SoficGroups.prefixElementaryGroup
          SoficGroups.alphaPrefixCode)) = ⊤)
    (F : Finset
      (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
        SoficGroups.ThompsonPrefixLocal.sourceLocalWord))
    (n k : ℕ) : Finset (Fin (A.model n).size) := by
  classical
  let SK :=
    SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset S
  let AP :=
    SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation A
  exact
    SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
      AP SK
      (SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset_inv_mem
        S hsymmetric)
      (SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset_closure
        S hgenerates)
      F n k ∪ sourceGeneratorFamilyConjugacyBad A S n
end KunLiteralSourceSelectedComponents
namespace SourceGuardedCanonicalSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff
abbrev SourceK :=
  SoficGroups.prefixElementaryGroup SoficGroups.alphaZeroPrefixCode
abbrev SourceJ :=
  SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
    SoficGroups.ThompsonPrefixLocal.sourceLocalWord
noncomputable def guardedCanonicalProductRadiusBad
    [DecidableEq SourceK] [DecidableEq SourceJ]
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) =
          ⊤)
    (F : Finset SourceJ)
    (E : (n : ℕ) → ℕ → Finset (Fin (A.model n).size))
    (n k : ℕ) : Finset (Fin (A.model n).size) :=
  SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
    (SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation A)
    (SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset SΓ)
    (SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset_inv_mem
      SΓ hsymmetric)
    (SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset_closure
      SΓ hgenerates)
    F n k ∪ E n k
end SourceGuardedCanonicalSelection
namespace KunActualSourceURetainedNoPremise
open Filter Topology
open scoped BigOperators symmDiff
end KunActualSourceURetainedNoPremise
namespace KunLiteralSourceSelectedComponents
open Filter Topology
open scoped BigOperators Pointwise
noncomputable def sourceSelectedProductRadiusLabels
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (F : Finset
      (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
        SoficGroups.ThompsonPrefixLocal.sourceLocalWord))
    (k : ℕ) :
    Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaZeroPrefixCode ×
        SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
          SoficGroups.ThompsonPrefixLocal.sourceLocalWord) := by
  classical
  exact
    SoficGroups.CanonicalProductRadiusBadMatchedCapture.sourceProductRadiusLabels
      (SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset S)
      F k
end KunLiteralSourceSelectedComponents
namespace SourceProductThroughAlpha
open scoped BigOperators
noncomputable def sourceCompressedGeneratorSubtypeEquiv
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) :
    (↥SΓ) ≃
      (↥(sourceCompressedGeneratingFinset SΓ)) := by
  classical
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro g
    refine ⟨sourceCompressionUAlphaEquiv (g :
      SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode), ?_⟩
    change sourceCompressionUAlphaEquiv (g :
      SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode) ∈
        SΓ.image sourceCompressionUAlphaEquiv
    exact Finset.mem_image.mpr ⟨g, g.property, rfl⟩
  · intro k
    refine ⟨sourceCompressionUAlphaEquiv.symm (k :
      SoficGroups.prefixElementaryGroup SoficGroups.alphaZeroPrefixCode), ?_⟩
    have hk :
        (k : SoficGroups.prefixElementaryGroup
          SoficGroups.alphaZeroPrefixCode) ∈
          SΓ.image sourceCompressionUAlphaEquiv := by
      exact k.property
    obtain ⟨g, hg, heq⟩ := Finset.mem_image.mp hk
    rw [← heq, sourceCompressionUAlphaEquiv.symm_apply_apply]
    exact hg
  · intro g
    apply Subtype.ext
    exact sourceCompressionUAlphaEquiv.symm_apply_apply _
  · intro k
    apply Subtype.ext
    exact sourceCompressionUAlphaEquiv.apply_symm_apply _
end SourceProductThroughAlpha
namespace KunGuardedCanonicalMatchedDensity
open Filter Topology
end KunGuardedCanonicalMatchedDensity
namespace KunActualCanonicalSelectedPruning
open Filter Topology
open SoficGroups.MatchedComponentCompletion
end KunActualCanonicalSelectedPruning
namespace KunActualCanonicalPrunedSourceBadDensity
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
end KunActualCanonicalPrunedSourceBadDensity
namespace KunActualTwicePrunedFirstFactorRootBad
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open scoped BigOperators Pointwise
noncomputable def restrictionMultiplicationBad
    {V : Type*} [DecidableEq V]
    (p q r : Equiv.Perm V) (Z : Finset V) : Finset V :=
  Z.filter (fun x => q x ∉ Z ∨ r x ∉ Z ∨ r x ≠ p (q x))
end KunActualTwicePrunedFirstFactorRootBad
namespace KunActualSelectedPrunedSourceFiniteModelBridge
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.KunActualSoficRootRadius
open scoped BigOperators Pointwise
end KunActualSelectedPrunedSourceFiniteModelBridge
namespace KunActualCanonicalSelectedFiniteModelComposition
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
end KunActualCanonicalSelectedFiniteModelComposition
namespace KunLiteralSourceSelectedComponents
end KunLiteralSourceSelectedComponents
namespace KunActualSourceSelectedCompletedGeneratorExpansion
open Filter Topology
open scoped BigOperators
end KunActualSourceSelectedCompletedGeneratorExpansion
namespace KunLiteralNineSourceFiniteModels
open Filter Topology
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open scoped BigOperators Pointwise
end KunLiteralNineSourceFiniteModels
namespace SourceTopLevelCompressionFinal
open SoficGroups.SourceTopLevelCompression
open SoficGroups.KunLiteralNineSourceFiniteModels
end SourceTopLevelCompressionFinal
end SoficGroups
end


