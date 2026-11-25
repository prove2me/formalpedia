-- Prove2me | Definitions.Def_RPLib_FX_EtP1_12
-- name    : RPLib_FX_EtP1_12
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T03:26:20.849239+00:00
-- url     : https://prove2.me/theorems/ba2faa8a-7e4f-46e4-9747-717de8188646
-- title:
--   Étale cohomology of the projective line, library file 12 of 34
-- statement:
--   File 12 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
--   * `S4.Def_RP_EtSheaves_LiftRing`: S4-EtSheaves, part 17: lifting standard etale algebras along a surjection
--   * `S4.Def_RP_EtCompact_ExtAdj`: S4-EtCompact, part 1: `Ext` along an adjunction
--   * `S4.Def_RP_CdOne_Lc`: S4-PD (3), group layer part 1: locally constant cochains and the index lemma
--   * `S4.Def_RP_CdOne_Grp`: S4-PD (3), group layer part 2: Sylow reduction and `ℤ/l` coefficients
--   * `S4.Def_RP_CdOne_Dev`: S4-PD (3), group layer part 3: dévissage and `H²(P, A) = 0`
--   * `S4.Def_RP_CdOne_Wrap`: S4-PD (3), group layer part 4: wrappers for `cd_l ≤ 1`
--   * `S4.Def_RP_CdOne_Emb`: S4-PD (3b): the central embedding problem with kernel `μ_l`
--   * `S4.Def_RP_CdOne_Field`: S4-PD (3), field layer: `HypL` for `Gal(Ω/E₀)` from Tsen + Kummer
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_11

/-!
# Étale cohomology of the projective line, library file 12 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
* `S4.Def_RP_EtSheaves_LiftRing`: S4-EtSheaves, part 17: lifting standard etale algebras along a surjection
* `S4.Def_RP_EtCompact_ExtAdj`: S4-EtCompact, part 1: `Ext` along an adjunction
* `S4.Def_RP_CdOne_Lc`: S4-PD (3), group layer part 1: locally constant cochains and the index lemma
* `S4.Def_RP_CdOne_Grp`: S4-PD (3), group layer part 2: Sylow reduction and `ℤ/l` coefficients
* `S4.Def_RP_CdOne_Dev`: S4-PD (3), group layer part 3: dévissage and `H²(P, A) = 0`
* `S4.Def_RP_CdOne_Wrap`: S4-PD (3), group layer part 4: wrappers for `cd_l ≤ 1`
* `S4.Def_RP_CdOne_Emb`: S4-PD (3b): the central embedding problem with kernel `μ_l`
* `S4.Def_RP_CdOne_Field`: S4-PD (3), field layer: `HypL` for `Gal(Ω/E₀)` from Tsen + Kummer
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtSheaves_Closed =====
section

/-!
# S4-EtSheaves, part 14: `i_*` vanishes off `Z`

For `i : Z ⟶ X` and an etale `j : U ⟶ X` whose image misses the image of `i`, the restriction
`j^* i_* G` is the zero sheaf: its values are those of `G` on the empty schemes `W ×_X Z`.
Hence the stalks of `i_* G` vanish at geometric points outside the (closed) image of `i`, every
map `j_! G' ⟶ i_* G` is zero, and `j_! j^* F ⟶ F ⟶ i_* i^* F` is a complex.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [Etale j]

theorem range_complOpens_ι [IsClosedImmersion i] :
    Set.range (complOpens i).ι = (Set.range i)ᶜ := Scheme.Opens.range_ι _

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_LiftRing =====
section

/-!
# S4-EtSheaves, part 17: lifting standard etale algebras along a surjection

If `A → R` is surjective and `S` is a standard etale `R`-algebra, there is a standard etale
`A`-algebra `P.Ring` with `S ≃ₐ[R] R ⊗[A] P.Ring`: lift `f` to a monic `F`, lift `g` to any `G`
and use the pair `(F, G * F')`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial TensorProduct

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
  (hφ : Function.Surjective (algebraMap A R)) (Q : StandardEtalePair R)

include hφ

theorem exists_monic_lift : ∃ F : A[X], F.map (algebraMap A R) = Q.f ∧ F.Monic := by
  obtain ⟨F, h1, -, h2⟩ := lifts_and_natDegree_eq_and_monic
    (mem_lifts_of_surjective hφ Q.f) Q.monic_f
  exact ⟨F, h1, h2⟩

/-- The lifted standard etale pair `(F, G * F')`. -/
def liftPair : StandardEtalePair A where
  f := (exists_monic_lift hφ Q).choose
  monic_f := (exists_monic_lift hφ Q).choose_spec.2
  g := (map_surjective _ hφ Q.g).choose * derivative (exists_monic_lift hφ Q).choose
  cond := ⟨(map_surjective _ hφ Q.g).choose, 0, 1, by ring⟩

theorem liftPair_map_f : ((liftPair hφ Q).map (algebraMap A R)).f = Q.f :=
  (exists_monic_lift hφ Q).choose_spec.1

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtCompact_ExtAdj =====
section

/-!
# S4-EtCompact, part 1: `Ext` along an adjunction

For an adjunction `L ⊣ R` between abelian categories with `R` exact and `L` preserving
monomorphisms (so `R` preserves injective objects), the map
`e ↦ mk₀ (η_A) ∘ R(e) : Ext (L A) B n → Ext A (R B) n` is bijective.
Proof: induction on `n` with injective presentations of `B`, as in
`Functor.mapExt_bijective_of_preservesInjectiveObjects`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

universe w v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable [HasExt.{w} C] [HasExt.{w} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

theorem extAdjMap_apply (A : C) (B : D) (n : ℕ) (e : Ext (L.obj A) B n) :
    extAdjMap adj A B n e = (Ext.mk₀ (adj.unit.app A)).comp (e.mapExactFunctor R) (zero_add n) :=
  rfl

theorem extAdjMap_mk₀ (A : C) (B : D) (f : L.obj A ⟶ B) :
    extAdjMap adj A B 0 (Ext.mk₀ f) = Ext.mk₀ (adj.homEquiv A B f) := by
  rw [extAdjMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Adjunction.homEquiv_unit]

theorem extAdjMap_zero_bijective (A : C) (B : D) : Function.Bijective (extAdjMap adj A B 0) := by
  have h : (extAdjMap adj A B 0 : Ext (L.obj A) B 0 → Ext A (R.obj B) 0) =
      Ext.mk₀ ∘ adj.homEquiv A B ∘ Ext.homEquiv₀ := by
    funext x
    obtain ⟨y, rfl⟩ := (Ext.mk₀_bijective (L.obj A) B).2 x
    simp only [Function.comp_apply, extAdjMap_mk₀]
    congr 2
    exact (Ext.homEquiv₀.apply_symm_apply y).symm
  rw [h]
  exact (Ext.mk₀_bijective _ _).comp ((adj.homEquiv A B).bijective.comp Ext.homEquiv₀.bijective)

theorem extAdjMap_comp_mk₀ (A : C) {B B' : D} (g : B ⟶ B') {n : ℕ} (x : Ext (L.obj A) B n) :
    extAdjMap adj A B' n (x.comp (Ext.mk₀ g) (add_zero n)) =
      (extAdjMap adj A B n x).comp (Ext.mk₀ (R.map g)) (add_zero n) := by
  simp only [extAdjMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by simp)]

theorem extAdjMap_comp_extClass (A : C) {S : ShortComplex D} (hS : S.ShortExact) {n : ℕ}
    (x : Ext (L.obj A) S.X₃ n) :
    extAdjMap adj A S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (extAdjMap adj A S.X₃ n x).comp (hS.map_of_exact R).extClass rfl := by
  simp only [extAdjMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

attribute [local instance] Ext.subsingleton_of_injective in
theorem extAdjMap_bijective [EnoughInjectives D] [L.PreservesMonomorphisms]
    (A : C) (B : D) (n : ℕ) : Function.Bijective (extAdjMap adj A B n) := by
  have hR : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  induction n generalizing B with
  | zero => exact extAdjMap_zero_bijective adj A B
  | succ n hn =>
    let I : InjectivePresentation B := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map R).X₂ := Functor.PreservesInjectiveObjects.injective_obj I.injective
    have : Injective S.X₂ := I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (extAdjMap adj A S.X₂ n) (extAdjMap adj A S.X₃ n) (extAdjMap adj A S.X₁ (n + 1))
      (by ext x; exact (extAdjMap_comp_mk₀ adj A S.g x).symm)
      (by ext x; exact (extAdjMap_comp_extClass adj A hS x).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (L.obj A) hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A (hS.map_of_exact R) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map_of_exact R) y₁ (by subsingleton) rfl)

/-- The adjunction isomorphism `Ext (L A) B n ≃+ Ext A (R B) n`. -/
def extAdjEquiv [EnoughInjectives D] [L.PreservesMonomorphisms] (A : C) (B : D) (n : ℕ) :
    Ext (L.obj A) B n ≃+ Ext A (R.obj B) n :=
  AddEquiv.ofBijective (extAdjMap adj A B n) (extAdjMap_bijective adj A B n)

theorem extAdjEquiv_apply [EnoughInjectives D] [L.PreservesMonomorphisms] (A : C) (B : D) (n : ℕ)
    (e : Ext (L.obj A) B n) : extAdjEquiv adj A B n e = extAdjMap adj A B n e :=
  rfl

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_CdOne_Lc =====
section

/-!
# S4-PD (3), group layer part 1: locally constant cochains and the index lemma

For a compact topological group `P` acting on `A` (locally constant action, `LcAct`):
* `lc_dite`, `lc_sum`, `lc_d₁`: closure properties of locally constant cochains;
* `exists_open_inv`: a locally constant function on `P × P` is invariant under right multiplication by an open
  subgroup in each variable (finite level); `exists_openNormal_le`, `actKer`, `isOpen_actKer`;
* `index_lemma`: for an open subgroup `H` whose index is invertible on `A`, a locally constant 2-cocycle whose
  restriction to `H × H` is the coboundary of a locally constant cochain is a locally constant coboundary on `P`
  (normalise to `f(g, n) = 0` for `n ∈ H`, then average over the left cosets `P ⧸ H`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open groupCohomology Filter Topology

section LcBasic

variable {X : Type*} [TopologicalSpace X]

end LcBasic

variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  {A : Type*} [AddCommGroup A] [DistribMulAction P A]

theorem lc_smul_comp (hact : LcAct P A) {b : P → A} (hb : IsLocallyConstant b) :
    IsLocallyConstant fun p : P × P => p.1 • b p.2 := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g, h⟩
  have h1 := (IsLocallyConstant.iff_eventually_eq _).1 (hact (b h)) g
  have h2 := (IsLocallyConstant.iff_eventually_eq _).1 hb h
  rw [nhds_prod_eq]
  filter_upwards [h1.prod_mk h2] with p hp
  rw [hp.2, hp.1]

theorem lc_d₁ (hact : LcAct P A) {b : P → A} (hb : IsLocallyConstant b) : IsLocallyConstant (d₁ b) := by
  have h1 := lc_smul_comp hact hb
  have h2 : IsLocallyConstant fun p : P × P => b (p.1 * p.2) := hb.comp_continuous continuous_mul
  have h3 : IsLocallyConstant fun p : P × P => b p.1 := hb.comp_continuous continuous_fst
  exact (h1.sub h2).add h3

/-- Finite level: a locally constant function on `P × P` (`P` compact) is invariant under right multiplication
by an open subgroup in each variable. -/
theorem exists_open_inv [CompactSpace P] {X : Type*} {f : P × P → X} (hf : IsLocallyConstant f) :
    ∃ W : Subgroup P, IsOpen (W : Set P) ∧
      ∀ x ∈ W, ∀ g h : P, f (g * x, h) = f (g, h) ∧ f (g, h * x) = f (g, h) := by
  let W : Subgroup P :=
    { carrier := {x | ∀ g h : P, f (g * x, h) = f (g, h) ∧ f (g, h * x) = f (g, h)}
      one_mem' := by intro g h; simp
      mul_mem' := fun {x y} hx hy g h => by
        refine ⟨?_, ?_⟩
        · rw [← mul_assoc, (hy (g * x) h).1, (hx g h).1]
        · rw [← mul_assoc, (hy g (h * x)).2, (hx g h).2]
      inv_mem' := fun {x} hx g h => by
        refine ⟨?_, ?_⟩
        · have := (hx (g * x⁻¹) h).1
          rw [inv_mul_cancel_right] at this
          exact this.symm
        · have := (hx g (h * x⁻¹)).2
          rw [inv_mul_cancel_right] at this
          exact this.symm }
  refine ⟨W, W.isOpen_of_mem_nhds (g := 1) ?_, fun x hx => hx⟩
  have hK := (isCompact_univ : IsCompact (Set.univ : Set (P × P))).eventually_forall_of_forall_eventually
    (x₀ := (1 : P)) (P := fun x y => f (y.1 * x, y.2) = f y ∧ f (y.1, y.2 * x) = f y) ?_
  · filter_upwards [hK] with x hx
    exact fun g h => hx (g, h) (Set.mem_univ _)
  · rintro ⟨g, h⟩ -
    have hf' := (IsLocallyConstant.iff_eventually_eq f).1 hf (g, h)
    have c1 : Continuous fun z : P × (P × P) => (z.2.1 * z.1, z.2.2) := by fun_prop
    have c2 : Continuous fun z : P × (P × P) => (z.2.1, z.2.2 * z.1) := by fun_prop
    have e1 := (c1.tendsto' ((1 : P), (g, h)) (g, h) (by simp)).eventually hf'
    have e2 := (c2.tendsto' ((1 : P), (g, h)) (g, h) (by simp)).eventually hf'
    have e0 := (continuous_snd.tendsto' ((1 : P), (g, h)) (g, h) rfl).eventually hf'
    filter_upwards [e1, e2, e0] with z h1 h2 h0
    exact ⟨h1.trans h0.symm, h2.trans h0.symm⟩

/-- An open subgroup of a compact group contains an open normal subgroup. -/
theorem exists_openNormal_le [CompactSpace P] (W : Subgroup P) (hW : IsOpen (W : Set P)) :
    ∃ N : Subgroup P, N.Normal ∧ IsOpen (N : Set P) ∧ N ≤ W := by
  obtain ⟨N, hN⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
    ⟨W.isClosed_of_isOpen hW, hW⟩ W.one_mem
  exact ⟨N.toSubgroup, N.isNormal', N.isOpen', fun x hx => hN hx⟩

/-- The kernel of the action. -/
def actKer (P A : Type*) [Group P] [AddCommGroup A] [DistribMulAction P A] : Subgroup P where
  carrier := {x | ∀ a : A, x • a = a}
  one_mem' := fun a => one_smul P a
  mul_mem' := fun {x y} hx hy a => by rw [mul_smul, hy, hx]
  inv_mem' := fun {x} hx a => by rw [inv_smul_eq_iff, hx]

theorem mem_actKer {x : P} : x ∈ actKer P A ↔ ∀ a : A, x • a = a := Iff.rfl

theorem isOpen_actKer [Finite A] (hact : LcAct P A) : IsOpen (actKer P A : Set P) := by
  refine (actKer P A).isOpen_of_mem_nhds (g := 1) ?_
  have : ∀ᶠ x in 𝓝 (1 : P), ∀ a : A, x • a = a := Filter.eventually_all.2 fun a => by
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hact a) 1] with x hx
    rw [hx, one_smul]
  exact this

/-! ## Coset representatives for a (not necessarily normal) subgroup -/

/-- A representative of the left coset `g H`. -/
noncomputable def crep (H : Subgroup P) (g : P) : P := (QuotientGroup.mk g : P ⧸ H).out

theorem crep_inv_mul_mem (H : Subgroup P) (g : P) : (crep H g)⁻¹ * g ∈ H :=
  QuotientGroup.eq.mp (QuotientGroup.out_eq' _)

theorem crep_eq_of_mem (H : Subgroup P) {g g' : P} (h : g⁻¹ * g' ∈ H) : crep H g = crep H g' := by
  unfold crep; rw [QuotientGroup.eq.mpr h]

theorem crep_mul_mem (H : Subgroup P) (g : P) {n : P} (hn : n ∈ H) : crep H (g * n) = crep H g :=
  crep_eq_of_mem H (by simpa [mul_assoc] using H.inv_mem hn)

theorem crep_mem_of_mem (H : Subgroup P) {n : P} (hn : n ∈ H) : crep H n ∈ H := by
  have h := H.mul_mem (crep_inv_mul_mem H n) (H.inv_mem hn)
  rw [mul_inv_cancel_right] at h
  simpa using H.inv_mem h

theorem lc_mk {H : Subgroup P} (hH : IsOpen (H : Set P)) :
    IsLocallyConstant (QuotientGroup.mk : P → P ⧸ H) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hc : Continuous fun y : P => g⁻¹ * y := continuous_const.mul continuous_id
  have : ∀ᶠ y in 𝓝 g, g⁻¹ * y ∈ H :=
    hc.continuousAt.eventually_mem (by rw [inv_mul_cancel]; exact hH.mem_nhds H.one_mem)
  filter_upwards [this] with y hy
  exact (QuotientGroup.eq.mpr hy).symm

theorem lc_crep {H : Subgroup P} (hH : IsOpen (H : Set P)) : IsLocallyConstant (crep H) :=
  (lc_mk hH).comp (fun q : P ⧸ H => q.out)

/-! ## The index lemma -/

theorem zero_right_aux (H : Subgroup P) {f : P × P → A} (hf : IsCocycle₂ f)
    (h0 : ∀ n ∈ H, ∀ n' ∈ H, f (n, n') = 0) :
    ∀ g, ∀ n ∈ H, (f - d₁ (fun g => -f (crep H g, (crep H g)⁻¹ * g))) (g, n) = 0 := by
  intro g n hn
  have hbn : f (crep H n, (crep H n)⁻¹ * n) = 0 :=
    h0 _ (crep_mem_of_mem H hn) _ (crep_inv_mul_mem H n)
  have hgn : crep H (g * n) = crep H g := crep_mul_mem H g hn
  have hc := hf (crep H g) ((crep H g)⁻¹ * g) n
  rw [mul_inv_cancel_left, h0 _ (crep_inv_mul_mem H g) _ hn, smul_zero, zero_add,
    mul_assoc ((crep H g)⁻¹) g n] at hc
  simp only [Pi.sub_apply, d₁_apply, hgn, hbn, neg_zero, smul_zero]
  rw [← hc]; abel

theorem right_inv (H : Subgroup P) {F : P × P → A} (hF : IsCocycle₂ F) (h0 : ∀ g, ∀ n ∈ H, F (g, n) = 0)
    (g x : P) {n : P} (hn : n ∈ H) : F (g, x * n) = F (g, x) := by
  have := hF g x n
  have e1 := h0 (g * x) n hn
  have e2 := h0 x n hn
  rw [e1, e2, smul_zero, zero_add, zero_add] at this
  exact this.symm

/-- **Index lemma.** `H` open of index invertible on `A`; if `f|H×H = d₁ β` with `β` locally constant, then `f` is
a locally constant coboundary on `P`. -/
theorem index_lemma [CompactSpace P] (hact : LcAct P A) (H : Subgroup P) (hH : IsOpen (H : Set P))
    (x : ℤ) (hx : ∀ a : A, (x * (H.index : ℤ)) • a = a)
    {f : P × P → A} (hf : IsLocallyConstant f) (hc : IsCocycle₂ f)
    (β : P → A) (hβ : IsLocallyConstant β) (hβH : ∀ h ∈ H, ∀ h' ∈ H, f (h, h') = d₁ β (h, h')) :
    IsLcCob f := by
  classical
  have : Finite (P ⧸ H) := H.quotient_finite_of_isOpen hH
  let _ : Fintype (P ⧸ H) := Fintype.ofFinite _
  obtain ⟨f₁, hf₁⟩ : ∃ f₁, f₁ = f - d₁ β := ⟨_, rfl⟩
  have hc₁ : IsCocycle₂ f₁ := by rw [hf₁]; exact isCocycle₂_sub_d₁ hc β
  have hl₁ : IsLocallyConstant f₁ := by rw [hf₁]; exact hf.sub (lc_d₁ hact hβ)
  have h0₁ : ∀ n ∈ H, ∀ n' ∈ H, f₁ (n, n') = 0 := fun n hn n' hn' => by
    rw [hf₁, Pi.sub_apply, hβH n hn n' hn', sub_self]
  obtain ⟨b₁, hb₁⟩ : ∃ b₁ : P → A, b₁ = fun g => -f₁ (crep H g, (crep H g)⁻¹ * g) := ⟨_, rfl⟩
  have hlb₁ : IsLocallyConstant b₁ := by
    rw [hb₁]
    have hcont : Continuous fun g : P => (crep H g, (crep H g)⁻¹ * g) :=
      (lc_crep hH).continuous.prodMk ((lc_crep hH).continuous.inv.mul continuous_id)
    exact (hl₁.comp_continuous hcont).comp (fun a => -a)
  obtain ⟨f₂, hf₂⟩ : ∃ f₂, f₂ = f₁ - d₁ b₁ := ⟨_, rfl⟩
  have hc₂ : IsCocycle₂ f₂ := by rw [hf₂]; exact isCocycle₂_sub_d₁ hc₁ b₁
  have h0₂ : ∀ g, ∀ n ∈ H, f₂ (g, n) = 0 := by rw [hf₂, hb₁]; exact zero_right_aux H hc₁ h0₁
  have hl₂ : IsLocallyConstant f₂ := by rw [hf₂]; exact hl₁.sub (lc_d₁ hact hlb₁)
  obtain ⟨F, hF⟩ : ∃ F : P → A, F = fun g => ∑ y : P ⧸ H, f₂ (g, y.out) := ⟨_, rfl⟩
  have hFg : ∀ g, ∑ y : P ⧸ H, f₂ (g, y.out) = F g := fun g => by rw [hF]
  have hlF : IsLocallyConstant F := by
    rw [hF]
    exact lc_sum (fun (y : P ⧸ H) (g : P) => f₂ (g, y.out))
      (fun y => hl₂.comp_continuous (continuous_id.prodMk continuous_const))
  have hperm : ∀ g h : P, ∑ y : P ⧸ H, f₂ (g, h * y.out) = F g := by
    intro g h
    rw [← hFg]
    have hstep : ∀ y : P ⧸ H, f₂ (g, h * y.out) = f₂ (g, (h • y).out) := by
      intro y
      have e : (QuotientGroup.mk (h * y.out) : P ⧸ H) = QuotientGroup.mk ((h • y).out) := by
        rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
      have hm := QuotientGroup.eq.mp e
      have := right_inv H hc₂ h0₂ g (h * y.out) hm
      rw [mul_inv_cancel_left] at this
      exact this.symm
    rw [Finset.sum_congr rfl (fun y _ => hstep y)]
    exact Fintype.sum_equiv (MulAction.toPerm h) _ _ (fun y => rfl)
  have key : ∀ g h : P, (H.index : ℤ) • f₂ (g, h) = g • F h - F (g * h) + F g := by
    intro g h
    have hs := Finset.sum_congr (rfl : (Finset.univ : Finset (P ⧸ H)) = Finset.univ)
      (fun y _ => hc₂ g h y.out)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_const,
      Finset.card_univ, hperm, hFg, hFg] at hs
    rw [H.index_eq_card, Nat.card_eq_fintype_card, natCast_zsmul]
    exact eq_of_sub_eq hs (by abel)
  refine ⟨β + b₁ + x • F, ?_, fun g h => ?_⟩
  · have h3 : IsLocallyConstant (x • F) := hlF.comp (fun a : A => x • a)
    exact (hβ.add hlb₁).add h3
  · have e1 : f (g, h) = f₁ (g, h) + d₁ β (g, h) := by rw [hf₁, Pi.sub_apply, sub_add_cancel]
    have e2 : f₁ (g, h) = f₂ (g, h) + d₁ b₁ (g, h) := by rw [hf₂, Pi.sub_apply, sub_add_cancel]
    have e3 : f₂ (g, h) = x • (g • F h - F (g * h) + F g) := by
      rw [← key, ← mul_smul, hx]
    rw [e1, e2, e3, d₁_add, d₁_add]
    simp only [Pi.add_apply, d₁_apply, Pi.smul_apply, smul_add, smul_sub, smul_zsmul']
    abel

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_CdOne_Grp =====
section

/-!
# S4-PD (3), group layer part 2: Sylow reduction and `ℤ/l` coefficients

* `exists_inv_index`: an index prime to `l` is invertible on an `l`-primary module;
* `exists_sylow_open`: the preimage `H` of an `l`-Sylow of the finite quotient `P ⧸ N`;
* `HypL l P`: the hypothesis (Hl) supplied by the field layer (central embedding problems): `ℤ/l`-valued 2-cocycles
  with trivial action on an open subgroup `Q`, factoring through an `l`-group quotient `Q/N`, are locally constant
  coboundaries on `Q`;
* `trivial_coeff`: under `HypL`, every locally constant `ℤ/l`-valued 2-cocycle (trivial action) on `P` is a locally
  constant coboundary (finite level, Sylow, `index_lemma`);
* `hypL_subgroup`: `HypL` passes to open subgroups.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open groupCohomology Filter Topology

theorem exists_inv_index {A : Type*} [AddCommGroup A] {l e m : ℕ} (hl : l.Prime) (hm : ¬ l ∣ m)
    (hA : ∀ a : A, (l ^ e) • a = 0) : ∃ x : ℤ, ∀ a : A, (x * m) • a = a := by
  have hcop : Nat.Coprime m (l ^ e) :=
    Nat.Coprime.pow_right e (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hl).mpr hm))
  obtain ⟨u, v, huv⟩ := Nat.Coprime.isCoprime hcop
  refine ⟨u, fun a => ?_⟩
  have h1 : (u * m : ℤ) = 1 - v * ((l ^ e : ℕ) : ℤ) := by rw [← huv]; ring
  rw [h1, sub_smul, one_smul, mul_smul, natCast_zsmul, hA, smul_zero, sub_zero]

/-- The trivial action (used only as a local instance). -/
def trivAct (P B : Type*) [Monoid P] [AddMonoid B] : DistribMulAction P B where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]

/-- The preimage of an `l`-Sylow subgroup of the finite quotient `P ⧸ N`. -/
theorem exists_sylow_open [CompactSpace P] (l : ℕ) [Fact l.Prime] (N : Subgroup P) [N.Normal]
    (hN : IsOpen (N : Set P)) :
    ∃ H : Subgroup P, N ≤ H ∧ IsOpen (H : Set P) ∧ ¬ l ∣ H.index ∧ ∀ q ∈ H, ∃ k : ℕ, q ^ (l ^ k) ∈ N := by
  have : Finite (P ⧸ N) := N.quotient_finite_of_isOpen hN
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow l (P ⧸ N)))
  have hNH : N ≤ (S : Subgroup (P ⧸ N)).comap (QuotientGroup.mk' N) := by
    intro n hn
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  refine ⟨_, hNH, Subgroup.isOpen_mono hNH hN, ?_, ?_⟩
  · rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)]
    exact S.not_dvd_index
  · intro q hq
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨_, hq⟩
    refine ⟨k, (QuotientGroup.eq_one_iff _).mp ?_⟩
    have := congrArg Subtype.val hk
    simpa using this

/-- **(Hl)**: `ℤ/l`-valued 2-cocycles (trivial action) on an open subgroup `Q` that factor through an `l`-group
quotient `Q/N` are locally constant coboundaries on `Q`. Supplied by the field layer (Kummer theory over a C1 field). -/
def HypL (l : ℕ) (P : Type*) [Group P] [TopologicalSpace P] : Prop :=
  ∀ Q N : Subgroup P, IsOpen (Q : Set P) → IsOpen (N : Set P) → N ≤ Q →
    (∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N) → (∀ q ∈ Q, ∃ k : ℕ, q ^ (l ^ k) ∈ N) →
    ∀ f : P × P → ZMod l, IsLocallyConstant f →
    (∀ g ∈ Q, ∀ h ∈ Q, ∀ j ∈ Q, f (g * h, j) + f (g, h) = f (h, j) + f (g, h * j)) →
    (∀ g ∈ Q, ∀ h ∈ Q, ∀ n ∈ N, ∀ n' ∈ N, f (g * n, h * n') = f (g, h)) →
    ∃ γ : P → ZMod l, IsLocallyConstant γ ∧ ∀ g ∈ Q, ∀ h ∈ Q, f (g, h) = γ h - γ (g * h) + γ g

/-- Under `HypL`, every locally constant `ℤ/l`-valued 2-cocycle with trivial action is a locally constant
coboundary. -/
theorem trivial_coeff [CompactSpace P] (l : ℕ) [hl : Fact l.Prime] (hL : HypL l P) {f : P × P → ZMod l}
    (hf : IsLocallyConstant f) (hc : ∀ g h j : P, f (g * h, j) + f (g, h) = f (h, j) + f (g, h * j)) :
    ∃ γ : P → ZMod l, IsLocallyConstant γ ∧ ∀ g h : P, f (g, h) = γ h - γ (g * h) + γ g := by
  obtain ⟨W, hWo, hW⟩ := exists_open_inv hf
  obtain ⟨N, hNn, hNo, hNW⟩ := exists_openNormal_le W hWo
  have := hNn
  obtain ⟨H, hNH, hHo, hl', hH⟩ := exists_sylow_open l N hNo
  obtain ⟨γ, hγ, hγH⟩ := hL H N hHo hNo hNH (fun q _ n hn => hNn.conj_mem n hn q) hH f hf
    (fun g _ h _ j _ => hc g h j)
    (fun g _ h _ n hn n' hn' => by rw [(hW n (hNW hn) g (h * n')).1, (hW n' (hNW hn') g h).2])
  letI : DistribMulAction P (ZMod l) := trivAct P (ZMod l)
  obtain ⟨x, hx⟩ := exists_inv_index (A := ZMod l) (e := 1) hl.out hl' (fun a => by simp)
  obtain ⟨b, hb, hfb⟩ := index_lemma (fun a => IsLocallyConstant.const a) H hHo x hx hf
    (fun g h j => hc g h j) γ hγ (fun h hh h' hh' => hγH h hh h' hh')
  exact ⟨b, hb, fun g h => hfb g h⟩

/-- `HypL` passes to open subgroups. -/
theorem hypL_subgroup (l : ℕ) (hL : HypL l P) (H : Subgroup P) (hH : IsOpen (H : Set P)) : HypL l H := by
  classical
  intro Q₁ N₁ hQ₁ hN₁ hNQ₁ hnorm hlg f₁ hf₁ hc₁ hinv₁
  have hemb := hH.isOpenEmbedding_subtypeVal
  have hopen : ∀ K : Subgroup H, IsOpen (K : Set H) → IsOpen ((K.map H.subtype : Subgroup P) : Set P) := by
    intro K hK
    rw [Subgroup.coe_map]
    exact hemb.isOpenMap _ hK
  let f : P × P → ZMod l := fun p =>
    if hp : p ∈ (H : Set P) ×ˢ (H : Set P) then f₁ (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩) else 0
  have hfv : ∀ a b : H, f ((a : P), (b : P)) = f₁ (a, b) := fun a b => by
    simp only [f, dif_pos (Set.mk_mem_prod a.2 b.2)]
  have hlf : IsLocallyConstant f := by
    have hc : IsClopen (H : Set P) := ⟨H.isClosed_of_isOpen hH, hH⟩
    refine lc_dite (hc.prod hc) (fun p => f₁ (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)) ?_
    exact hf₁.comp_continuous
      (((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  have hnorm' : ∀ q ∈ Q₁.map H.subtype, ∀ n ∈ N₁.map H.subtype, q * n * q⁻¹ ∈ N₁.map H.subtype := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨n, hn, rfl⟩
    exact ⟨q * n * q⁻¹, hnorm q hq n hn, by simp⟩
  have hlg' : ∀ q ∈ Q₁.map H.subtype, ∃ k : ℕ, q ^ (l ^ k) ∈ N₁.map H.subtype := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨k, hk⟩ := hlg q hq
    exact ⟨k, ⟨_, hk, by simp⟩⟩
  have hcoc : ∀ g ∈ Q₁.map H.subtype, ∀ h ∈ Q₁.map H.subtype, ∀ j ∈ Q₁.map H.subtype,
      f (g * h, j) + f (g, h) = f (h, j) + f (g, h * j) := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ _ ⟨j, hj, rfl⟩
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hfv, hfv, hfv, hfv]
    exact hc₁ g hg h hh j hj
  have hinv : ∀ g ∈ Q₁.map H.subtype, ∀ h ∈ Q₁.map H.subtype, ∀ n ∈ N₁.map H.subtype,
      ∀ n' ∈ N₁.map H.subtype, f (g * n, h * n') = f (g, h) := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ _ ⟨n, hn, rfl⟩ _ ⟨n', hn', rfl⟩
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hfv, hfv]
    exact hinv₁ g hg h hh n hn n' hn'
  obtain ⟨γ, hγ, hγQ⟩ := hL (Q₁.map H.subtype) (N₁.map H.subtype) (hopen Q₁ hQ₁) (hopen N₁ hN₁)
    (Subgroup.map_mono hNQ₁) hnorm' hlg' f hlf hcoc hinv
  refine ⟨γ ∘ Subtype.val, hγ.comp_continuous continuous_subtype_val, fun g hg h hh => ?_⟩
  have := hγQ g ⟨g, hg, rfl⟩ h ⟨h, hh, rfl⟩
  rw [hfv] at this
  exact this

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_CdOne_Dev =====
section

/-!
# S4-PD (3), group layer part 3: dévissage and `H²(P, A) = 0`

* `exists_fixed_order_l`: an `l`-group action on a finite module of order divisible by `l` fixes an element of
  order `l` (fixed points of the image in `Perm A`, an `l`-group);
* `quotAct`: the action on `A ⧸ M` for a stable subgroup `M`;
* `lgroup_case`: under `HypL`, if `P` acts on `A` (`|A| = lᵉ`) through an `l`-group, every locally constant
  2-cocycle is a locally constant coboundary (induction on `e`, `trivial_coeff` on `⟨m⟩ ≅ ℤ/l`);
* `cd_le_one`: the same for any finite module of order `lᵉ` with locally constant action (Sylow + `index_lemma`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace RamanujanPetersson.CdOne

open groupCohomology

variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]

section Fixed

variable {A : Type*} [AddCommGroup A] [DistribMulAction P A]

/-- The `P`-fixed vectors. -/
def fixAdd (P A : Type*) [Group P] [AddCommGroup A] [DistribMulAction P A] : AddSubgroup A where
  carrier := {a | ∀ g : P, g • a = a}
  zero_mem' := fun g => smul_zero g
  add_mem' := fun {a b} ha hb g => by rw [smul_add, ha g, hb g]
  neg_mem' := fun {a} ha g => by rw [smul_neg, ha g]

theorem exists_fixed_order_l [Finite A] (l : ℕ) [hl : Fact l.Prime] (hdvd : l ∣ Nat.card A)
    (hp : ∀ g : P, ∃ k : ℕ, ∀ a : A, g ^ (l ^ k) • a = a) :
    ∃ m : A, addOrderOf m = l ∧ ∀ g : P, g • m = m := by
  classical
  let G := (MulAction.toPermHom P A).range
  have hG : IsPGroup l G := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨k, hk⟩ := hp g
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow]
    ext a
    simp [hk]
  have hmod := hG.card_modEq_card_fixedPoints A
  have hset : MulAction.fixedPoints G A = (fixAdd P A : Set A) := by
    ext a
    constructor
    · intro h g
      exact h ⟨MulAction.toPermHom P A g, g, rfl⟩
    · rintro h ⟨_, g, rfl⟩
      exact h g
  have hcard : l ∣ Nat.card (fixAdd P A) := by
    have h1 : Nat.card (MulAction.fixedPoints G A) = Nat.card (fixAdd P A) := by
      rw [hset]; rfl
    rw [← h1]
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  let _ : Fintype (fixAdd P A) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨m, hm⟩ := exists_prime_addOrderOf_dvd_card l hcard
  exact ⟨m, by rw [AddSubgroup.addOrderOf_coe, hm], m.2⟩

end Fixed

section Quot

variable {A : Type*} [AddCommGroup A] [DistribMulAction P A] (M : AddSubgroup A)
  (hM : ∀ g : P, ∀ a ∈ M, g • a ∈ M)

/-- `g` acting on `A ⧸ M`. -/
def qsmul (g : P) : A ⧸ M →+ A ⧸ M :=
  QuotientAddGroup.map M M (DistribSMul.toAddMonoidHom A g) (fun a ha => hM g a ha)

theorem qsmul_mk (g : P) (a : A) : qsmul M hM g (a : A ⧸ M) = ((g • a : A) : A ⧸ M) := rfl

/-- The action on `A ⧸ M` (local instance). -/
def quotAct : DistribMulAction P (A ⧸ M) where
  smul g q := qsmul M hM g q
  one_smul q := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact (qsmul_mk M hM 1 a).trans (congrArg (fun x : A => (x : A ⧸ M)) (one_smul P a))
  mul_smul g h q := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact (qsmul_mk M hM _ a).trans (congrArg (fun x : A => (x : A ⧸ M)) (mul_smul g h a))
  smul_zero g := map_zero (qsmul M hM g)
  smul_add g := map_add (qsmul M hM g)

end Quot

/-- Under `HypL`: actions through an `l`-group on modules of order `lᵉ` have no locally constant `H²`. -/
theorem lgroup_case [CompactSpace P] (l : ℕ) [hl : Fact l.Prime] (hL : HypL l P) (e : ℕ) :
    ∀ (A : Type u) [AddCommGroup A] [DistribMulAction P A] [Finite A], Nat.card A = l ^ e → LcAct P A →
    (∀ g : P, ∃ k : ℕ, ∀ a : A, g ^ (l ^ k) • a = a) →
    ∀ f : P × P → A, IsLocallyConstant f → IsCocycle₂ f → IsLcCob f := by
  induction e with
  | zero =>
    intro A _ _ _ hcard _ _ f _ _
    have : Subsingleton A := Finite.card_le_one_iff_subsingleton.mp (by rw [hcard, pow_zero])
    exact ⟨0, IsLocallyConstant.const 0, fun g h => Subsingleton.elim _ _⟩
  | succ e ih =>
    intro A _ _ _ hcard hact hp f hf hc
    obtain ⟨m, hm, hmfix⟩ :=
      exists_fixed_order_l l (by rw [hcard]; exact dvd_pow_self l (Nat.succ_ne_zero e)) hp
    have hMfix : ∀ a ∈ AddSubgroup.zmultiples m, ∀ g : P, g • a = a := by
      intro a ha g
      obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
      rw [smul_zsmul', hmfix g]
    have hM : ∀ g : P, ∀ a ∈ AddSubgroup.zmultiples m, g • a ∈ AddSubgroup.zmultiples m :=
      fun g a ha => by rw [hMfix a ha g]; exact ha
    letI : DistribMulAction P (A ⧸ AddSubgroup.zmultiples m) := quotAct _ hM
    have hcard' : Nat.card (A ⧸ AddSubgroup.zmultiples m) = l ^ e := by
      have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (AddSubgroup.zmultiples m)
      rw [Nat.card_zmultiples, hm, hcard, pow_succ] at h1
      exact (Nat.eq_of_mul_eq_mul_right hl.out.pos h1).symm
    have hactq : LcAct P (A ⧸ AddSubgroup.zmultiples m) := by
      intro q
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      exact (hact a).comp (fun x : A => (x : A ⧸ AddSubgroup.zmultiples m))
    have hpq : ∀ g : P, ∃ k : ℕ, ∀ q : A ⧸ AddSubgroup.zmultiples m, g ^ (l ^ k) • q = q := by
      intro g
      obtain ⟨k, hk⟩ := hp g
      refine ⟨k, fun q => ?_⟩
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      exact congrArg (fun x : A => (x : A ⧸ AddSubgroup.zmultiples m)) (hk a)
    have hcq : IsCocycle₂ (fun p => (f p : A ⧸ AddSubgroup.zmultiples m)) := by
      intro g h j
      have := congrArg (fun x : A => (x : A ⧸ AddSubgroup.zmultiples m)) (hc g h j)
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_add] at this
      exact this
    obtain ⟨b'', hb'', hfb''⟩ := ih (A ⧸ AddSubgroup.zmultiples m) hcard' hactq hpq _
      (hf.comp (fun x : A => (x : A ⧸ AddSubgroup.zmultiples m))) hcq
    obtain ⟨b, hb⟩ : ∃ b : P → A, b = fun g => (b'' g).out := ⟨_, rfl⟩
    have hlb : IsLocallyConstant b := by rw [hb]; exact hb''.comp _
    have e1 : ∀ x : P, ((b x : A) : A ⧸ AddSubgroup.zmultiples m) = b'' x := fun x => by
      rw [hb]; exact QuotientAddGroup.out_eq' _
    have hFM : ∀ g h : P, (f - d₁ b) (g, h) ∈ AddSubgroup.zmultiples m := by
      intro g h
      rw [← QuotientAddGroup.eq_zero_iff]
      have hq : ((f (g, h) : A) : A ⧸ AddSubgroup.zmultiples m) = d₁ b'' (g, h) := hfb'' g h
      have e2 : ((g • b h : A) : A ⧸ AddSubgroup.zmultiples m) = g • b'' h :=
        (qsmul_mk _ hM g (b h)).symm.trans (congrArg (qsmul _ hM g) (e1 h))
      rw [Pi.sub_apply, QuotientAddGroup.mk_sub, hq, d₁_apply, d₁_apply, QuotientAddGroup.mk_add,
        QuotientAddGroup.mk_sub, e2, e1, e1, sub_self]
    have hml : (l : ℤ) • m = 0 := by rw [natCast_zsmul, ← hm]; exact addOrderOf_nsmul_eq_zero m
    let E : ZMod l →+ A := ZMod.lift l ⟨zmultiplesHom A m, by simpa using hml⟩
    have hE : ∀ z : ℤ, E (z : ZMod l) = z • m := fun z => by
      simp only [E, ZMod.lift_coe, zmultiplesHom_apply]
    have hEinj : Function.Injective E := by
      rw [injective_iff_map_eq_zero]
      intro k hk
      obtain ⟨z, rfl⟩ := ZMod.intCast_surjective k
      rw [hE, ← addOrderOf_dvd_iff_zsmul_eq_zero, hm] at hk
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd z l).mpr hk
    have hEmem : ∀ k : ZMod l, E k ∈ AddSubgroup.zmultiples m := fun k => by
      obtain ⟨z, rfl⟩ := ZMod.intCast_surjective k
      rw [hE]
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨z, rfl⟩
    have hErange : ∀ a ∈ AddSubgroup.zmultiples m, ∃ k, E k = a := by
      intro a ha
      obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
      exact ⟨z, hE z⟩
    obtain ⟨c, hcdef⟩ : ∃ c : P × P → ZMod l, c = fun p => Function.invFun E ((f - d₁ b) p) :=
      ⟨_, rfl⟩
    have hEc : ∀ p, E (c p) = (f - d₁ b) p := fun p => by
      rw [hcdef]
      obtain ⟨k, hk⟩ := hErange _ (hFM p.1 p.2)
      exact Function.invFun_eq ⟨k, hk⟩
    have hlF : IsLocallyConstant (f - d₁ b) := hf.sub (lc_d₁ hact hlb)
    have hlc : IsLocallyConstant c := by rw [hcdef]; exact hlF.comp (Function.invFun E)
    have hcF : IsCocycle₂ (f - d₁ b) := isCocycle₂_sub_d₁ hc b
    have hcc : ∀ g h j : P, c (g * h, j) + c (g, h) = c (h, j) + c (g, h * j) := by
      intro g h j
      apply hEinj
      rw [map_add, map_add, hEc, hEc, hEc, hEc, hcF g h j, hMfix _ (hFM h j) g]
    obtain ⟨γ, hγ, hcγ⟩ := trivial_coeff l hL hlc hcc
    refine ⟨b + E ∘ γ, hlb.add (hγ.comp E), fun g h => ?_⟩
    have h1 : f (g, h) = (f - d₁ b) (g, h) + d₁ b (g, h) := by rw [Pi.sub_apply, sub_add_cancel]
    rw [h1, ← hEc, hcγ g h, d₁_add]
    simp only [Pi.add_apply, d₁_apply, Function.comp_apply, map_add, map_sub]
    rw [hMfix _ (hEmem (γ h)) g]
    abel

/-- **`cd_l ≤ 1`, group form.** Under `HypL`, for a compact group `P` and a finite module `A` of order `lᵉ` with
locally constant action, every locally constant 2-cocycle is a locally constant coboundary. -/
theorem cd_le_one [CompactSpace P] (l : ℕ) [hl : Fact l.Prime] (hL : HypL l P) (e : ℕ) (A : Type u)
    [AddCommGroup A] [DistribMulAction P A] [Finite A] (hcard : Nat.card A = l ^ e) (hact : LcAct P A)
    {f : P × P → A} (hf : IsLocallyConstant f) (hc : IsCocycle₂ f) : IsLcCob f := by
  classical
  obtain ⟨N, hNn, hNo, hNK⟩ := exists_openNormal_le (actKer P A) (isOpen_actKer hact)
  have := hNn
  obtain ⟨H, hNH, hHo, hl', hH⟩ := exists_sylow_open l N hNo
  have : CompactSpace H := isCompact_iff_compactSpace.mp (H.isClosed_of_isOpen hHo).isCompact
  have hLH : HypL l H := hypL_subgroup l hL H hHo
  have hactH : LcAct H A := fun a => (hact a).comp_continuous continuous_subtype_val
  have hpH : ∀ g : H, ∃ k : ℕ, ∀ a : A, g ^ (l ^ k) • a = a := by
    intro g
    obtain ⟨k, hk⟩ := hH g g.2
    exact ⟨k, fun a => (mem_actKer.mp (hNK hk)) a⟩
  obtain ⟨β₀, hβ₀, hfβ₀⟩ := lgroup_case l hLH e A hcard hactH hpH (fun p : H × H => f (p.1, p.2))
    (hf.comp_continuous (continuous_subtype_val.prodMap continuous_subtype_val)) (fun g h j => hc g h j)
  obtain ⟨x, hx⟩ := exists_inv_index (A := A) (e := e) hl.out hl'
    (fun a => by rw [← hcard]; exact card_nsmul_eq_zero')
  refine index_lemma hact H hHo x hx hf hc (fun g => if h : g ∈ H then β₀ ⟨g, h⟩ else 0)
    (lc_dite (S := (H : Set P)) ⟨H.isClosed_of_isOpen hHo, hHo⟩ β₀ hβ₀) (fun h hh h' hh' => ?_)
  simp only [d₁_apply, dif_pos hh, dif_pos hh', dif_pos (H.mul_mem hh hh')]
  exact hfβ₀ ⟨h, hh⟩ ⟨h', hh'⟩

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_CdOne_Wrap =====
section

/-!
# S4-PD (3), group layer part 4: wrappers for `cd_l ≤ 1`

* `card_eq_pow_of_nsmul`: a finite abelian group killed by `lⁿ` has order a power of `l` (Cauchy);
* `cd_le_one_of_nsmul`: `cd_le_one` for modules killed by `lⁿ`;
* `repAct`, `h2_eq_zero`: the statement for a closed (compact) subgroup `Γ` of a topological group `G` acting on
  `M` through a representation `ρ` with open kernel (the `S4-CurveCoh` convention: cochains on `Γ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace RamanujanPetersson.CdOne

open groupCohomology Topology

/-- A finite abelian group killed by `lⁿ` has order a power of `l`. -/
theorem card_eq_pow_of_nsmul (A : Type*) [AddCommGroup A] [Finite A] (l : ℕ) [hl : Fact l.Prime] (n : ℕ)
    (hA : ∀ a : A, (l ^ n) • a = 0) : ∃ e : ℕ, Nat.card A = l ^ e := by
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun {d} hd hdvd => ?_)⟩
  have := Fact.mk hd
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card' d hdvd
  have h1 : addOrderOf a ∣ l ^ n := addOrderOf_dvd_of_nsmul_eq_zero (hA a)
  rw [ha] at h1
  exact (Nat.prime_dvd_prime_iff_eq hd hl.out).mp (hd.dvd_of_dvd_pow h1)

/-- **`cd_l ≤ 1`** for finite modules killed by `lⁿ` with locally constant action. -/
theorem cd_le_one_of_nsmul {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    (l : ℕ) [Fact l.Prime] (hL : HypL l P) (n : ℕ) (A : Type u) [AddCommGroup A] [DistribMulAction P A]
    [Finite A] (hA : ∀ a : A, (l ^ n) • a = 0) (hact : LcAct P A) {f : P × P → A} (hf : IsLocallyConstant f)
    (hc : IsCocycle₂ f) : IsLcCob f := by
  obtain ⟨e, he⟩ := card_eq_pow_of_nsmul A l n hA
  exact cd_le_one l hL e A he hact hf hc

section Rep

variable {k : Type*} [CommRing k] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type u} [AddCommGroup M] [Module k M]

end Rep

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_CdOne_Emb =====
section

/-!
# S4-PD (3b): the central embedding problem with kernel `μ_l`

Let `E` be a C1 field containing a primitive `l`-th root of unity `ζ`, and `L/E` a finite Galois `l`-extension.
For a 2-cocycle `f : Gal(L/E)² → ZMod l` (trivial action), `Br(L/E) = 0` (`br_eq_zero`) gives `β : Gal(L/E) → Lˣ`
with `dβ = ζ^f`, and Hilbert 90 gives `b ∈ Lˣ` with `σ b / b = β(σ)^l` (`exists_kummer_data`). For any extension
`Ω ⊇ L` of `E` containing an `l`-th root `y` of `a·b` (`a ∈ Eˣ` free, used later to remove ramification), the
inflation of `f` to `Gal(Ω/E)` is the coboundary of `γ(σ) = log_ζ (β(σ|L) y / σ y)` (`emb_coboundary`), and `γ(σ)`
only depends on `σ|L` and `σ y`. `emb_solve` packages both steps.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open groupCohomology IntermediateField RamanujanPetersson.Tsen

theorem pow_val_add {M : Type*} [Monoid M] {z : M} {l : ℕ} [NeZero l] (hz : z ^ l = 1) (a b : ZMod l) :
    z ^ (a + b).val = z ^ a.val * z ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) l, pow_add, pow_mul, hz, one_pow, mul_one]

theorem cg_key {G : Type*} [CommGroup G] (P Q R S U Y W : G) (hW : W = P * S / U) :
    U * (R * Y / S) = P / Q * R * (Q * Y / W) := by
  subst hW
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

theorem cg_pow {G : Type*} [CommGroup G] (X A B S : G) (hS : S = A * (X * B)) :
    X * (A * B) / S = 1 := by
  subst hS
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_one]
  abel

section Kummer

variable {E : Type*} [Field E]

/-- The image of a nonzero `ζ : E` in `Lˣ`. -/
noncomputable def unitOf (L : Type*) [Field L] [Algebra E L] (ζ : E) (h : ζ ≠ 0) : Lˣ :=
  Units.mk0 (algebraMap E L ζ) ((map_ne_zero _).mpr h)

variable {L : Type*} [Field L] [Algebra E L]

theorem unitOf_val (ζ : E) (h : ζ ≠ 0) : ((unitOf L ζ h : Lˣ) : L) = algebraMap E L ζ := rfl

theorem smul_unitOf (σ : Gal(L/E)) (ζ : E) (h : ζ ≠ 0) : σ • unitOf L ζ h = unitOf L ζ h :=
  Units.ext (σ.commutes ζ)

/-- Step (i): `Br(L/E) = 0` and Hilbert 90 produce the Kummer data `(β, b)`. -/
theorem exists_kummer_data [FiniteDimensional E L] [IsGalois E L] (hE : IsC1 E) (l : ℕ) [Fact l.Prime]
    (hG : IsPGroup l Gal(L/E)) {ζ : E} (hζ : IsPrimitiveRoot ζ l) (hζ0 : ζ ≠ 0)
    (f : Gal(L/E) × Gal(L/E) → ZMod l) (hf : ∀ g h j, f (g * h, j) + f (g, h) = f (h, j) + f (g, h * j)) :
    ∃ (β : Gal(L/E) → Lˣ) (b : Lˣ),
      (∀ σ τ, σ • β τ / β (σ * τ) * β σ = unitOf L ζ hζ0 ^ (f (σ, τ)).val) ∧
        ∀ σ, σ • b / b = β σ ^ l := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hz : unitOf L ζ hζ0 ^ l = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, unitOf_val, ← map_pow, hζ.pow_eq_one, map_one, Units.val_one])
  have hc : IsMulCocycle₂ (fun q : Gal(L/E) × Gal(L/E) => unitOf L ζ hζ0 ^ (f q).val) := by
    intro g h j
    simp only
    rw [smul_pow', smul_unitOf, ← pow_val_add hz, ← pow_val_add hz, hf]
  obtain ⟨β, hβ⟩ := br_eq_zero hE l L hG _ hc
  have hφ : IsMulCocycle₁ (fun σ : Gal(L/E) => β σ ^ l) := by
    intro g h
    have h1 : (g • β h / β (g * h) * β g) ^ l = 1 := by
      rw [hβ g h, ← pow_mul, mul_comm, pow_mul, hz, one_pow]
    rw [mul_pow, div_pow, ← smul_pow', div_mul_eq_mul_div, div_eq_one] at h1
    exact h1.symm
  obtain ⟨b, hb⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hφ
  exact ⟨β, b, hβ, hb⟩

end Kummer

section Emb

variable {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω]

set_option synthInstance.maxHeartbeats 400000 in
/-- Step (ii): an `l`-th root `y` of `a·b` in `Ω` kills the inflation of `f`. -/
theorem emb_coboundary (L : IntermediateField E Ω) [Normal E L] {l : ℕ} [Fact l.Prime] {ζ : E}
    (hζ : IsPrimitiveRoot ζ l) (hζ0 : ζ ≠ 0) (f : Gal(L/E) × Gal(L/E) → ZMod l)
    (β : Gal(L/E) → Lˣ) (b : Lˣ)
    (hβ : ∀ σ τ, σ • β τ / β (σ * τ) * β σ = unitOf L ζ hζ0 ^ (f (σ, τ)).val)
    (hb : ∀ σ, σ • b / b = β σ ^ l) (a : E) (ha : a ≠ 0) (y : Ω)
    (hy : y ^ l = algebraMap E Ω a * ((b : L) : Ω)) :
    ∃ γ : Gal(Ω/E) → ZMod l,
      (∀ σ τ, f (AlgEquiv.restrictNormalHom (K₁ := Ω) L σ, AlgEquiv.restrictNormalHom (K₁ := Ω) L τ) =
        γ τ - γ (σ * τ) + γ σ) ∧
      ∀ σ τ, AlgEquiv.restrictNormalHom (K₁ := Ω) L σ = AlgEquiv.restrictNormalHom (K₁ := Ω) L τ →
        σ y = τ y → γ σ = γ τ := by
  classical
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  set ρ : Gal(Ω/E) →* Gal(L/E) := AlgEquiv.restrictNormalHom (K₁ := Ω) L
  set φ : Lˣ →* Ωˣ := Units.map (algebraMap L Ω : L →+* Ω).toMonoidHom
  have hφ : ∀ w : Lˣ, ((φ w : Ωˣ) : Ω) = ((w : L) : Ω) := fun w => rfl
  have hφσ : ∀ (σ : Gal(Ω/E)) (w : Lˣ), φ (ρ σ • w) = σ • φ w := fun σ w =>
    Units.ext (AlgEquiv.restrictNormal_commutes σ L (w : L))
  obtain ⟨zU, hzUdef⟩ : ∃ zU : Ωˣ, zU = φ (unitOf L ζ hζ0) := ⟨_, rfl⟩
  have hzU : ((zU : Ωˣ) : Ω) = algebraMap E Ω ζ := by
    rw [hzUdef, hφ, unitOf_val]; rfl
  have hprim : IsPrimitiveRoot zU l := by
    rw [← IsPrimitiveRoot.coe_units_iff, hzU]
    exact hζ.map_of_injective (algebraMap E Ω).injective
  have hzfix : ∀ σ : Gal(Ω/E), σ • zU = zU := fun σ =>
    Units.ext (show σ ((zU : Ωˣ) : Ω) = (zU : Ω) by rw [hzU]; exact σ.commutes ζ)
  -- discrete logarithm on `μ_l ⊆ Ωˣ`
  let lg : Ωˣ → ZMod l := fun x =>
    if h : ∃ i < l, ((zU : Ωˣ) : Ω) ^ i = (x : Ω) then ((Classical.choose h : ℕ) : ZMod l) else 0
  have hlg : ∀ x : Ωˣ, x ^ l = 1 → zU ^ (lg x).val = x := by
    intro x hx
    have hx' : (x : Ω) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
    have h := ((IsPrimitiveRoot.coe_units_iff).mpr hprim).eq_pow_of_pow_eq_one hx'
    have hlx : lg x = ((Classical.choose h : ℕ) : ZMod l) := dif_pos h
    apply Units.ext
    rw [hlx, Units.val_pow_eq_pow_val, ZMod.val_natCast_of_lt (Classical.choose_spec h).1]
    exact (Classical.choose_spec h).2
  have hy0 : y ≠ 0 := by
    intro h0
    have h1 : algebraMap E Ω a * ((b : L) : Ω) = 0 := by
      rw [← hy, h0, zero_pow (Fact.out : l.Prime).ne_zero]
    rcases mul_eq_zero.mp h1 with h | h
    · exact ha ((map_eq_zero _).mp h)
    · exact b.ne_zero (Subtype.ext h)
  set Y : Ωˣ := Units.mk0 y hy0
  have ha0 : algebraMap E Ω a ≠ 0 := (map_ne_zero _).mpr ha
  set aU : Ωˣ := Units.mk0 _ ha0
  have hafix : ∀ σ : Gal(Ω/E), σ • aU = aU := fun σ => Units.ext (σ.commutes a)
  have hY : Y ^ l = aU * φ b := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mul, hφ]; exact hy)
  -- `u σ = β(σ|L) y / σ y`
  set u : Gal(Ω/E) → Ωˣ := fun σ => φ (β (ρ σ)) * Y / σ • Y with hu_def
  have hu : ∀ σ, u σ ^ l = 1 := by
    intro σ
    have hb' : ρ σ • b = β (ρ σ) ^ l * b := by rw [← hb]; exact (div_mul_cancel _ _).symm
    have hσY : (σ • Y) ^ l = aU * (φ (β (ρ σ)) ^ l * φ b) := by
      rw [← smul_pow', hY, smul_mul', hafix, ← hφσ, hb', map_mul, map_pow]
    rw [hu_def]
    dsimp only
    rw [div_pow, mul_pow, hY, hσY]
    exact cg_pow _ _ _ _ rfl
  set γ : Gal(Ω/E) → ZMod l := fun σ => lg (u σ) with hγ_def
  have hγ : ∀ σ, zU ^ (γ σ).val = u σ := fun σ => hlg _ (hu σ)
  refine ⟨γ, fun σ τ => ?_, fun σ τ hρ hy' => ?_⟩
  · -- the multiplicative identity `u τ * u σ = ζ^f * u (σ τ)`
    have hfixu : σ • u τ = u τ := by rw [← hγ τ, smul_pow', hzfix]
    have hW : (σ * τ) • Y = σ • φ (β (ρ τ)) * σ • Y / u τ := by
      conv_rhs => rw [← hfixu]
      rw [hu_def]
      dsimp only
      rw [smul_div', smul_mul', mul_smul]
      exact (div_div_cancel _ _).symm
    have hc : σ • φ (β (ρ τ)) / φ (β (ρ (σ * τ))) * φ (β (ρ σ)) = zU ^ (f (ρ σ, ρ τ)).val := by
      have h1 := congrArg φ (hβ (ρ σ) (ρ τ))
      rw [map_mul, map_div, hφσ, ← map_mul ρ, map_pow, ← hzUdef] at h1
      exact h1
    have key : u τ * u σ = zU ^ (f (ρ σ, ρ τ)).val * u (σ * τ) := by
      rw [← hc]
      exact cg_key _ _ _ _ _ _ _ hW
    have hD : zU ^ (γ τ - γ (σ * τ) + γ σ).val * u (σ * τ) = zU ^ (f (ρ σ, ρ τ)).val * u (σ * τ) := by
      rw [← key, ← hγ (σ * τ), ← pow_val_add hprim.pow_eq_one, ← hγ τ, ← hγ σ, ← pow_val_add hprim.pow_eq_one]
      rw [show γ τ - γ (σ * τ) + γ σ + γ (σ * τ) = γ τ + γ σ by abel]
    have hD' := mul_right_cancel hD
    exact (ZMod.val_injective _ (hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hD')).symm
  · have hYe : σ • Y = τ • Y := Units.ext hy'
    rw [hγ_def, hu_def]
    dsimp only
    rw [hρ, hYe]

end Emb
end RamanujanPetersson.CdOne

end

-- ===== S4.Def_RP_CdOne_Field =====
section

/-!
# S4-PD (3), field layer: `HypL` for `Gal(Ω/E₀)` from Tsen + Kummer

Let `Ω/E₀` be a (possibly infinite) Galois extension with a primitive `l`-th root of unity in `E₀`, such that every
finite subextension `E/E₀` is C1 and satisfies the **Kummer closure** property: if `L/E` is a finite Galois
subextension and `b ∈ Lˣ` has `σ b / b ∈ Lˣˡ` for all `σ ∈ Gal(L/E)`, then some `a·b` (`a ∈ Eˣ`) has an `l`-th root
in `Ω` (for `Ω` the maximal unramified extension this is where `Pic(V̄)/l = 0` enters). Then `HypL l Gal(Ω/E₀)`
holds (`hypL_of_field`): for open `N ⊴ Q` with `Q/N` an `l`-group, `E := Ω^Q`, `L := Ω^N`, a `ℤ/l`-valued
2-cocycle on `Q` factoring through `Q/N = Gal(L/E)` is killed in `Gal(Ω/E) = Q` by `exists_kummer_data` and
`emb_coboundary`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open IntermediateField RamanujanPetersson.Tsen Topology

/-- A function constant on left cosets of an open subgroup is locally constant. -/
theorem lc_of_coset {P X : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] (W : Subgroup P)
    (hW : IsOpen (W : Set P)) (u : P → X) (hu : ∀ g, ∀ w ∈ W, u (g * w) = u g) : IsLocallyConstant u := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have h1 : (W : Set P) ∈ 𝓝 (1 : P) := hW.mem_nhds W.one_mem
  have h2 : Filter.Tendsto (fun x : P => g⁻¹ * x) (𝓝 g) (𝓝 1) := by
    have := (continuous_const_mul g⁻¹).tendsto g
    rwa [inv_mul_cancel] at this
  filter_upwards [h2 h1] with x hx
  have := hu g _ hx
  rwa [mul_inv_cancel_left] at this

variable {E₀ Ω : Type*} [Field E₀] [Field Ω] [Algebra E₀ Ω] [IsGalois E₀ Ω]

theorem fix_fixed_of_isOpen (Q : Subgroup Gal(Ω/E₀)) (hQ : IsOpen (Q : Set Gal(Ω/E₀))) :
    (fixedField Q).fixingSubgroup = Q :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨Q, Q.isClosed_of_isOpen hQ⟩

theorem finiteDimensional_fixedField_of_isOpen (Q : Subgroup Gal(Ω/E₀))
    (hQ : IsOpen (Q : Set Gal(Ω/E₀))) : FiniteDimensional E₀ (fixedField Q) :=
  (InfiniteGalois.isOpen_iff_finite (fixedField Q)).mp (by
    rw [fix_fixed_of_isOpen Q hQ]; exact hQ)

theorem finiteDimensional_extendScalars {E L' : IntermediateField E₀ Ω} (h : E ≤ L')
    [FiniteDimensional E₀ L'] : FiniteDimensional E (extendScalars h) := by
  have : Module.Finite E₀ (extendScalars h) := Module.Finite.of_surjective
    ({ toFun := fun x : L' => (⟨x.1, x.2⟩ : extendScalars h)
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : L' →ₗ[E₀] extendScalars h)
    (fun y => ⟨⟨y.1, y.2⟩, rfl⟩)
  exact Module.Finite.of_restrictScalars_finite E₀ E (extendScalars h)

theorem isGalois_extendScalars {Q N : Subgroup Gal(Ω/E₀)} (hQ : IsOpen (Q : Set Gal(Ω/E₀)))
    (hN : IsOpen (N : Set Gal(Ω/E₀))) (hnorm : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N)
    (h : fixedField Q ≤ fixedField N) : IsGalois (fixedField Q) (extendScalars h) := by
  rw [← InfiniteGalois.normal_iff_isGalois]
  constructor
  intro τ hτ g
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
  intro x hx
  have hg : ((fixingSubgroupEquiv (fixedField Q)).symm g : Gal(Ω/E₀)) ∈ Q :=
    (fix_fixed_of_isOpen Q hQ).le ((fixingSubgroupEquiv _).symm g).2
  have hτ' : ((fixingSubgroupEquiv (fixedField Q)).symm τ : Gal(Ω/E₀)) ∈ N :=
    (fix_fixed_of_isOpen N hN).le
      ((IntermediateField.mem_fixingSubgroup_iff _ _).mpr (fun y hy => hτ y hy))
  have := (IntermediateField.mem_fixingSubgroup_iff _ _).mp
    ((fix_fixed_of_isOpen N hN).ge (hnorm _ hg _ hτ'))
  exact this x hx

end RamanujanPetersson.CdOne


end


