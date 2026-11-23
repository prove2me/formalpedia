-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:35.465318+00:00
-- url     : https://prove2.me/theorems/e7c51eec-a361-4c30-aae5-87405edf9494
-- title:
--   Line Opposite Parabolic Unitary Levi Section Eq
-- statement:
--   Definitions and structural lemmas for Line Opposite Parabolic Unitary Levi Section Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_continuous_leviEmb
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero


set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
namespace GlobalTheory.LGrp
open GlobalTheory.PRep
section Alg
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def twist (χ : G →* ℂˣ) (ρ : Representation ℂ G V) : Representation ℂ G V where
  toFun g := (χ g : ℂ) • ρ g
  map_one' := by simp
  map_mul' a b := by
    ext v
    simp [smul_smul, mul_comm]
@[simp] theorem twist_apply (χ : G →* ℂˣ) (ρ : Representation ℂ G V) (g : G) (v : V) :
    twist χ ρ g v = (χ g : ℂ) • ρ g v := rfl
def charRep (χ : G →* ℂˣ) : Representation ℂ G ℂ := twist χ (Representation.trivial ℂ G ℂ)
@[simp] theorem charRep_apply (χ : G →* ℂˣ) (g : G) (z : ℂ) : charRep χ g z = (χ g : ℂ) * z := by
  simp [charRep]
def extProd (π : Representation ℂ G V) (π' : Representation ℂ H W) : Representation ℂ (G × H) (V ⊗[ℂ] W) :=
  Representation.tprod (π.comp (MonoidHom.fst G H)) (π'.comp (MonoidHom.snd G H))
@[simp] theorem extProd_tmul (π : Representation ℂ G V) (π' : Representation ℂ H W) (g : G × H) (v : V) (w : W) :
    extProd π π' g (v ⊗ₜ w) = π g.1 v ⊗ₜ π' g.2 w := by
  simp [extProd]
def IsSubquot (π : Representation ℂ G W) (ρ : Representation ℂ G V) : Prop :=
  ∃ (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap π), Function.Surjective f
def Embeds (π : Representation ℂ G W) (ρ : Representation ℂ G V) : Prop :=
  ∃ f : π.IntertwiningMap ρ, Function.Injective f
def HasFiniteLength (ρ : Representation ℂ G V) : Prop := IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule
def IsUnitarisable (ρ : Representation ℂ G V) : Prop :=
  ∃ B : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ, (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧
    (∀ v, v ≠ 0 → 0 < (B v v).re) ∧ ∀ g v w, B (ρ g v) (ρ g w) = B v w
def IsSpherical (ρ : Representation ℂ G V) (K : Subgroup G) : Prop := fixed ρ K ≠ ⊥
def coeff (ρ : Representation ℂ G V) (v : V) (l : Module.Dual ℂ V) : G → ℂ := fun g => l (ρ g v)
def IsZonal (ρ : Representation ℂ G V) (K : Subgroup G) (ω : G → ℂ) : Prop :=
  ∃ v ∈ fixed ρ K, ∃ l : Module.Dual ℂ V, (∀ k ∈ K, ∀ x, l (ρ k x) = l x) ∧ l v = 1 ∧ ω = coeff ρ v l
def twJacquet (ρ : Representation ℂ G V) (N : Subgroup G) (ψ : N →* ℂˣ) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * n * (s m)⁻¹ ∈ N, ψ ⟨_, h⟩ = ψ n) :
    Representation ℂ M (TwJacquet ρ N ψ) where
  toFun m := (twKer ρ N ψ).mapQ (twKer ρ N ψ) (ρ (s m)) (by
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, v, rfl⟩
    obtain ⟨hn, e⟩ := hs m n
    refine Submodule.subset_span ⟨⟨_, hn⟩, ρ (s m) v, ?_⟩
    rw [e, map_sub, map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group)
  map_one' := by ext v; simp
  map_mul' a b := by
    ext v
    show Submodule.Quotient.mk (ρ (s (a * b)) v) = Submodule.Quotient.mk (ρ (s a) (ρ (s b) v))
    simp
def coinvFst (ρ : Representation ℂ (G × H) V) :
    Representation ℂ H (Jacquet ρ (MonoidHom.inl G H).range) :=
  twJacquet ρ _ 1 (MonoidHom.inr G H) (by
    rintro m ⟨_, g, rfl⟩
    exact ⟨⟨g, by simp⟩, rfl⟩)
end Alg
section Top
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
def IsIrrSmooth (ρ : Representation ℂ G V) : Prop := IsSmooth ρ ∧ ρ.IsIrreducible
variable [IsTopologicalGroup G]
def smoothDual (ρ : Representation ℂ G V) : Representation ℂ G (smoothPart ρ.dual) := smoothRep ρ.dual
theorem smoothRep_isSmooth (ρ : Representation ℂ G V) : IsSmooth (smoothRep ρ) := by
  intro v
  have : {g : G | smoothRep ρ g v = v} = {g : G | ρ g v.1 = v.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact v.2
def IsMatrixCoeff (ρ : Representation ℂ G V) (c : G → ℂ) : Prop :=
  ∃ (v : V) (l : smoothPart ρ.dual), c = coeff ρ v l.1
def conjAut (U : Subgroup G) (g : Subgroup.normalizer (U : Set G)) : U ≃ₜ* U where
  toMulEquiv := U.normalizerMonoidHom g
  continuous_toFun := Continuous.subtype_mk
    (f := fun u : U => (g : G) * u * (g : G)⁻¹) (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk
    (f := fun u : U => ((g⁻¹ : Subgroup.normalizer (U : Set G)) : G) * u *
      ((g⁻¹ : Subgroup.normalizer (U : Set G)) : G)⁻¹) (by fun_prop) _
@[simp] theorem conjAut_coe (U : Subgroup G) (g : Subgroup.normalizer (U : Set G)) (u : U) :
    (conjAut U g u : G) = g * u * (g : G)⁻¹ := rfl
variable [LocallyCompactSpace G]
def modulus (U : Subgroup G) (hU : IsClosed (U : Set G)) : Subgroup.normalizer (U : Set G) →* ℝ≥0 :=
  letI : MeasurableSpace U := borel U
  haveI : BorelSpace U := ⟨rfl⟩
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  { toFun := fun g => mulEquivHaarChar (conjAut U g)
    map_one' := by
      have : conjAut U 1 = ContinuousMulEquiv.refl U := by ext u; simp
      simp only [this, mulEquivHaarChar_refl]
    map_mul' := fun a b => by
      have : conjAut U (a * b) = (conjAut U b).trans (conjAut U a) := by ext u; simp [mul_assoc]
      simp only [this, mulEquivHaarChar_trans, mul_comm] }
end Top
structure LeviDatum (G M : Type) [Group G] [TopologicalSpace G] [Group M] [TopologicalSpace M] where

  Q : Subgroup G

  s : M →* G

  p : Q →* M
  s_mem : ∀ m, s m ∈ Q
  p_s : ∀ m, p ⟨s m, s_mem m⟩ = m
  closed_Q : IsClosed (Q : Set G)
  leviSection_continuous : Continuous s
  cont_p : Continuous p
namespace LeviDatum
variable {G M : Type} [Group G] [TopologicalSpace G] [Group M] [TopologicalSpace M] (P : LeviDatum G M)
def U : Subgroup G := P.p.ker.map P.Q.subtype
def L : Subgroup G := P.s.range
def sQ : M →* P.Q := P.s.codRestrict P.Q P.s_mem
theorem mem_U {g : G} : g ∈ P.U ↔ ∃ h : g ∈ P.Q, P.p ⟨g, h⟩ = 1 := by
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q.2, hq⟩
  · rintro ⟨h, e⟩; exact ⟨⟨g, h⟩, e, rfl⟩
theorem Q_le_normalizer : P.Q ≤ Subgroup.normalizer (P.U : Set G) := by
  have key : ∀ q ∈ P.Q, ∀ u ∈ P.U, q * u * q⁻¹ ∈ P.U := by
    intro q hq u hu
    obtain ⟨h, e⟩ := P.mem_U.1 hu
    refine ⟨⟨q, hq⟩ * ⟨u, h⟩ * ⟨q, hq⟩⁻¹, ?_, rfl⟩
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, e, map_inv, mul_one, mul_inv_cancel]
  intro q hq
  refine Subgroup.mem_normalizer_iff.2 fun u => ⟨key q hq u, fun h => ?_⟩
  have := key q⁻¹ (inv_mem hq) _ h
  simpa [mul_assoc] using this
theorem closed_U [T1Space M] : IsClosed (P.U : Set G) := by
  have : IsClosed (P.p.ker : Set P.Q) := isClosed_singleton.preimage P.cont_p
  exact P.closed_Q.isClosedMap_subtype_val _ this
def IsOpposite (P' : LeviDatum G M) : Prop := P.s = P'.s ∧ P.Q ⊓ P'.Q = P.L
def restrict (H : Subgroup G) (hH : ∀ q : P.Q, (q : G) ∈ H → P.s (P.p q) ∈ H) : LeviDatum H (H.comap P.s) where
  Q := P.Q.subgroupOf H
  s := P.s.subgroupComap H
  p := ((P.p.comp ((H.subtype.subgroupComap P.Q)))).codRestrict _ fun q => hH _ q.1.2
  s_mem m := P.s_mem m
  p_s m := Subtype.ext (P.p_s m)
  closed_Q := P.closed_Q.preimage continuous_subtype_val
  leviSection_continuous := (P.leviSection_continuous.comp continuous_subtype_val).subtype_mk _
  cont_p := (P.cont_p.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _
def comap {G' : Type} [Group G'] [TopologicalSpace G'] (e : G' ≃ₜ* G) : LeviDatum G' M where
  Q := P.Q.comap e.toMulEquiv.toMonoidHom
  s := e.symm.toMulEquiv.toMonoidHom.comp P.s
  p := P.p.comp (e.toMulEquiv.toMonoidHom.subgroupComap P.Q)
  s_mem m := by
    show e (e.symm (P.s m)) ∈ P.Q
    rw [e.apply_symm_apply]; exact P.s_mem m
  p_s m := by
    refine Eq.trans (congrArg P.p (Subtype.ext ?_)) (P.p_s m)
    exact e.apply_symm_apply _
  closed_Q := P.closed_Q.preimage e.continuous
  leviSection_continuous := e.symm.continuous.comp P.leviSection_continuous
  cont_p := P.cont_p.comp ((e.continuous.comp continuous_subtype_val).subtype_mk _)
def reparam {M' : Type} [Group M'] [TopologicalSpace M'] (e : M' ≃ₜ* M) : LeviDatum G M' where
  Q := P.Q
  s := P.s.comp e.toMulEquiv.toMonoidHom
  p := e.symm.toMulEquiv.toMonoidHom.comp P.p
  s_mem m := P.s_mem _
  p_s m := by
    show e.symm (P.p ⟨P.s (e m), _⟩) = m
    rw [P.p_s, e.symm_apply_apply]
  closed_Q := P.closed_Q
  leviSection_continuous := P.leviSection_continuous.comp e.continuous
  cont_p := e.symm.continuous.comp P.cont_p
def prod (H : Type) [Group H] [TopologicalSpace H] : LeviDatum (G × H) (M × H) where
  Q := P.Q.comap (MonoidHom.fst G H)
  s := P.s.prodMap (MonoidHom.id H)
  p := (P.p.comp ((MonoidHom.fst G H).subgroupComap P.Q)).prod ((MonoidHom.snd G H).comp (Subgroup.subtype _))
  s_mem m := P.s_mem m.1
  p_s m := Prod.ext (P.p_s m.1) rfl
  closed_Q := P.closed_Q.preimage continuous_fst
  leviSection_continuous := P.leviSection_continuous.prodMap continuous_id
  cont_p := (P.cont_p.comp ((continuous_fst.comp continuous_subtype_val).subtype_mk _)).prodMk
    (continuous_snd.comp continuous_subtype_val)
variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T1Space M]
def delta : P.Q →* ℝ≥0 :=
  (modulus P.U P.closed_U).comp ((Subgroup.inclusion P.Q_le_normalizer).comp (P.sQ.comp P.p))
def deltaHalf : P.Q →* ℂˣ :=
  (((Complex.ofRealHom.comp NNReal.toRealHom : ℝ≥0 →+* ℂ) : ℝ≥0 →* ℂ).comp
    ((NNReal.sqrtHom : ℝ≥0 →* ℝ≥0).comp P.delta)).toHomUnits
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def nIndQ (τ : Representation ℂ P.Q W) : Representation ℂ G (smoothPart (ind P.Q (twist P.deltaHalf τ))) :=
  smInd P.Q (twist P.deltaHalf τ)
abbrev IndSpace (σ : Representation ℂ M W) : Type := smoothPart (ind P.Q (twist P.deltaHalf (σ.comp P.p)))
def nInd (σ : Representation ℂ M W) : Representation ℂ G (P.IndSpace σ) := P.nIndQ (σ.comp P.p)
theorem nInd_isSmooth (σ : Representation ℂ M W) : IsSmooth (P.nInd σ) := smoothRep_isSmooth _
def rJac (π : Representation ℂ G V) : Representation ℂ M (Jacquet π P.U) :=
  twist (P.deltaHalf.comp P.sQ)⁻¹ (jacquet π P.U P.s fun m => P.Q_le_normalizer (P.s_mem m))
def IsConstituent (π : Representation ℂ G V) (σ : Representation ℂ M W) : Prop :=
  IsIrrSmooth π ∧ IsSubquot π (P.nInd σ)
def IsCuspSupport [IsTopologicalGroup M] (π : Representation ℂ G V) (σ : Representation ℂ M W) : Prop :=
  σ.IsIrreducible ∧ IsSupercuspidal σ ∧ P.IsConstituent π σ
end LeviDatum
section Blocks
variable {k n α : Type} [Field k] [Fintype n] [DecidableEq n] [LinearOrder α]
def blockQ (k : Type) [Field k] (b : n → α) : Subgroup (GL n k) where
  carrier := {g | (g : Matrix n n k).BlockTriangular b}
  one_mem' := blockTriangular_one
  mul_mem' hx hy := BlockTriangular.mul hx hy
  inv_mem' := by
    intro x hx
    show ((x⁻¹ : GL n k) : Matrix n n k).BlockTriangular b
    have : Invertible (x : Matrix n n k) := x.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hx
def blockL (k : Type) [Field k] (b : n → α) : Subgroup (GL n k) where
  carrier := {g | ∀ i j, b i ≠ b j → (g : Matrix n n k) i j = 0}
  one_mem' i j h := Matrix.one_apply_ne fun e => h (congrArg b e)
  mul_mem' := by
    intro x y hx hy i j h
    rcases lt_or_gt_of_ne h with h | h
    · exact (blockQ k (α := αᵒᵈ) b).mul_mem (fun _ _ h => hx _ _ (ne_of_lt h)) (fun _ _ h => hy _ _ (ne_of_lt h)) h
    · exact (blockQ k b).mul_mem (fun _ _ h => hx _ _ (ne_of_gt h)) (fun _ _ h => hy _ _ (ne_of_gt h)) h
  inv_mem' := by
    intro x hx i j h
    rcases lt_or_gt_of_ne h with h | h
    · exact (blockQ k (α := αᵒᵈ) b).inv_mem (fun _ _ h => hx _ _ (ne_of_lt h)) h
    · exact (blockQ k b).inv_mem (fun _ _ h => hx _ _ (ne_of_gt h)) h
theorem blockL_le (b : n → α) : blockL k b ≤ blockQ k b := fun _ hx _ _ h => hx _ _ (ne_of_gt h)
def blockPart (b : n → α) (A : Matrix n n k) : Matrix n n k := fun i j => if b i = b j then A i j else 0
omit [DecidableEq n] in
theorem blockPart_mul {b : n → α} {A B : Matrix n n k} (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) :
    blockPart b (A * B) = blockPart b A * blockPart b B := by
  ext i j
  simp only [blockPart, mul_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy (b l) (b i) with h' | h' | h'
    · simp [hA h']
    · simp [h', h]
    · simp [hB (h ▸ h' : b j < b l)]
  · refine (Finset.sum_eq_zero fun l _ => ?_).symm
    by_cases h' : b i = b l
    · simp [← h', h]
    · simp [h']
def blockProj (b : n → α) : blockQ k b →* GL n k :=
  MonoidHom.toHomUnits
    { toFun := fun q => blockPart b (q : GL n k).val
      map_one' := by
        ext i j
        by_cases h : i = j <;> simp [blockPart, Matrix.one_apply, h]
      map_mul' := fun x y => blockPart_mul x.2 y.2 }
theorem blockProj_val (b : n → α) (q : blockQ k b) : (blockProj b q).val = blockPart b (q : GL n k).val := rfl
theorem blockProj_mem (b : n → α) (q : blockQ k b) : blockProj b q ∈ blockL k b :=
  fun i j h => by simp [blockProj_val, blockPart, h]
theorem blockProj_of_mem (b : n → α) (q : blockQ k b) (h : (q : GL n k) ∈ blockL k b) : blockProj b q = q := by
  ext i j
  by_cases e : b i = b j
  · simp [blockProj_val, blockPart, e]
  · simp [blockProj_val, blockPart, e, h i j e]
def diagHom (k n : Type) [Field k] [Fintype n] [DecidableEq n] : (n → kˣ) →* GL n k :=
  MonoidHom.toHomUnits
    { toFun := fun t => diagonal fun i => (t i : k)
      map_one' := by simp
      map_mul' := fun x y => by simp [diagonal_mul_diagonal] }
theorem diagHom_val (t : n → kˣ) : (diagHom k n t).val = diagonal fun i => (t i : k) := rfl
def diagEntries {b : n → α} (hb : Function.Injective b) : blockQ k b →* (n → kˣ) :=
  MonoidHom.pi fun i => MonoidHom.toHomUnits
    { toFun := fun q => (q : GL n k).val i i
      map_one' := by simp
      map_mul' := fun x y => by
        have := congrFun (congrFun (blockPart_mul x.2 y.2) i) i
        simp only [blockPart, if_true, mul_apply, hb.eq_iff] at this
        show ((x : GL n k).val * (y : GL n k).val) i i = _
        rw [mul_apply, this, Finset.sum_eq_single i] <;> simp +contextual [eq_comm] }
theorem diagEntries_val {b : n → α} (hb : Function.Injective b) (q : blockQ k b) (i : n) :
    (diagEntries hb q i : k) = (q : GL n k).val i i := rfl
theorem diagHom_diagEntries {b : n → α} (hb : Function.Injective b) (q : blockQ k b) :
    diagHom k n (diagEntries hb q) = blockProj b q := by
  ext i j
  by_cases h : i = j <;> simp [diagHom_val, diagEntries_val, blockProj_val, blockPart, diagonal_apply, h, hb.eq_iff]
variable [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
theorem continuous_toHomUnits {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Monoid A]
    [TopologicalSpace A] (f : G →* A) (hf : Continuous f) : Continuous f.toHomUnits :=
  Units.continuous_iff.2 ⟨hf, hf.comp continuous_inv⟩
instance locallyCompact_GL [LocallyCompactSpace k] : LocallyCompactSpace (GL n k) := by
  haveI : LocallyCompactSpace (Matrix n n k) := inferInstanceAs (LocallyCompactSpace (n → n → k))
  haveI : LocallyCompactSpace (Matrix n n k)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace
omit [IsTopologicalRing k] [T2Space k] in
theorem continuous_entry (i j : n) : Continuous fun g : GL n k => g.val i j :=
  Units.continuous_val.matrix_elem i j
omit [IsTopologicalRing k] in
theorem isClosed_blockQ (b : n → α) : IsClosed (blockQ k b : Set (GL n k)) := by
  have : (blockQ k b : Set (GL n k)) = ⋂ i, ⋂ j, ⋂ _ : b j < b i, {g | g.val i j = 0} := by
    ext g; simp only [Set.mem_iInter]; exact ⟨fun h _ _ e => h e, fun h _ _ e => h _ _ e⟩
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (continuous_entry i j) continuous_const
omit [IsTopologicalRing k] in
theorem isClosed_blockL (b : n → α) : IsClosed (blockL k b : Set (GL n k)) := by
  have : (blockL k b : Set (GL n k)) = ⋂ i, ⋂ j, ⋂ _ : b i ≠ b j, {g | g.val i j = 0} := by
    ext g; simp only [Set.mem_iInter]; exact ⟨fun h _ _ e => h _ _ e, fun h _ _ e => h _ _ e⟩
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (continuous_entry i j) continuous_const
instance locallyCompact_blockL [LocallyCompactSpace k] (b : n → α) : LocallyCompactSpace (blockL k b) :=
  (isClosed_blockL b).locallyCompactSpace
omit [T2Space k] in
theorem continuous_blockProj (b : n → α) : Continuous (blockProj (k := k) b) := by
  refine continuous_toHomUnits _ (continuous_matrix fun i j => ?_)
  show Continuous fun q : blockQ k b => if b i = b j then (q : GL n k).val i j else 0
  split_ifs
  · exact (continuous_entry i j).comp continuous_subtype_val
  · exact continuous_const
def stdPar (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] (b : n → α) :
    LeviDatum (GL n k) (blockL k b) where
  Q := blockQ k b
  s := (blockL k b).subtype
  p := (blockProj b).codRestrict _ (blockProj_mem b)
  s_mem m := blockL_le b m.2
  p_s m := Subtype.ext (blockProj_of_mem b _ m.2)
  closed_Q := isClosed_blockQ b
  leviSection_continuous := continuous_subtype_val
  cont_p := (continuous_blockProj b).subtype_mk _
def stdParOp (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] (b : n → α) :
    LeviDatum (GL n k) (blockL k b) := stdPar k (α := αᵒᵈ) b
def parIn (b : n → α) (H : Subgroup (GL n k)) (hH : ∀ q : blockQ k b, (q : GL n k) ∈ H → blockProj b q ∈ H) :
    LeviDatum H (H ⊓ blockL k b : Subgroup (GL n k)) where
  Q := (blockQ k b).subgroupOf H
  s := Subgroup.inclusion inf_le_left
  p := ((blockProj b).comp (H.subtype.subgroupComap _)).codRestrict _ fun q => ⟨hH _ q.1.2, blockProj_mem b _⟩
  s_mem m := blockL_le b m.2.2
  p_s m := Subtype.ext (blockProj_of_mem b _ m.2.2)
  closed_Q := (isClosed_blockQ b).preimage continuous_subtype_val
  leviSection_continuous := continuous_subtype_val.subtype_mk _
  cont_p := ((continuous_blockProj b).comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _
def borelOf (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] {b : n → α}
    (hb : Function.Injective b) : LeviDatum (GL n k) (n → kˣ) where
  Q := blockQ k b
  s := diagHom k n
  p := diagEntries hb
  s_mem m i j h := diagonal_apply_ne _ fun e => h.ne' (congrArg b e)
  p_s m := by ext i; simp [diagEntries_val, diagHom_val]
  closed_Q := isClosed_blockQ b
  leviSection_continuous := continuous_toHomUnits _ (Continuous.matrix_diagonal
    (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i)))
  cont_p := continuous_pi fun i => continuous_toHomUnits _ ((continuous_entry i i).comp continuous_subtype_val)
def borelGL (k n : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] [Fintype n] [DecidableEq n]
    [LinearOrder n] : LeviDatum (GL n k) (n → kˣ) := borelOf k (b := id) Function.injective_id
def borelIn [LinearOrder n] (H : Subgroup (GL n k))
    (hH : ∀ q : blockQ k (id : n → n), (q : GL n k) ∈ H → blockProj id q ∈ H) :
    LeviDatum H (H.comap (diagHom k n)) :=
  (borelGL k n).restrict H fun (q : blockQ k (id : n → n)) hq => by
    have := hH q hq
    rw [← diagHom_diagEntries Function.injective_id] at this
    exact this
omit [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] in

theorem blockProj_mem_blockL {β : Type} [LinearOrder β] (b : n → α) (c : n → β) (q : blockQ k c)
    (h : (q : GL n k) ∈ blockL k b) : blockProj c q ∈ blockL k b :=
  fun i j e => by simp [blockProj_val, blockPart, h i j e]
def borelLevi [LinearOrder n] (b : n → α) : LeviDatum (blockL k b) ((blockL k b).comap (diagHom k n)) :=
  borelIn _ (blockProj_mem_blockL b id)
variable {a d : Type} [Fintype a] [DecidableEq a] [Fintype d] [DecidableEq d]
def twoBlocks (a d : Type) : a ⊕ d → ℕ := Sum.elim (fun _ => 0) fun _ => 1
omit [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] in
theorem mem_blockQ_two {g : GL (a ⊕ d) k} : g ∈ blockQ k (twoBlocks a d) ↔ g.val.toBlocks₂₁ = 0 := by
  constructor
  · intro h; ext i j; exact h (by simp [twoBlocks])
  · rintro h (i | i) (j | j) e
    · simp [twoBlocks] at e
    · simp [twoBlocks] at e
    · exact congrFun (congrFun h i) j
    · simp [twoBlocks] at e
omit [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] in
theorem toBlocks_mul (x y : blockQ k (twoBlocks a d)) :
    ((x * y : blockQ k (twoBlocks a d)) : GL (a ⊕ d) k).val.toBlocks₁₁ = x.1.val.toBlocks₁₁ * y.1.val.toBlocks₁₁ ∧
    ((x * y : blockQ k (twoBlocks a d)) : GL (a ⊕ d) k).val.toBlocks₂₂ = x.1.val.toBlocks₂₂ * y.1.val.toBlocks₂₂ := by
  have hx := mem_blockQ_two.1 x.2
  have hy := mem_blockQ_two.1 y.2
  have e : ((x * y : blockQ k (twoBlocks a d)) : GL (a ⊕ d) k).val = x.1.val * y.1.val := rfl
  rw [e]
  constructor
  · conv_lhs => rw [← fromBlocks_toBlocks x.1.val, ← fromBlocks_toBlocks y.1.val, fromBlocks_multiply]
    simp [hy]
  · conv_lhs => rw [← fromBlocks_toBlocks x.1.val, ← fromBlocks_toBlocks y.1.val, fromBlocks_multiply]
    simp [hx]
def blockPar (k a d : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    [Fintype a] [DecidableEq a] [Fintype d] [DecidableEq d] : LeviDatum (GL (a ⊕ d) k) (GL a k × GL d k) where
  Q := blockQ k (twoBlocks a d)
  s := MonoidHom.toHomUnits
    { toFun := fun m => fromBlocks m.1.val 0 0 m.2.val
      map_one' := by simp
      map_mul' := fun x y => by simp [fromBlocks_multiply] }
  p := (MonoidHom.toHomUnits
    { toFun := fun q : blockQ k (twoBlocks a d) => q.1.val.toBlocks₁₁
      map_one' := by simp [← fromBlocks_one]
      map_mul' := fun x y => (toBlocks_mul x y).1 }).prod (MonoidHom.toHomUnits
    { toFun := fun q : blockQ k (twoBlocks a d) => q.1.val.toBlocks₂₂
      map_one' := by simp [← fromBlocks_one]
      map_mul' := fun x y => (toBlocks_mul x y).2 })
  s_mem m := mem_blockQ_two.2 rfl
  p_s m := Prod.ext (Units.ext rfl) (Units.ext rfl)
  closed_Q := isClosed_blockQ _
  leviSection_continuous := continuous_toHomUnits _ (Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst)
    continuous_const continuous_const (Units.continuous_val.comp continuous_snd))
  cont_p := (continuous_toHomUnits _ (continuous_matrix fun i j =>
      (continuous_entry (Sum.inl i) (Sum.inl j)).comp continuous_subtype_val)).prodMk
    (continuous_toHomUnits _ (continuous_matrix fun i j =>
      (continuous_entry (Sum.inr i) (Sum.inr j)).comp continuous_subtype_val))
def glReindex (k : Type) [Field k] [TopologicalSpace k] (e : n ≃ d) : GL n k ≃ₜ* GL d k :=
  Units.mapContinuousMulEquiv
    { toMulEquiv := (Matrix.reindexRingEquiv k e).toMulEquiv
      continuous_toFun := continuous_id.matrix_reindex e e
      continuous_invFun := continuous_id.matrix_reindex e.symm e.symm }
def blockParOf (e : n ≃ a ⊕ d) : LeviDatum (GL n k) (GL a k × GL d k) := (blockPar k a d).comap (glReindex k e)
def blockParFin (r t : ℕ) : LeviDatum (GL (Fin (r + t)) k) (GL (Fin r) k × GL (Fin t) k) :=
  blockParOf finSumFinEquiv.symm
end Blocks
section Unram
open WithZero
def ordHom {k : Type} [Field k] (v : k →*₀ WithZero (Multiplicative ℤ)) : kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (-log (v x))
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, map_mul, log_mul (by simp) (by simp), neg_add, ofAdd_add]
def unrChar {k : Type} [Field k] (v : k →*₀ WithZero (Multiplicative ℤ)) (z : ℂˣ) : kˣ →* ℂˣ :=
  (zpowersHom ℂˣ z).comp (ordHom v)
def unrTorus {k n : Type} [Field k] [Fintype n] (v : k →*₀ WithZero (Multiplicative ℤ)) (α : n → ℂˣ) :
    (n → kˣ) →* ℂˣ :=
  ∏ i, (unrChar v (α i)).comp (Pi.evalMonoidHom (fun _ : n => kˣ) i)
end Unram
section LocalGL
open ValuativeRel
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
instance t2Space_of_nonarchimedeanLocalField : T2Space k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance
def vZ : k →*₀ WithZero (Multiplicative ℤ) :=
  ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k).toMulEquiv.toMonoidWithZeroHom).comp
    (valuation k).toMonoidWithZeroHom
variable {k}
variable (k) {n V : Type} [Fintype n] [DecidableEq n] [LinearOrder n] [AddCommGroup V] [Module ℂ V]
def psGL (α : n → ℂˣ) : Representation ℂ (GL n k) ((borelGL k n).IndSpace (charRep (unrTorus (vZ k) α))) :=
  (borelGL k n).nInd (charRep (unrTorus (vZ k) α))
variable {k}
def InUPSGL (π : Representation ℂ (GL n k) V) (S : Multiset ℂˣ) : Prop :=
  ∃ α : n → ℂˣ, Finset.univ.val.map α = S ∧ IsIrrSmooth π ∧ IsSubquot π (psGL k α)
def HasSatakeGL (π : Representation ℂ (GL n k) V) (S : Multiset ℂˣ) : Prop :=
  InUPSGL π S ∧ IsSpherical π (SplitWeil.KO k n)
end LocalGL
section Unitary
open Formalism.UG
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {α : Type} [LinearOrder α]
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem antiJ_apply (n : ℕ) (i j : Fin n) : antiJ L n i j = if j = i.rev then 1 else 0 := by
  unfold antiJ
  congr 1
  rw [Fin.ext_iff, Fin.val_rev]
  apply propext
  omega
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem antiJ_mul_apply (n : ℕ) (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (antiJ L n * A) i j = A i.rev j := by
  simp [mul_apply, antiJ_apply]
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mul_antiJ_apply (n : ℕ) (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (A * antiJ L n) i j = A i j.rev := by
  simp only [mul_apply, antiJ_apply, eq_comm (a := j), Fin.rev_eq_iff]
  simp
omit [Valued L (WithZero (Multiplicative ℤ))] in

theorem mem_GU_iff (σ : L →+* L) (n : ℕ) (g : GL (Fin n) L) :
    g ∈ GU σ n ↔ ∀ i j, (g⁻¹).val i j = σ (g.val j.rev i.rev) := by
  have h1 : g ∈ GU σ n ↔ cT σ g.val * antiJ L n = antiJ L n * (g⁻¹).val := by
    show cT σ g.val * antiJ L n * g.val = antiJ L n ↔ _
    constructor
    · intro h
      conv_rhs => rw [← h]
      rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    · intro h
      rw [h, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [h1, ← Matrix.ext_iff]
  simp only [antiJ_mul_apply, mul_antiJ_apply, cT, transpose_apply, map_apply]
  exact ⟨fun h i j => by simpa using (h i.rev j).symm, fun h i j => by simpa using (h i.rev j).symm⟩
def SelfDualBlocks {n : ℕ} (b : Fin n → α) : Prop := ∀ i j, b i.rev < b j.rev ↔ b j < b i
theorem selfDualBlocks_id (n : ℕ) : SelfDualBlocks (id : Fin n → Fin n) := fun _ _ => Fin.rev_lt_rev
theorem SelfDualBlocks.dual {n : ℕ} {b : Fin n → α} (hb : SelfDualBlocks b) : SelfDualBlocks (α := αᵒᵈ) b :=
  fun i j => hb j i
omit [Valued L (WithZero (Multiplicative ℤ))] in

theorem blockProj_mem_GU (σ : L →+* L) {n : ℕ} {b : Fin n → α} (hb : SelfDualBlocks b) (q : blockQ L b)
    (hq : (q : GL (Fin n) L) ∈ GU σ n) : blockProj b q ∈ GU σ n := by
  rw [mem_GU_iff] at hq ⊢
  intro i j
  have e : b j.rev = b i.rev ↔ b i = b j := by
    rw [← not_iff_not, ← ne_eq, ← ne_eq, ne_iff_lt_or_gt, ne_iff_lt_or_gt, hb, hb]
  rw [← map_inv, blockProj_val, blockProj_val]
  simp only [blockPart, e]
  split_ifs
  · exact hq i j
  · simp
def parU (σ : L →+* L) {n : ℕ} {b : Fin n → α} (hb : SelfDualBlocks b) :
    LeviDatum (GU σ n) (GU σ n ⊓ blockL L b : Subgroup (GL (Fin n) L)) :=
  parIn b _ (blockProj_mem_GU σ hb)
def parUOp (σ : L →+* L) {n : ℕ} {b : Fin n → α} (hb : SelfDualBlocks b) :
    LeviDatum (GU σ n) (GU σ n ⊓ blockL L b : Subgroup (GL (Fin n) L)) :=
  parU (α := αᵒᵈ) σ hb.dual
def lineBlocks (n : ℕ) (i : Fin n) : ℤ := (if i.val + 1 = n then 1 else 0) - (if i.val = 0 then 1 else 0)
theorem selfDualBlocks_line (n : ℕ) : SelfDualBlocks (lineBlocks n) := by
  intro i j
  have hi := i.2
  have hj := j.2
  simp only [lineBlocks, Fin.val_rev]
  split_ifs <;> omega
abbrev torusU (σ : L →+* L) (n : ℕ) : Subgroup (Fin n → Lˣ) := (GU σ n).comap (diagHom L (Fin n))
def borelU (σ : L →+* L) (n : ℕ) : LeviDatum (GU σ n) (torusU σ n) :=
  borelIn _ (blockProj_mem_GU σ (selfDualBlocks_id n))
def borelLeviU (σ : L →+* L) {n : ℕ} (b : Fin n → α) :
    LeviDatum (GU σ n ⊓ blockL L b : Subgroup (GL (Fin n) L)) ((GU σ n ⊓ blockL L b).comap (diagHom L (Fin n))) :=
  borelIn _ fun q hq => ⟨blockProj_mem_GU σ (selfDualBlocks_id n) q hq.1, blockProj_mem_blockL b id q hq.2⟩
instance locallyCompact_leviU (σ : L →+* L) {n : ℕ} (b : Fin n → α) [LocallyCompactSpace (GU σ n)] :
    LocallyCompactSpace (GU σ n ⊓ blockL L b : Subgroup (GL (Fin n) L)) := by
  have h : Topology.IsClosedEmbedding (Subgroup.inclusion (inf_le_left : GU σ n ⊓ blockL L b ≤ GU σ n)) := by
    refine ⟨Topology.IsEmbedding.inclusion (inf_le_left : GU σ n ⊓ blockL L b ≤ GU σ n), ?_⟩
    have : Set.range (Subgroup.inclusion (inf_le_left : GU σ n ⊓ blockL L b ≤ GU σ n)) =
        Subtype.val ⁻¹' (blockL L b : Set (GL (Fin n) L)) := by
      ext g
      exact ⟨by rintro ⟨m, rfl⟩; exact m.2.2, fun h => ⟨⟨g.1, g.2, h⟩, rfl⟩⟩
    rw [this]
    exact (isClosed_blockL b).preimage continuous_subtype_val
  exact h.locallyCompactSpace
theorem locallyCompact_GU [LocallyCompactSpace L] (σ : L →+* L) (hσ : Continuous σ) (n : ℕ) :
    LocallyCompactSpace (GU σ n) := by
  refine IsClosed.locallyCompactSpace (s := (GU σ n : Set (GL (Fin n) L))) ?_
  exact isClosed_eq (((Units.continuous_val.matrix_map hσ).matrix_transpose.matrix_mul continuous_const).matrix_mul
    Units.continuous_val) continuous_const
def unrU (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (α : Fin (n / 2) → ℂˣ) :
    (Fin n → Lˣ) →* ℂˣ :=
  ∏ i, (unrChar (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom (α i)).comp
    (Pi.evalMonoidHom (fun _ : Fin n => Lˣ) (Fin.castLE (Nat.div_le_self n 2) i))
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
def psU (σ : L →+* L) [LocallyCompactSpace (GU σ n)] (α : Fin (n / 2) → ℂˣ) :
    Representation ℂ (GU σ n) ((borelU σ n).IndSpace (charRep ((unrU L α).comp (torusU σ n).subtype))) :=
  (borelU σ n).nInd (charRep ((unrU L α).comp (torusU σ n).subtype))
def InUPSU {σ : L →+* L} [LocallyCompactSpace (GU σ n)] (π : Representation ℂ (GU σ n) V)
    (α : Fin (n / 2) → ℂˣ) : Prop :=
  IsIrrSmooth π ∧ IsSubquot π (psU σ α)
def HasSatakeU {σ : L →+* L} [LocallyCompactSpace (GU σ n)] (π : Representation ℂ (GU σ n) V)
    (α : Fin (n / 2) → ℂˣ) : Prop :=
  InUPSU π α ∧ IsSpherical π (KU σ n)
def WeylConjU {r : ℕ} (α β : Fin r → ℂˣ) : Prop :=
  ∃ w : Equiv.Perm (Fin r), ∀ i, β i = α (w i) ∨ β i = (α (w i))⁻¹
def bcParam (n : ℕ) (α : Fin (n / 2) → ℂˣ) : Multiset ℂˣ :=
  Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) + Multiset.replicate (n % 2) 1
def twParam (z : ℂˣ) (n : ℕ) (α : Fin (n / 2) → ℂˣ) : Multiset ℂˣ := (bcParam n α).map (z⁻¹ * ·)
end Unitary
section Examples
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open Formalism.UG
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
theorem locallyCompact_GU_of_unram [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (n : ℕ) :
    LocallyCompactSpace (GU σ n) := by
  obtain ⟨-, hv, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := L)).2 ⟨inferInstance, (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (by
        refine ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  haveI : LocallyCompactSpace L := by
    open scoped Valued in exact inferInstance
  refine locallyCompact_GU σ (continuous_of_continuousAt_zero σ ?_) n
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero L _).tendsto_iff (Valued.hasBasis_nhds_zero L _)]
  refine fun γ _ => ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  rwa [show Valued.v.restrict (σ x) = Valued.v.restrict x from (Valuation.restrict_inj _).2 (hv x)]
end Examples
section Coinv
variable {A G H V W : Type} [Group A] [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def tensorFst (ω : Representation ℂ (G × H) V) (τ : Representation ℂ G W) : Representation ℂ (G × H) (V ⊗[ℂ] W) :=
  Representation.tprod ω (τ.comp (MonoidHom.fst G H))
@[simp] theorem tensorFst_tmul (ω : Representation ℂ (G × H) V) (τ : Representation ℂ G W) (g : G × H) (v : V)
    (w : W) : tensorFst ω τ g (v ⊗ₜ w) = ω g v ⊗ₜ τ g.1 w := by
  simp [tensorFst]
def coinvTensor (ω : Representation ℂ (G × H) V) (τ : Representation ℂ G W) :
    Representation ℂ H (Jacquet (tensorFst ω τ) (MonoidHom.inl G H).range) :=
  coinvFst (tensorFst ω τ)
def charFst (H : Type) [Group H] (χ : A →* ℂˣ) : (MonoidHom.inl A H).range →* ℂˣ :=
  χ.comp ((MonoidHom.fst A H).comp (Subgroup.subtype _))
def coinvChar (χ : A →* ℂˣ) (ρ : Representation ℂ (A × H) V) :
    Representation ℂ H (TwJacquet ρ (MonoidHom.inl A H).range (charFst H χ)) :=
  twJacquet ρ _ _ (MonoidHom.inr A H) (by
    rintro m ⟨_, g, rfl⟩
    exact ⟨⟨g, by simp⟩, by simp [charFst]⟩)
def coinvTensorChar (χ : A →* ℂˣ) (ω : Representation ℂ (A × H) V) (τ : Representation ℂ A W) :
    Representation ℂ H (TwJacquet (tensorFst ω τ) (MonoidHom.inl A H).range (charFst H χ)) :=
  coinvChar χ (tensorFst ω τ)
def prodSwapMid (A G H : Type) [Group A] [Group G] [Group H] : A × (G × H) ≃* G × (A × H) where
  toFun x := (x.2.1, x.1, x.2.2)
  invFun x := (x.2.1, x.1, x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
def coinvCharMid (χ : A →* ℂˣ) (ρ : Representation ℂ (G × (A × H)) V) :
    Representation ℂ (G × H) (TwJacquet (ρ.comp (prodSwapMid A G H).toMonoidHom) (MonoidHom.inl A (G × H)).range
      (charFst (G × H) χ)) :=
  coinvChar χ (ρ.comp (prodSwapMid A G H).toMonoidHom)
variable [TopologicalSpace G] [IsTopologicalGroup G]
end Coinv
namespace LeviDatum
variable {G M : Type} [Group G] [TopologicalSpace G] [Group M] [TopologicalSpace M] (P : LeviDatum G M)
def prodLeft (H : Type) [Group H] [TopologicalSpace H] : LeviDatum (H × G) (H × M) where
  Q := P.Q.comap (MonoidHom.snd H G)
  s := (MonoidHom.id H).prodMap P.s
  p := ((MonoidHom.fst H G).comp (Subgroup.subtype _)).prod (P.p.comp ((MonoidHom.snd H G).subgroupComap P.Q))
  s_mem m := P.s_mem m.2
  p_s m := Prod.ext rfl (P.p_s m.2)
  closed_Q := P.closed_Q.preimage continuous_snd
  leviSection_continuous := continuous_id.prodMap P.leviSection_continuous
  cont_p := (continuous_fst.comp continuous_subtype_val).prodMk
    (P.cont_p.comp ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
theorem reparam_L {M' : Type} [Group M'] [TopologicalSpace M'] (e : M' ≃ₜ* M) : (P.reparam e).L = P.L := by
  ext g
  exact ⟨fun ⟨m, h⟩ => ⟨e m, h⟩, fun ⟨m, h⟩ => ⟨e.symm m, (congrArg P.s (e.apply_symm_apply m)).trans h⟩⟩
variable {P} {P' : LeviDatum G M}
theorem IsOpposite.reparam (h : P.IsOpposite P') {M' : Type} [Group M'] [TopologicalSpace M'] (e : M' ≃ₜ* M) :
    (P.reparam e).IsOpposite (P'.reparam e) :=
  ⟨congrArg (·.comp e.toMulEquiv.toMonoidHom) h.1, h.2.trans (P.reparam_L e).symm⟩
end LeviDatum
section Compare
open ValuativeRel
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]
def parDatum (e : (Σ a, m a) ≃ n) : LeviDatum (GL n k) (SmGL.Levi k m) where
  Q := SmGL.parab k e
  s := SmGL.leviEmb k e
  p := SmGL.leviProj k e
  s_mem := SmGL.leviEmb_mem_parab k e
  p_s := SmGL.leviProj_leviEmb k e
  closed_Q := isClosed_blockQ (SmGL.blk e)
  leviSection_continuous := SmGL.continuous_leviEmb k e
  cont_p := continuous_pi fun a => continuous_toHomUnits (SmGL.diagBlock k e a)
    (continuous_matrix fun _ _ => (continuous_entry _ _).comp continuous_subtype_val)
end Compare
section Line
open Formalism.UG
variable {n : ℕ}
def midIdx (i : Fin n) : Fin (n + 2) := i.castSucc.succ
@[simp] theorem midIdx_val (i : Fin n) : (midIdx i).val = i.val + 1 := rfl
theorem lineCases {p : Fin (n + 2) → Prop} (h0 : p 0) (hm : ∀ i, p (midIdx i)) (hl : p (Fin.last (n + 1))) (i) : p i :=
  Fin.cases h0 (fun j => Fin.lastCases hl hm j) i
theorem sum_line {M : Type} [AddCommMonoid M] (f : Fin (n + 2) → M) :
    ∑ i, f i = f 0 + ∑ i, f (midIdx i) + f (Fin.last (n + 1)) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]; exact (add_assoc _ _ _).symm
@[simp] theorem rev_midIdx (i : Fin n) : (midIdx i).rev = midIdx i.rev := by
  ext; have := i.2; simp only [Fin.val_rev, midIdx_val]; omega
@[simp] theorem midIdx_ne_zero (i : Fin n) : midIdx i ≠ 0 := Fin.succ_ne_zero _
@[simp] theorem midIdx_ne_last (i : Fin n) : midIdx i ≠ Fin.last (n + 1) := fun e => by
  have := congrArg Fin.val e; have := i.2; simp only [midIdx_val, Fin.val_last] at *; omega
@[simp] theorem zero_ne_midIdx (i : Fin n) : 0 ≠ midIdx i := (midIdx_ne_zero i).symm
@[simp] theorem last_ne_midIdx (i : Fin n) : Fin.last (n + 1) ≠ midIdx i := (midIdx_ne_last i).symm
@[simp] theorem zero_ne_lastIdx : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := Fin.last_pos.ne
@[simp] theorem midIdx_inj {i j : Fin n} : midIdx i = midIdx j ↔ i = j := by
  simp only [Fin.ext_iff, midIdx_val]; omega
@[simp] theorem lineBlocks_zero : lineBlocks (n + 2) 0 = -1 := by simp [lineBlocks]
@[simp] theorem lineBlocks_mid (i : Fin n) : lineBlocks (n + 2) (midIdx i) = 0 := by
  have := i.2
  rw [lineBlocks, midIdx_val, if_neg (by omega), if_neg (by omega), sub_zero]
@[simp] theorem lineBlocks_last : lineBlocks (n + 2) (Fin.last (n + 1)) = 1 := by simp [lineBlocks]
section Mat
variable {L : Type} [Field L]
def lineMat (a : L) (h : Matrix (Fin n) (Fin n) L) (d : L) : Matrix (Fin (n + 2)) (Fin (n + 2)) L :=
  Matrix.of fun i j => Fin.cases (Fin.cases a (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' =>
    Fin.lastCases (Fin.lastCases d (fun _ => 0) j') (fun i'' => Fin.lastCases 0 (fun j'' => h i'' j'') j') i') j) i
variable (a d : L) (h : Matrix (Fin n) (Fin n) L)
@[simp] theorem lineMat_zero_zero : lineMat a h d 0 0 = a := rfl
@[simp] theorem lineMat_mid_mid (i j : Fin n) : lineMat a h d (midIdx i) (midIdx j) = h i j := by
  simp [lineMat, midIdx]
@[simp] theorem lineMat_last_last : lineMat a h d (Fin.last (n + 1)) (Fin.last (n + 1)) = d := by
  simp [lineMat, ← Fin.succ_last]
@[simp] theorem lineMat_zero_mid (j : Fin n) : lineMat a h d 0 (midIdx j) = 0 := rfl
@[simp] theorem lineMat_zero_last : lineMat a h d 0 (Fin.last (n + 1)) = 0 := rfl
@[simp] theorem lineMat_mid_zero (i : Fin n) : lineMat a h d (midIdx i) 0 = 0 := rfl
@[simp] theorem lineMat_last_zero : lineMat a h d (Fin.last (n + 1)) 0 = 0 := rfl
@[simp] theorem lineMat_mid_last (i : Fin n) : lineMat a h d (midIdx i) (Fin.last (n + 1)) = 0 := by
  simp [lineMat, midIdx, ← Fin.succ_last]
@[simp] theorem lineMat_last_mid (j : Fin n) : lineMat a h d (Fin.last (n + 1)) (midIdx j) = 0 := by
  simp [lineMat, midIdx, ← Fin.succ_last]
theorem lineMat_mul (a' d' : L) (h' : Matrix (Fin n) (Fin n) L) :
    lineMat a h d * lineMat a' h' d' = lineMat (a * a') (h * h') (d * d') := by
  ext i j
  induction i using lineCases <;> induction j using lineCases <;> simp [mul_apply, sum_line]
theorem lineMat_one : lineMat (1 : L) (1 : Matrix (Fin n) (Fin n) L) 1 = 1 := by
  ext i j
  induction i using lineCases <;> induction j using lineCases <;>
    simp [Matrix.one_apply]
def lineEmb (L : Type) [Field L] (n : ℕ) : Lˣ × GL (Fin n) L × Lˣ →* GL (Fin (n + 2)) L :=
  MonoidHom.toHomUnits
    { toFun := fun x => lineMat (x.1 : L) x.2.1.val (x.2.2 : L)
      map_one' := lineMat_one
      map_mul' := fun _ _ => (lineMat_mul _ _ _ _ _ _).symm }
theorem lineEmb_val (x : Lˣ × GL (Fin n) L × Lˣ) : (lineEmb L n x).val = lineMat (x.1 : L) x.2.1.val (x.2.2 : L) := rfl
theorem lineEmb_mem (x : Lˣ × GL (Fin n) L × Lˣ) : lineEmb L n x ∈ blockL L (lineBlocks (n + 2)) := by
  intro i j
  induction i using lineCases <;> induction j using lineCases <;> simp [lineEmb_val]
def lineFirst (L : Type) [Field L] (n : ℕ) : blockL L (lineBlocks (n + 2)) →* Lˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => g.1.val 0 0
      map_one' := by simp
      map_mul' := fun x y => by
        show (x.1.val * y.1.val) 0 0 = _
        simp [mul_apply, sum_line, x.2 0 (midIdx _), x.2 0 (Fin.last (n + 1))] }
def lineMid (L : Type) [Field L] (n : ℕ) : blockL L (lineBlocks (n + 2)) →* GL (Fin n) L :=
  MonoidHom.toHomUnits
    { toFun := fun g => g.1.val.submatrix midIdx midIdx
      map_one' := by ext i j; simp [Matrix.one_apply]
      map_mul' := fun x y => by
        ext i j
        show (x.1.val * y.1.val) (midIdx i) (midIdx j) = _
        simp [mul_apply, sum_line, x.2 (midIdx _) 0, x.2 (midIdx _) (Fin.last (n + 1))] }
variable {σ : L →+* L}
theorem lineEmb_mem_GU [Valued L (WithZero (Multiplicative ℤ))] (hσ : ∀ x, σ (σ x) = x) (u : Lˣ) (h : GU σ n) :
    lineEmb L n (u, h.1, (Units.map σ.toMonoidHom u)⁻¹) ∈ GU σ (n + 2) := by
  rw [mem_GU_iff, ← map_inv]
  have hh := (mem_GU_iff σ n h.1).1 h.2
  intro i j
  induction i using lineCases <;> induction j using lineCases <;> simp [lineEmb_val, hσ, ← hh]
end Mat
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
def lineSec (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (n : ℕ) : Lˣ × GU σ n →* GU σ (n + 2) where
  toFun x := ⟨_, lineEmb_mem_GU hσ x.1 x.2⟩
  map_one' := Subtype.ext (by
    show lineEmb L n _ = 1
    rw [← map_one (lineEmb L n)]; simp [Prod.one_eq_mk])
  map_mul' x y := Subtype.ext (by
    show lineEmb L n _ = lineEmb L n _ * lineEmb L n _
    rw [← map_mul]; simp [mul_comm])
theorem lineSec_val (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (x : Lˣ × GU σ n) :
    (lineSec σ hσ n x).1.val = lineMat (x.1 : L) x.2.1.val (σ x.1)⁻¹ := by
  simp [lineSec, lineEmb_val]
def lineLevi (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ) (n : ℕ) :
    (Lˣ × GU σ n) ≃ₜ* (GU σ (n + 2) ⊓ blockL L (lineBlocks (n + 2)) : Subgroup (GL (Fin (n + 2)) L)) where
  toFun x := ⟨(lineSec σ hσ n x).1, (lineSec σ hσ n x).2, lineEmb_mem _⟩
  invFun g := (lineFirst L n ⟨g.1, g.2.2⟩, ⟨lineMid L n ⟨g.1, g.2.2⟩, by
    rw [mem_GU_iff, ← map_inv]
    intro i j
    have := (mem_GU_iff σ _ g.1).1 g.2.1 (midIdx i) (midIdx j)
    rw [rev_midIdx, rev_midIdx] at this
    exact this⟩)
  left_inv x := Prod.ext (Units.ext rfl) (Subtype.ext (Units.ext (Matrix.ext fun i j =>
    (congrFun (congrFun (lineSec_val σ hσ x) (midIdx i)) (midIdx j)).trans (lineMat_mid_mid _ _ _ i j))))
  right_inv g := by
    refine Subtype.ext (Units.ext ?_)
    refine (lineSec_val σ hσ _).trans (Matrix.ext fun i j => ?_)
    have hl : g.1.val (Fin.last (n + 1)) (Fin.last (n + 1)) = (σ (g.1.val 0 0))⁻¹ := by
      have h1 := (mem_GU_iff σ _ g.1).1 g.2.1 0 0
      have h2 : (g.1⁻¹).val 0 0 = (g.1.val 0 0)⁻¹ :=
        (congrArg Units.val (map_inv (lineFirst L n) (⟨g.1, g.2.2⟩ : blockL L (lineBlocks (n + 2))))).trans
          (Units.val_inv_eq_inv_val _)
      rw [Fin.rev_zero, h2] at h1
      rw [← map_inv₀, h1, hσ]
    induction i using lineCases <;> induction j using lineCases <;>
      first
      | rfl
      | (refine Eq.trans (by simp) (g.2.2 _ _ ?_).symm; simp; done)
      | exact lineMat_mid_mid _ _ _ _ _
      | exact (lineMat_last_last _ _ _).trans hl.symm
  map_mul' x y := Subtype.ext (by simp only [map_mul]; rfl)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_toHomUnits ((Units.coeHom _).comp ((GU σ (n + 2)).subtype.comp (lineSec σ hσ n)))
      (continuous_matrix fun i j => ?_)
    show Continuous fun x => (lineSec σ hσ n x).1.val i j
    simp only [lineSec_val]
    induction i using lineCases <;> induction j using lineCases <;>
      simp only [lineMat_zero_zero, lineMat_mid_mid, lineMat_last_last, lineMat_zero_mid, lineMat_zero_last,
        lineMat_mid_zero, lineMat_last_zero, lineMat_mid_last, lineMat_last_mid, continuous_const]
    · exact Units.continuous_val.comp continuous_fst
    · exact (continuous_entry _ _).comp (continuous_subtype_val.comp continuous_snd)
    · simp only [← map_inv₀, ← Units.val_inv_eq_inv_val]
      exact hc.comp (Units.continuous_coe_inv.comp continuous_fst)
  continuous_invFun := by
    have h0 : Continuous fun g : (GU σ (n + 2) ⊓ blockL L (lineBlocks (n + 2)) : Subgroup (GL (Fin (n + 2)) L)) =>
        (⟨g.1, g.2.2⟩ : blockL L (lineBlocks (n + 2))) := continuous_subtype_val.subtype_mk _
    refine Continuous.prodMk ((continuous_toHomUnits _ ?_).comp h0)
      (((continuous_toHomUnits _ (continuous_matrix fun i j => ?_)).comp h0).subtype_mk _)
    · exact (continuous_entry _ _).comp continuous_subtype_val
    · exact (continuous_entry _ _).comp continuous_subtype_val
variable (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)
def lineParU (n : ℕ) : LeviDatum (GU σ (n + 2)) (Lˣ × GU σ n) :=
  (parU σ (selfDualBlocks_line (n + 2))).reparam (lineLevi σ hσ hc n)
def lineParUOp (n : ℕ) : LeviDatum (GU σ (n + 2)) (Lˣ × GU σ n) :=
  (parUOp σ (selfDualBlocks_line (n + 2))).reparam (lineLevi σ hσ hc n)
@[simp] theorem lineParabolicUnitary_leviSection_eq : (lineParU σ hσ hc n).s = lineSec σ hσ n := rfl
@[simp] theorem lineOppositeParabolicUnitary_leviSection_eq : (lineParUOp σ hσ hc n).s = lineSec σ hσ n := rfl
def borelLineLevi (n : ℕ) : LeviDatum (Lˣ × GU σ n) (Lˣ × torusU σ n) := (borelU σ n).prodLeft Lˣ
omit σ hσ hc
def unrL (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (z : ℂˣ) : Lˣ →* ℂˣ :=
  unrChar (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom z
def consParam (z : ℂˣ) (α : Fin (n / 2) → ℂˣ) : Fin ((n + 2) / 2) → ℂˣ :=
  (Fin.cons z α : Fin (n / 2 + 1) → ℂˣ) ∘ Fin.cast (Nat.add_div_right n two_pos)
def stringParam (q : ℂˣ) (t : ℤ) : Multiset ℂˣ :=
  (Multiset.range t.toNat).map fun i : ℕ => q ^ (2 * (i : ℤ) + 1 - t)
theorem stringParam_of_nonpos (q : ℂˣ) {t : ℤ} (h : t ≤ 0) : stringParam q t = 0 := by
  simp [stringParam, Int.toNat_of_nonpos h]
theorem stringParam_add_two (q : ℂˣ) {t : ℤ} (h : 0 ≤ t) :
    stringParam q (t + 2) = stringParam q t + {q ^ (-(t + 1)), q ^ (t + 1)} := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
  have e : ((m : ℤ) + 2).toNat = (m + 1) + 1 := by omega
  have r : Multiset.range (m + 1) = 0 ::ₘ (Multiset.range m).map (· + 1) := by
    simp only [Multiset.range, List.range_succ_eq_map, Multiset.map_coe, Multiset.cons_coe]
  rw [stringParam, stringParam, e, Multiset.range_succ, r, Int.toNat_natCast]
  simp only [Multiset.map_cons, Multiset.map_map, Function.comp_def, Multiset.insert_eq_cons, ← Multiset.singleton_add,
    Multiset.map_add, Multiset.map_singleton]
  have h1 : 2 * (((m + 1 : ℕ) : ℕ) : ℤ) + 1 - (m + 2) = m + 1 := by push_cast; ring
  have h2 : 2 * ((0 : ℕ) : ℤ) + 1 - (m + 2) = -(m + 1) := by push_cast; ring
  have h3 : ∀ i : ℕ, 2 * ((i + 1 : ℕ) : ℤ) + 1 - (m + 2) = 2 * i + 1 - m := fun i => by push_cast; ring
  simp only [h1, h2, h3]
  abel
example (q : ℂˣ) : stringParam q 1 = {1} := by simp [stringParam]
example (q : ℂˣ) : stringParam q 2 = {q⁻¹, q} := by
  simpa [stringParam_of_nonpos] using stringParam_add_two q le_rfl
variable {ϖ : L} {σ : L →+* L} {q : ℕ}
theorem continuous_of_unramInv (h : IsUnramInv ϖ σ q) : Continuous σ := by
  refine continuous_of_continuousAt_zero σ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero L _).tendsto_iff (Valued.hasBasis_nhds_zero L _)]
  refine fun γ _ => ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  rwa [show Valued.v.restrict (σ x) = Valued.v.restrict x from (Valuation.restrict_inj _).2 (h.2.1 x)]
example [CompleteSpace L] (h : IsUnramInv ϖ σ q) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π₁ : Representation ℂ (GU σ n) V) (z : ℂˣ) :
    haveI := locallyCompact_GU_of_unram h (n + 2)
    IsSmooth ((lineParU σ h.1 (continuous_of_unramInv h) n).nInd (extProd (charRep (unrL L z)) π₁)) :=
  haveI := locallyCompact_GU_of_unram h (n + 2)
  LeviDatum.nInd_isSmooth _ _
end Line
end GlobalTheory.LGrp


