-- Prove2me | Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
-- name    : CerednikDrinfeld_FormalUpperHalfPlaneFunctor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/9c01d24b-1b59-5a10-9426-2c883bae2e67
-- title:
--   Functoriality and GL2​(K)-action on Deligne data
-- statement:
--   Throughout, $\mathcal O$ is a commutative ring, $K$ a field with an $\mathcal O$-algebra structure, $\pi\in\mathcal O$, and $B$ a commutative $\mathcal O$-algebra. A `DeligneDatum` over $B$ assigns to every full lattice $M\subset K^2$ a $B$-submodule `line M` of $B\otimes_{\mathcal O}M$ whose quotient is an invertible $B$-module, monotone under lattice inclusions, equivariant for homotheties $\mathrm{scalarGL}\,c$, and satisfying, for every prime $\mathfrak p\subset B$, the non-degeneracy condition asserting the existence of $M'\subset M$ with $\pi M\subset M'$ and two explicit non-membership statements for elements $1\otimes v$ modulo $\mathrm{line}\oplus\mathfrak p\cdot\top$. Two constructions are made here. First, `DeligneDatum.pullback` sends $g\in GL_2(K)$ and a datum $d$ to the datum whose line at $M$ is the preimage of $d$'s line at $g\cdot M$ under the base-changed isomorphism $B\otimes M\to B\otimes gM$; all five fields are verified, and `isPullback_pullback` records that it satisfies the relation `DeligneDatum.IsPullback`. Second, for an $\mathcal O$-algebra map $f\colon B\to B'$, `DeligneDatum.map` sends $d$ to the datum whose line at $M$ is `lineBaseChange f M (d.line M)`, the $B'$-span of the image of $d.line\,M$ under $f\otimes 1$; `lineBaseChange_eq_ker` identifies this span with the kernel of $B'\otimes_{\mathcal O}M\to B'\otimes_B\bigl((B\otimes_{\mathcal O}M)/N\bigr)$, which yields invertibility of the new quotient, and the non-degeneracy condition is transported using a linear form separating a point from $I\cdot\top$ on a projective module (`exists_linearMap_apply_not_mem`) together with `rTensor_not_mem_lineBaseChange_sup`. These assemble into `Omega K π`, an `AlgFunctor 𝒪` with $B\mapsto$ Deligne data over $B$ and functorial maps as above, with `Omega_obj` identifying its values with `OmegaObj`, and into `Omega.action`, the $GL_2(K)$-action on `Omega K π` given by $g\cdot d=\mathrm{pullback}(g^{-1},d)$, whose unit, multiplicativity and compatibility with base change (`DeligneDatum.map_pullback`) are proved. The remaining declarations are computational lemmas: transport of a datum's line along an equality of underlying lattices, commutation of the base-changed $GL_2$-action with lattice inclusions, with $f\otimes 1$ and with homotheties, and the cocycle identities for $g^{-1}$ needed for the action axioms.
--
--   **Relation to Mathlib.** `AlgFunctor`, `DeligneDatum` and `lineBaseChange` are the project's own notions; the base-change line is here matched with Mathlib's Grassmannian base-change quotient map (`Module.Grassmannian.baseChangeMkQ`) and invertibility is Mathlib's `Module.Invertible`.
--
--   **Where it is used.** The functor `Omega K π` together with its $GL_2(K)$-action is the formal object over which statements of Drinfeld's representability theorem and of the Čerednik–Drinfeld uniformisation of Shimura curves are formulated in this development, on the quaternionic side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open LT.LatticeTree TensorProduct Matrix

namespace CerednikDrinfeld
namespace FormalOmega

section Functoriality

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (B : Type) [CommRing B] [Algebra 𝒪 B]

def transportEquiv {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 = M₂.1) :
    latticeBaseChange 𝒪 K B M₁ ≃ₗ[B] latticeBaseChange 𝒪 K B M₂ :=
  (LinearEquiv.ofEq M₁.1 M₂.1 h).baseChange 𝒪 B _ _

theorem transportEquiv_tmul {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 = M₂.1) (b : B) (v : ↥M₁.1) :
    transportEquiv B h (b ⊗ₜ v) = b ⊗ₜ (LinearEquiv.ofEq M₁.1 M₂.1 h v) := rfl

theorem coe_ofEq_apply {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 = M₂.1) (v : ↥M₁.1) :
    ((LinearEquiv.ofEq M₁.1 M₂.1 h v : ↥M₂.1) : Fin 2 → K) = v := rfl

variable {B} in

theorem DeligneDatum.line_transport (d : DeligneDatum (K := K) π B) {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 = M₂.1) :
    d.line M₂ = (d.line M₁).map (transportEquiv B h).toLinearMap := by
  obtain ⟨L₁, h₁⟩ := M₁
  obtain ⟨L₂, h₂⟩ := M₂
  change L₁ = L₂ at h
  subst h
  have hT : ∀ x : latticeBaseChange 𝒪 K B ⟨L₁, h₁⟩, transportEquiv B (M₁ := ⟨L₁, h₁⟩) (M₂ := ⟨L₁, h₂⟩) rfl x = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact LinearEquiv.map_zero _
    | tmul b v => rfl
    | add x y hx hy => rw [LinearEquiv.map_add, hx, hy]
  ext x
  constructor
  · intro hx; exact ⟨x, hx, hT x⟩
  · rintro ⟨y, hy, rfl⟩
    rw [LinearEquiv.coe_coe, hT y]; exact hy

theorem actBaseChange_inclBaseChange (g : Matrix.GeneralLinearGroup (Fin 2) K) {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1)
    (x : latticeBaseChange 𝒪 K B M') :
    (actBaseChange B g M).toLinearMap (inclBaseChange B h x) =
      inclBaseChange B (latticeMap_mono g h) ((actBaseChange B g M').toLinearMap x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero]
  | add x y hx hy => simp only [LinearMap.map_add, hx, hy]
  | tmul b v =>
    change b ⊗ₜ[𝒪] (latticeMapEquiv g M.1 (Submodule.inclusion h v)) =
      b ⊗ₜ[𝒪] Submodule.inclusion (latticeMap_mono g h) (latticeMapEquiv g M'.1 v)
    congr 1

variable {B} in

theorem rTensor_inclBaseChange {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B') {M' M : FullLattice 𝒪 K}
    (h : M'.1 ≤ M.1) (x : latticeBaseChange 𝒪 K B M') :
    LinearMap.rTensor (↥M.1) f.toLinearMap (inclBaseChange B h x) =
      inclBaseChange B' h (LinearMap.rTensor (↥M'.1) f.toLinearMap x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero]
  | add x y hx hy => simp only [LinearMap.map_add, hx, hy]
  | tmul b v => rfl

variable {B} in

theorem rTensor_actBaseChange {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B') (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (M : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K B M) :
    LinearMap.rTensor (↥(FullLattice.act g M).1) f.toLinearMap (actBaseChange B g M x) =
      actBaseChange B' g M (LinearMap.rTensor (↥M.1) f.toLinearMap x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.map_zero, LinearEquiv.map_zero]
  | add x y hx hy => rw [LinearEquiv.map_add, LinearMap.map_add, LinearMap.map_add, LinearEquiv.map_add, hx, hy]
  | tmul b v => rfl

theorem coe_latticeMapEquiv_apply (g : Matrix.GeneralLinearGroup (Fin 2) K) (L : Submodule 𝒪 (Fin 2 → K)) (v : ↥L) :
    ((latticeMapEquiv g L v : ↥(latticeMap g L)) : Fin 2 → K) = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K) :=
  rfl

theorem actBaseChange_tmul (g : Matrix.GeneralLinearGroup (Fin 2) K) (M : FullLattice 𝒪 K) (b : B) (v : ↥M.1) :
    actBaseChange B g M (b ⊗ₜ v) = b ⊗ₜ latticeMapEquiv g M.1 v := rfl

theorem act_act_scalarGL (g : Matrix.GeneralLinearGroup (Fin 2) K) (c : Kˣ) (M : FullLattice 𝒪 K) :
    (FullLattice.act (scalarGL c) (FullLattice.act g M)).1 = (FullLattice.act g (FullLattice.act (scalarGL c) M)).1 := by
  show latticeMap (scalarGL c) (latticeMap g M.1) = latticeMap g (latticeMap (scalarGL c) M.1)
  rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]

theorem act_act_inv (g : Matrix.GeneralLinearGroup (Fin 2) K) (N : FullLattice 𝒪 K) :
    (FullLattice.act g (FullLattice.act g⁻¹ N)).1 = N.1 :=
  latticeMap_latticeMap_inv g N.1

theorem transport_actBaseChange_scalarGL (g : Matrix.GeneralLinearGroup (Fin 2) K) (c : Kˣ) (M : FullLattice 𝒪 K)
    (x : latticeBaseChange 𝒪 K B M) :
    transportEquiv B (act_act_scalarGL g c M)
        (actBaseChange B (scalarGL c) (FullLattice.act g M) (actBaseChange B g M x)) =
      actBaseChange B g (FullLattice.act (scalarGL c) M) (actBaseChange B (scalarGL c) M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero]
  | add x y hx hy => simp only [LinearEquiv.map_add, hx, hy]
  | tmul b v =>
    have h1 : transportEquiv B (act_act_scalarGL g c M)
        (actBaseChange B (scalarGL c) (FullLattice.act g M) (actBaseChange B g M (b ⊗ₜ[𝒪] v))) =
        b ⊗ₜ[𝒪] (LinearEquiv.ofEq (FullLattice.act (scalarGL c) (FullLattice.act g M)).1
          (FullLattice.act g (FullLattice.act (scalarGL c) M)).1 (act_act_scalarGL g c M)
          (latticeMapEquiv (scalarGL c) (FullLattice.act g M).1 (latticeMapEquiv g M.1 v))) := rfl
    have h2 : actBaseChange B g (FullLattice.act (scalarGL c) M) (actBaseChange B (scalarGL c) M (b ⊗ₜ[𝒪] v)) =
        b ⊗ₜ[𝒪] latticeMapEquiv g (FullLattice.act (scalarGL c) M).1 (latticeMapEquiv (scalarGL c) M.1 v) := rfl
    rw [h1, h2]
    congr 1
    apply Subtype.ext
    rw [LinearEquiv.coe_ofEq_apply, coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply,
      coe_latticeMapEquiv_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      scalarGL_mul_comm]

variable {B} in

theorem DeligneDatum.tmul_mulVec_mem (d : DeligneDatum (K := K) π B) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (N : FullLattice 𝒪 K) (𝔭 : Ideal B) (v : ↥(FullLattice.act g⁻¹ N).1)
    (hv : (1 : B) ⊗ₜ[𝒪] v ∈ (d.line (FullLattice.act g (FullLattice.act g⁻¹ N))).comap
        (actBaseChange B g (FullLattice.act g⁻¹ N)).toLinearMap ⊔
        (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (FullLattice.act g⁻¹ N)))) :
    (1 : B) ⊗ₜ[𝒪] (⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K),
        (act_act_inv g N).le (mulVec_mem_latticeMap v.2)⟩ : ↥N.1) ∈
      d.line N ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B N)) := by
  set Φ := (actBaseChange B g (FullLattice.act g⁻¹ N)).trans (transportEquiv B (act_act_inv g N)) with hΦ
  have key : Φ ((1 : B) ⊗ₜ[𝒪] v) = (1 : B) ⊗ₜ[𝒪] (⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K),
      (act_act_inv g N).le (mulVec_mem_latticeMap v.2)⟩ : ↥N.1) := by
    rw [hΦ]; rfl
  rw [← key]
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
  rw [← hyz, map_add]
  refine Submodule.mem_sup.mpr ⟨Φ y, ?_, Φ z, ?_, rfl⟩
  · rw [DeligneDatum.line_transport π d (act_act_inv g N), hΦ, LinearEquiv.trans_apply]
    exact Submodule.mem_map_of_mem (Submodule.mem_comap.mp hy)
  · refine Submodule.smul_induction_on (p := fun z => Φ z ∈ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B N))) hz
      (fun r hr n _ => ?_) (fun x y hx hy => ?_)
    · show Φ (r • n) ∈ _
      rw [LinearEquiv.map_smul]; exact Submodule.smul_mem_smul hr Submodule.mem_top
    · show Φ (x + y) ∈ _
      rw [LinearEquiv.map_add]; exact Submodule.add_mem _ hx hy

def DeligneDatum.pullback (g : Matrix.GeneralLinearGroup (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum (K := K) π B where
  line M := (d.line (FullLattice.act g M)).comap (actBaseChange B g M).toLinearMap
  invertible M := by
    haveI := d.invertible (FullLattice.act g M)
    exact Module.Invertible.congr
      (Submodule.Quotient.equiv ((d.line (FullLattice.act g M)).comap (actBaseChange B g M).toLinearMap)
        (d.line (FullLattice.act g M)) (actBaseChange B g M)
        (Submodule.map_comap_eq_of_surjective (actBaseChange B g M).surjective _)).symm
  mono h := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap] at hx
    rw [Submodule.mem_comap, actBaseChange_inclBaseChange]
    exact d.mono (latticeMap_mono g h) (Submodule.mem_map_of_mem hx)
  homothety c M := by
    show (d.line (FullLattice.act g (FullLattice.act (scalarGL c) M))).comap
        (actBaseChange B g (FullLattice.act (scalarGL c) M)).toLinearMap =
      ((d.line (FullLattice.act g M)).comap (actBaseChange B g M).toLinearMap).map
        (actBaseChange B (scalarGL c) M).toLinearMap
    rw [DeligneDatum.line_transport π d (act_act_scalarGL g c M), d.homothety c (FullLattice.act g M)]
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hyx⟩
      refine ⟨(actBaseChange B g M).symm y, ?_, ?_⟩
      · rw [LinearEquiv.apply_symm_apply]; exact hy
      · apply (actBaseChange B g (FullLattice.act (scalarGL c) M)).injective
        rw [← transport_actBaseChange_scalarGL, LinearEquiv.apply_symm_apply]
        exact hyx
    · rintro ⟨w, hw, rfl⟩
      exact ⟨_, ⟨actBaseChange B g M w, hw, rfl⟩, transport_actBaseChange_scalarGL B g c M w⟩
  nondeg 𝔭 h𝔭 := by
    obtain ⟨N', N, hN, hπ, h1, h2⟩ := d.nondeg 𝔭 h𝔭
    refine ⟨FullLattice.act g⁻¹ N', FullLattice.act g⁻¹ N, latticeMap_mono g⁻¹ hN, ?_, ?_, ?_⟩
    · intro v
      obtain ⟨w, hw, hwv⟩ := mem_latticeMap.mp v.2
      rw [← hwv, ← Matrix.mulVec_smul]
      exact mulVec_mem_latticeMap (hπ ⟨w, hw⟩)
    · intro v hv hmem
      refine h1 ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K), (act_act_inv g N).le (mulVec_mem_latticeMap v.2)⟩
        ?_ (DeligneDatum.tmul_mulVec_mem π d g N 𝔭 v hmem)
      intro hgv
      apply hv
      have h' := mulVec_mem_latticeMap (g := g⁻¹) hgv
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h'
    · intro v' hv' hmem
      refine h2 ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v' : Fin 2 → K), (act_act_inv g N').le (mulVec_mem_latticeMap v'.2)⟩
        ?_ (DeligneDatum.tmul_mulVec_mem π d g N' 𝔭 v' hmem)
      rintro ⟨w, hw⟩
      apply hv'
      refine ⟨⟨((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (w : Fin 2 → K),
        show ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (w : Fin 2 → K) ∈
          (FullLattice.act g⁻¹ N).1 from mulVec_mem_latticeMap w.2⟩, ?_⟩
      show (v' : Fin 2 → K) = algebraMap 𝒪 K π • (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        *ᵥ (w : Fin 2 → K))
      rw [← Matrix.mulVec_smul, ← hw, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]

theorem DeligneDatum.isPullback_pullback (g : Matrix.GeneralLinearGroup (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) (π := π) B g d (DeligneDatum.pullback π B g d) :=
  fun _ => rfl

section BaseChange

variable {B} {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')

theorem rTensor_one_tmul (M : FullLattice 𝒪 K) (v : ↥M.1) :
    LinearMap.rTensor (↥M.1) f.toLinearMap ((1 : B) ⊗ₜ[𝒪] v) = (1 : B') ⊗ₜ[𝒪] v := by
  rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

theorem rTensor_smul_left {C : Type} [CommRing C] [Algebra 𝒪 C] (g : B' →ₐ[𝒪] C) (M : FullLattice 𝒪 K) (b' : B')
    (y : latticeBaseChange 𝒪 K B' M) :
    LinearMap.rTensor (↥M.1) g.toLinearMap (b' • y) = g b' • LinearMap.rTensor (↥M.1) g.toLinearMap y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul b v =>
    rw [smul_tmul', LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, smul_tmul', AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply, smul_eq_mul, smul_eq_mul, map_mul]

theorem cancelBaseChange_one_tmul [Algebra B B'] [IsScalarTower 𝒪 B B'] (hf : ∀ b, algebraMap B B' b = f b)
    (M : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K B M) :
    AlgebraTensorModule.cancelBaseChange 𝒪 B B' B' (↥M.1) ((1 : B') ⊗ₜ[B] x) =
      LinearMap.rTensor (↥M.1) f.toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  | tmul b v =>
    rw [AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, Algebra.smul_def,
      hf, mul_one]
  | add x y hx hy => rw [tmul_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]

theorem lineBaseChange_eq_ker [Algebra B B'] [IsScalarTower 𝒪 B B'] (hf : ∀ b, algebraMap B B' b = f b)
    (M : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    lineBaseChange f M N = LinearMap.ker (Module.Grassmannian.baseChangeMkQ B' N) := by
  have hker : LinearMap.ker (N.mkQ.baseChange B') = N.baseChange B' := by
    ext x
    have hx : x ∈ LinearMap.ker (LinearMap.lTensor B' N.mkQ) ↔ x ∈ LinearMap.range (LinearMap.lTensor B' N.subtype) := by
      rw [lTensor_mkQ (Q := B')]
    rw [LinearMap.mem_ker, LinearMap.mem_range] at hx
    rw [LinearMap.mem_ker, LinearMap.baseChange_eq_ltensor, hx, Submodule.baseChange, LinearMap.mem_range,
      LinearMap.baseChange_eq_ltensor]
  rw [Module.Grassmannian.baseChangeMkQ, LinearMap.ker_comp, hker, ← Submodule.map_equiv_eq_comap_symm,
    Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image, lineBaseChange]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact (cancelBaseChange_one_tmul f hf M x).symm

theorem invertible_quotient_lineBaseChange (M : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B M))
    (hN : Module.Invertible B (latticeBaseChange 𝒪 K B M ⧸ N)) :
    Module.Invertible B' (latticeBaseChange 𝒪 K B' M ⧸ lineBaseChange f M N) := by
  letI : Algebra B B' := f.toAlgebra
  haveI : IsScalarTower 𝒪 B B' := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  haveI := hN
  exact Module.Invertible.congr
    ((Module.Grassmannian.baseChangeMkQEquiv (B := B') N).symm.trans
      (Submodule.quotEquivOfEq _ _ (lineBaseChange_eq_ker f (fun _ => rfl) M N).symm))

theorem exists_linearMap_apply_not_mem {R : Type} [CommRing R] {Q : Type} [AddCommGroup Q] [Module R Q]
    [Module.Projective R Q] (I : Ideal R) (q : Q) (hq : q ∉ (I • ⊤ : Submodule R Q)) :
    ∃ φ : Q →ₗ[R] R, φ q ∉ I := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hq
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective R Q›
  have hx : q = Finsupp.linearCombination R id (s q) := (congrArg (fun g : Q →ₗ[R] Q => g q) hs).symm
  rw [hx, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem_smul (h ((Finsupp.lapply i).comp s)) Submodule.mem_top

theorem rTensor_not_mem_lineBaseChange_sup (M : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B M))
    (hN : Module.Invertible B (latticeBaseChange 𝒪 K B M ⧸ N)) (𝔭' : Ideal B') [𝔭'.IsPrime]
    (x : latticeBaseChange 𝒪 K B M) (hx : x ∉ N ⊔ (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) :
    LinearMap.rTensor (↥M.1) f.toLinearMap x ∉
      lineBaseChange f M N ⊔ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M)) := by
  letI : Algebra B B' := f.toAlgebra
  haveI : IsScalarTower 𝒪 B B' := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  haveI := hN

  have hq : N.mkQ x ∉ (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M ⧸ N)) := by
    intro hq
    apply hx
    have : x ∈ ((Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)).map N.mkQ).comap N.mkQ := by
      rw [Submodule.mem_comap, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]; exact hq
    rwa [Submodule.comap_map_mkQ] at this

  obtain ⟨φ, hφ⟩ := exists_linearMap_apply_not_mem (Ideal.comap f 𝔭') (N.mkQ x) hq

  let ψ : latticeBaseChange 𝒪 K B' M →ₗ[B'] B' :=
    (AlgebraTensorModule.rid B B' B').toLinearMap ∘ₗ (φ.baseChange B') ∘ₗ Module.Grassmannian.baseChangeMkQ B' N
  have hψx : ψ (LinearMap.rTensor (↥M.1) f.toLinearMap x) = f (φ (N.mkQ x)) := by
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← cancelBaseChange_one_tmul f (fun _ => rfl) M x, Module.Grassmannian.baseChangeMkQ, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul, Submodule.mkQ_apply,
      LinearMap.baseChange_tmul, AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]
    rfl
  have hψN : ∀ y ∈ lineBaseChange f M N, ψ y = 0 := by
    intro y hy
    rw [lineBaseChange_eq_ker f (fun _ => rfl) M N, LinearMap.mem_ker] at hy
    simp only [ψ, LinearMap.comp_apply, hy, map_zero]
  have hψ𝔭 : ∀ y ∈ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M)), ψ y ∈ 𝔭' := by
    intro y hy
    refine Submodule.smul_induction_on (p := fun y => ψ y ∈ 𝔭') hy (fun r hr n _ => ?_) (fun x y hx hy => ?_)
    · show ψ (r • n) ∈ 𝔭'
      rw [LinearMap.map_smul, smul_eq_mul]; exact Ideal.mul_mem_right _ _ hr
    · show ψ (x + y) ∈ 𝔭'
      rw [LinearMap.map_add]; exact Ideal.add_mem _ hx hy
  intro hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  apply hφ
  rw [Ideal.mem_comap, ← hψx, ← hyz, map_add, hψN y hy, zero_add]
  exact hψ𝔭 z hz

def DeligneDatum.map (d : DeligneDatum (K := K) π B) : DeligneDatum (K := K) π B' where
  line M := lineBaseChange f M (d.line M)
  invertible M := invertible_quotient_lineBaseChange f M (d.line M) (d.invertible M)
  mono h := by
    show (lineBaseChange f _ (d.line _)).map (inclBaseChange B' h) ≤ lineBaseChange f _ (d.line _)
    rw [lineBaseChange, lineBaseChange, Submodule.map_span, ← Set.image_comp]
    apply Submodule.span_mono
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨inclBaseChange B h x, d.mono h (Submodule.mem_map_of_mem hx), rTensor_inclBaseChange f h x⟩
  homothety c M := by
    show lineBaseChange f _ (d.line _) = (lineBaseChange f _ (d.line _)).map (actBaseChange B' (scalarGL c) M).toLinearMap
    rw [lineBaseChange, lineBaseChange, Submodule.map_span, ← Set.image_comp, d.homothety c M, Submodule.map_coe,
      ← Set.image_comp]
    congr 1
    apply Set.image_congr
    intro x _
    exact rTensor_actBaseChange f (scalarGL c) M x
  nondeg 𝔭' h𝔭' := by
    haveI := h𝔭'
    obtain ⟨M', M, h, hπ, h1, h2⟩ := d.nondeg (Ideal.comap f 𝔭') (Ideal.IsPrime.comap f)
    refine ⟨M', M, h, hπ, fun v hv => ?_, fun v' hv' => ?_⟩
    · rw [← rTensor_one_tmul f M v]
      exact rTensor_not_mem_lineBaseChange_sup f M (d.line M) (d.invertible M) 𝔭' _ (h1 v hv)
    · rw [← rTensor_one_tmul f M' v']
      exact rTensor_not_mem_lineBaseChange_sup f M' (d.line M') (d.invertible M') 𝔭' _ (h2 v' hv')

theorem DeligneDatum.isBaseChange_map (d : DeligneDatum (K := K) π B) :
    DeligneDatum.IsBaseChange (K := K) (π := π) f d (d.map π f) :=
  fun _ => rfl

end BaseChange

variable (K) in

def Omega : AlgFunctor 𝒪 where
  obj B _ _ := DeligneDatum (K := K) π B
  map f d := DeligneDatum.map π f d
  map_id d := by
    apply DeligneDatum.ext'
    funext M
    show lineBaseChange (AlgHom.id 𝒪 _) M (d.line M) = d.line M
    rw [lineBaseChange, AlgHom.toLinearMap_id, LinearMap.rTensor_id, LinearMap.id_coe, Set.image_id, Submodule.span_eq]
  map_comp f g d := by
    apply DeligneDatum.ext'
    funext M
    show lineBaseChange (g.comp f) M (d.line M) = lineBaseChange g M (lineBaseChange f M (d.line M))
    rw [lineBaseChange, lineBaseChange, lineBaseChange, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp,
      LinearMap.coe_comp, Set.image_comp]
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      induction hy using Submodule.span_induction with
      | mem s hs => exact Submodule.subset_span ⟨s, hs, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul b' a _ ha => rw [rTensor_smul_left]; exact Submodule.smul_mem _ _ ha

theorem Omega_obj (B : Type) [CommRing B] [Algebra 𝒪 B] : (Omega K π).obj B = OmegaObj (K := K) π B := rfl

theorem act_one_inv_val (M : FullLattice 𝒪 K) :
    M.1 = (FullLattice.act (1 : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹ M).1 := by
  show M.1 = latticeMap (1 : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹ M.1
  rw [inv_one, latticeMap_one]

theorem act_inv_act_inv_val (g h : Matrix.GeneralLinearGroup (Fin 2) K) (M : FullLattice 𝒪 K) :
    (FullLattice.act h⁻¹ (FullLattice.act g⁻¹ M)).1 = (FullLattice.act (g * h)⁻¹ M).1 := by
  show latticeMap h⁻¹ (latticeMap g⁻¹ M.1) = latticeMap (g * h)⁻¹ M.1
  rw [← latticeMap_mul, _root_.mul_inv_rev]

theorem actBaseChange_one_inv (M : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K B M) :
    actBaseChange B (1 : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹ M x = transportEquiv B (act_one_inv_val M) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero]
  | add x y hx hy => simp only [LinearEquiv.map_add, hx, hy]
  | tmul b v =>
    rw [actBaseChange_tmul, transportEquiv_tmul]
    congr 1
    apply Subtype.ext
    rw [coe_latticeMapEquiv_apply, LinearEquiv.coe_ofEq_apply, inv_one, Units.val_one, Matrix.one_mulVec]

theorem transport_actBaseChange_inv_inv (g h : Matrix.GeneralLinearGroup (Fin 2) K) (M : FullLattice 𝒪 K)
    (x : latticeBaseChange 𝒪 K B M) :
    transportEquiv B (act_inv_act_inv_val g h M)
        (actBaseChange B h⁻¹ (FullLattice.act g⁻¹ M) (actBaseChange B g⁻¹ M x)) =
      actBaseChange B (g * h)⁻¹ M x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero]
  | add x y hx hy => simp only [LinearEquiv.map_add, hx, hy]
  | tmul b v =>
    have h1 : transportEquiv B (act_inv_act_inv_val g h M)
        (actBaseChange B h⁻¹ (FullLattice.act g⁻¹ M) (actBaseChange B g⁻¹ M (b ⊗ₜ[𝒪] v))) =
        b ⊗ₜ[𝒪] (LinearEquiv.ofEq (FullLattice.act h⁻¹ (FullLattice.act g⁻¹ M)).1 (FullLattice.act (g * h)⁻¹ M).1
          (act_inv_act_inv_val g h M)
          (latticeMapEquiv h⁻¹ (FullLattice.act g⁻¹ M).1 (latticeMapEquiv g⁻¹ M.1 v))) := rfl
    rw [h1, actBaseChange_tmul]
    congr 1
    apply Subtype.ext
    rw [LinearEquiv.coe_ofEq_apply, coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply,
      Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev]

variable {B} in

theorem DeligneDatum.map_pullback {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    (DeligneDatum.pullback π B g d).map π f = DeligneDatum.pullback π B' g (d.map π f) := by
  apply DeligneDatum.ext'
  funext M
  show lineBaseChange f M ((d.line (FullLattice.act g M)).comap (actBaseChange B g M).toLinearMap) =
    (lineBaseChange f (FullLattice.act g M) (d.line (FullLattice.act g M))).comap (actBaseChange B' g M).toLinearMap
  rw [lineBaseChange, lineBaseChange, Submodule.comap_equiv_eq_map_symm, Submodule.comap_equiv_eq_map_symm,
    Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun y _ => ?_
  apply (actBaseChange B' g M).injective
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, ← rTensor_actBaseChange,
    LinearEquiv.apply_symm_apply]

variable (K) in

def Omega.action : AlgFunctor.GroupAction (Matrix.GeneralLinearGroup (Fin 2) K) (Omega K π) where
  act B _ _ g d := DeligneDatum.pullback π B g⁻¹ d
  act_one B _ _ d := by
    apply DeligneDatum.ext'
    funext M
    show (d.line (FullLattice.act (1 : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹ M)).comap
        (actBaseChange B (1 : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹ M).toLinearMap = d.line M
    rw [DeligneDatum.line_transport π d (act_one_inv_val M)]
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [actBaseChange_one_inv] at hyx
      rwa [← (transportEquiv B (act_one_inv_val M)).injective hyx]
    · intro hx
      exact ⟨x, hx, (actBaseChange_one_inv B M x).symm⟩
  act_mul B _ _ g h d := by
    apply DeligneDatum.ext'
    funext M
    show (d.line (FullLattice.act (g * h)⁻¹ M)).comap (actBaseChange B (g * h)⁻¹ M).toLinearMap =
      (((d.line (FullLattice.act h⁻¹ (FullLattice.act g⁻¹ M))).comap
        (actBaseChange B h⁻¹ (FullLattice.act g⁻¹ M)).toLinearMap)).comap (actBaseChange B g⁻¹ M).toLinearMap
    rw [DeligneDatum.line_transport π d (act_inv_act_inv_val g h M)]
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [← transport_actBaseChange_inv_inv] at hyx
      rwa [← (transportEquiv B (act_inv_act_inv_val g h M)).injective hyx]
    · intro hx
      exact ⟨_, hx, transport_actBaseChange_inv_inv B g h M x⟩
  act_map f g d := DeligneDatum.map_pullback π f g⁻¹ d

end Functoriality

end FormalOmega
end CerednikDrinfeld

end


