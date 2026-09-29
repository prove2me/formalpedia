-- Prove2me | Definitions.Def_ModularCurve_KatzLevelPYoneda
-- name    : ModularCurve_KatzLevelPYoneda
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/40b9e286-869d-5407-9b8f-24588eb3df7e
-- title:
--   Yoneda dictionary for Katz level-p forms
-- statement:
--   Throughout, $p$ is a natural number, $S$ a commutative ring and $A$ a commutative $S$-algebra, and $\mathcal T =$ `UnivBasisRing p` is the universal basis ring of level $p$ carrying the universal pair $(\mathrm{univCurveT}\,p,\ \mathrm{univData}\,p)$, with `UnivBasisRing.classify` classifying a Weierstrass curve $W$ over $A$ with $p\Delta_W$ invertible together with level-$p$ data $D$ satisfying `IsLevelPStructure`.
--
--   First, `sClassify` is the $S$-algebra map $S\otimes_{\mathbb Z}\mathcal T\to A$ with $s\otimes t\mapsto s\cdot\mathrm{classify}(W,D)(t)$, built from $\mathrm{IsUnit}(p)$ in $A$, $\mathrm{IsUnit}(\Delta_W)$ and the level-$p$ hypothesis. The accompanying lemmas compute it on tensors, identify its restriction along `univInclude` with $\mathrm{classify}(W,D)$, show that it carries `univCurveOver S p` to $W$ and `univDataOver S p` to $D$, prove that an $S$-algebra map out of $S\otimes_{\mathbb Z}\mathcal T$ is determined by the images of the universal curve and the universal data (hence uniqueness of `sClassify`, its identity case, and compatibility with $A\to A'$), and yield the Yoneda statement `toFun_eq_sClassify_evalUniv`: for a `KatzLevelPForm` $G$ over $S$ of weight $k$, $G(W,D)=\mathrm{sClassify}(W,D)(G.\mathrm{evalUniv})$.
--
--   Second, two $\mathbb Z$-linear "defect" forms on $\mathcal T$ are defined, each from a classifying map of a universal situation: $\mathrm{vcForm}_k(t)=\mathrm{vcClassify}(t)-u^{-k}\,\mathrm{ofUniv}(t)$ in `VCRing p`, for the universally variable-changed curve and data (under the hypothesis that these again form a level-$p$ structure), and $\mathrm{borelForm}(t)=\mathrm{borelClassify}(t)-\mathrm{ofUniv}(t)$ in `BorelRing p a`. Specialising maps `vcTheta`, `borelTheta` and the auxiliary `sLift` convert these into identities over $A$: `vc_eval` expresses $\mathrm{sClassify}(C\cdot W, D\cdot C)(g)-u_C^{-k}\,\mathrm{sClassify}(W,D)(g)$, and `borel_eval` expresses $\mathrm{sClassify}(W,D')(g)-\mathrm{sClassify}(W,D)(g)$ when $x(Q')$ lies on the line of $x(Q)$ (the hypothesis $D'.x_Q\,\Psi_a^2(D.x_Q)=\Phi_a(D.x_Q)$ with $\Psi_a^2$ invertible), as images of $\mathrm{lTensor}_S$ of the respective forms.
--
--   Finally, for $p$ invertible in $S$ and $g\in S\otimes_{\mathbb Z}\mathcal T$ annihilated by $\mathrm{lTensor}_S(\mathrm{vcForm}_k)$, `ofUniv` is the Katz level-$p$ form of weight $k$ sending $(W,D)$ to $\mathrm{sClassify}(W,D)(g)$; `evalUniv_ofUniv` and `ofUniv_evalUniv` show that `ofUniv` and `evalUniv` are mutually inverse between forms of weight $k$ and this kernel, and `dependsOnlyOnSndLine_ofUniv` gives `DependsOnlyOnSndLine` for `ofUniv g` when in addition $\mathrm{lTensor}_S(\mathrm{borelForm})$ kills $g$ for all $1\le a\le (p-1)/2$.
--
--   **Relation to Mathlib.** Katz-style modular forms as functorial rules on Weierstrass data, level-$p$ data and the universal basis ring are the project's own notions; the tensor-product constructions used here (`Algebra.TensorProduct.lift`, `LinearMap.lTensor`) and the Weierstrass curve, division polynomial and variable-change API are Mathlib's.
--
--   **Where it is used.** The results turn the functorial definition of Katz modular forms of level $p$ over $S$ into linear algebra in $S\otimes_{\mathbb Z}\mathcal T$: forms of weight $k$ correspond to elements killed by the weight-$k$ coordinate-change form, and the $\Gamma_0(p)$ condition `DependsOnlyOnSndLine` corresponds to being killed by the Borel forms. This is the algebraic handle used for the modular curves of level $p$ in the project's treatment of modular forms and their level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_KatzLevelPYoneda.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

noncomputable section

open Polynomial WeierstrassCurve
open scoped TensorProduct

namespace ModularCurve

namespace LevelP

section Yoneda

variable (p : ℕ) (S : Type u) [CommRing S] {A : Type u} [CommRing A] [Algebra S A]

def sClassify (hpA : IsUnit (p : A)) (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A)
    (hD : IsLevelPStructure W p D) : S ⊗[ℤ] UnivBasisRing p →ₐ[S] A :=
  Algebra.TensorProduct.lift (Algebra.ofId S A)
    (UnivBasisRing.classify p W (hpA.mul hW) D hD).toIntAlgHom (fun _ _ => Commute.all _ _)

variable (hpA : IsUnit (p : A)) (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A)
  (hD : IsLevelPStructure W p D)

@[simp] theorem sClassify_tmul (s : S) (t : UnivBasisRing p) :
    sClassify p S hpA W hW D hD (s ⊗ₜ t) =
      algebraMap S A s * UnivBasisRing.classify p W (hpA.mul hW) D hD t :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem sClassify_comp_univInclude :
    (sClassify p S hpA W hW D hD : S ⊗[ℤ] UnivBasisRing p →+* A).comp
        (KatzLevelPForm.univInclude S p) =
      UnivBasisRing.classify p W (hpA.mul hW) D hD := by
  ext t
  change sClassify p S hpA W hW D hD ((1 : S) ⊗ₜ t) = _
  rw [sClassify_tmul, map_one, one_mul]

theorem univCurveOver_map_sClassify :
    (KatzLevelPForm.univCurveOver S p).map
        (sClassify p S hpA W hW D hD : S ⊗[ℤ] UnivBasisRing p →+* A) = W := by
  rw [KatzLevelPForm.univCurveOver, WeierstrassCurve.map_map, sClassify_comp_univInclude,
    univCurveT_map_classify]

theorem univDataOver_map_sClassify :
    (KatzLevelPForm.univDataOver S p).map
        (sClassify p S hpA W hW D hD : S ⊗[ℤ] UnivBasisRing p →+* A) = D := by
  rw [KatzLevelPForm.univDataOver, LevelPData.map_map, sClassify_comp_univInclude,
    univData_map_classify]

theorem sAlgHom_ext {φ ψ : S ⊗[ℤ] UnivBasisRing p →ₐ[S] A}
    (hW : (KatzLevelPForm.univCurveOver S p).map (φ : S ⊗[ℤ] UnivBasisRing p →+* A) =
      (KatzLevelPForm.univCurveOver S p).map (ψ : S ⊗[ℤ] UnivBasisRing p →+* A))
    (hD : (KatzLevelPForm.univDataOver S p).map (φ : S ⊗[ℤ] UnivBasisRing p →+* A) =
      (KatzLevelPForm.univDataOver S p).map (ψ : S ⊗[ℤ] UnivBasisRing p →+* A)) : φ = ψ := by
  have h : (φ : S ⊗[ℤ] UnivBasisRing p →+* A).comp (KatzLevelPForm.univInclude S p) =
      (ψ : S ⊗[ℤ] UnivBasisRing p →+* A).comp (KatzLevelPForm.univInclude S p) := by
    refine UnivBasisRing.ringHom_ext p ?_ ?_
    · simpa only [KatzLevelPForm.univCurveOver, WeierstrassCurve.map_map] using hW
    · simpa only [KatzLevelPForm.univDataOver, LevelPData.map_map] using hD
  refine Algebra.TensorProduct.ext' fun s t => ?_
  have hs : s ⊗ₜ[ℤ] t = s • ((1 : S) ⊗ₜ[ℤ] t) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul]
  congr 1
  exact RingHom.congr_fun h t

theorem eq_sClassify {φ : S ⊗[ℤ] UnivBasisRing p →ₐ[S] A}
    (hφW : (KatzLevelPForm.univCurveOver S p).map (φ : S ⊗[ℤ] UnivBasisRing p →+* A) = W)
    (hφD : (KatzLevelPForm.univDataOver S p).map (φ : S ⊗[ℤ] UnivBasisRing p →+* A) = D) :
    φ = sClassify p S hpA W hW D hD :=
  sAlgHom_ext p S (by rw [hφW, univCurveOver_map_sClassify])
    (by rw [hφD, univDataOver_map_sClassify])

theorem sClassify_self (hpS : IsUnit (p : S ⊗[ℤ] UnivBasisRing p)) :
    sClassify p S hpS (KatzLevelPForm.univCurveOver S p) (KatzLevelPForm.isUnit_Δ_univCurveOver S p)
      (KatzLevelPForm.univDataOver S p) (KatzLevelPForm.isLevelPStructure_univDataOver S p) =
      AlgHom.id S _ :=
  (eq_sClassify p S _ _ _ _ _ (by exact WeierstrassCurve.map_id _)
    (by exact LevelPData.map_id _)).symm

theorem comp_sClassify {A' : Type u} [CommRing A'] [Algebra S A'] (f : A →ₐ[S] A')
    (hpA' : IsUnit (p : A')) (hW' : IsUnit (W.map (f : A →+* A')).Δ)
    (hD' : IsLevelPStructure (W.map (f : A →+* A')) p (D.map (f : A →+* A'))) :
    f.comp (sClassify p S hpA W hW D hD) =
      sClassify p S hpA' (W.map (f : A →+* A')) hW' (D.map (f : A →+* A')) hD' :=
  eq_sClassify p S _ _ _ _ _
    (by rw [AlgHom.comp_toRingHom, ← WeierstrassCurve.map_map, univCurveOver_map_sClassify])
    (by rw [AlgHom.comp_toRingHom, ← LevelPData.map_map, univDataOver_map_sClassify])

end Yoneda

end LevelP

namespace KatzLevelPForm

open LevelP

variable {p : ℕ} {S : Type u} [CommRing S] {k : ℤ}

theorem toFun_congr (G : KatzLevelPForm S p k) {A : Type u} [CommRing A] [Algebra S A]
    {W W' : WeierstrassCurve A} (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ) {D D' : LevelPData A}
    (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure W' p D') (e : W = W') (e' : D = D') :
    G.toFun W hW D hD = G.toFun W' hW' D' hD' := by
  subst e e'
  rfl

theorem map_toFun' (G : KatzLevelPForm S p k) {A B : Type u} [CommRing A] [Algebra S A]
    [CommRing B] [Algebra S B] (f : A →ₐ[S] B) (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D : LevelPData A) (hD : IsLevelPStructure W p D) :
    f (G.toFun W hW D hD) = G.toFun (W.map (f : A →+* B)) (KatzModularForm.isUnit_Δ_map _ hW)
      (D.map (f : A →+* B)) (hD.map _) :=
  (G.map_toFun f W hW _ D hD _).symm

theorem toFun_eq_sClassify_evalUniv (G : KatzLevelPForm S p k) {A : Type u} [CommRing A]
    [Algebra S A] (hpA : IsUnit (p : A)) (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D : LevelPData A) (hD : IsLevelPStructure W p D) :
    G.toFun W hW D hD = sClassify p S hpA W hW D hD G.evalUniv := by
  rw [KatzLevelPForm.evalUniv, map_toFun' G (sClassify p S hpA W hW D hD)]
  exact (toFun_congr G _ _ _ _ (univCurveOver_map_sClassify p S hpA W hW D hD)
    (univDataOver_map_sClassify p S hpA W hW D hD)).symm

end KatzLevelPForm

namespace LevelP

section Forms

variable (p : ℕ)

theorem isUnit_pΔ_vcCurve' : IsUnit ((p : VCRing p) * (univVC p • vcCurve p).Δ) := by
  refine (isUnit_natCast_vcRing p).mul ?_
  rw [variableChange_Δ]
  exact ((Units.isUnit _).pow 12).mul (isUnit_Δ_vcCurve p)

variable (hV : IsLevelPStructure (univVC p • vcCurve p) p ((vcData p).variableChange (univVC p)))

def vcClassify : UnivBasisRing p →+* VCRing p :=
  UnivBasisRing.classify p (univVC p • vcCurve p) (isUnit_pΔ_vcCurve' p) _ hV

theorem univCurveT_map_vcClassify : (univCurveT p).map (vcClassify p hV) = univVC p • vcCurve p :=
  univCurveT_map_classify p _ _ _ _

theorem univData_map_vcClassify :
    (univData p).map (vcClassify p hV) = (vcData p).variableChange (univVC p) :=
  univData_map_classify p _ _ _ _

def vcForm (k : ℤ) : UnivBasisRing p →ₗ[ℤ] VCRing p where
  toFun t := vcClassify p hV t - (((univVC p).u⁻¹ ^ k : (VCRing p)ˣ) : VCRing p) * VCRing.ofUniv p t
  map_add' x y := by simp only [map_add]; ring
  map_smul' n x := by
    simp only [zsmul_eq_mul, eq_intCast, Int.cast_id, map_mul, map_intCast]; ring

theorem vcForm_apply (k : ℤ) (t : UnivBasisRing p) :
    vcForm p hV k t =
      vcClassify p hV t - (((univVC p).u⁻¹ ^ k : (VCRing p)ˣ) : VCRing p) * VCRing.ofUniv p t :=
  rfl

theorem isUnit_pΔ_borelCurve (a : ℕ) : IsUnit ((p : BorelRing p a) * (borelCurve p a).Δ) :=
  (isUnit_natCast_borelRing p a).mul (isUnit_Δ_borelCurve p a)

variable {a : ℕ} (hB : IsLevelPStructure (borelCurve p a) p (borelData' p a))

def borelClassify : UnivBasisRing p →+* BorelRing p a :=
  UnivBasisRing.classify p (borelCurve p a) (isUnit_pΔ_borelCurve p a) (borelData' p a) hB

theorem univCurveT_map_borelClassify :
    (univCurveT p).map (borelClassify p hB) = borelCurve p a :=
  univCurveT_map_classify p _ _ _ _

theorem univData_map_borelClassify : (univData p).map (borelClassify p hB) = borelData' p a :=
  univData_map_classify p _ _ _ _

def borelForm : UnivBasisRing p →ₗ[ℤ] BorelRing p a where
  toFun t := borelClassify p hB t - BorelRing.ofUniv p a t
  map_add' x y := by simp only [map_add]; ring
  map_smul' n x := by
    simp only [zsmul_eq_mul, eq_intCast, Int.cast_id, map_mul, map_intCast]; ring

theorem borelForm_apply (t : UnivBasisRing p) :
    borelForm p hB t = borelClassify p hB t - BorelRing.ofUniv p a t := rfl

end Forms

section Targets

variable (p : ℕ) (S : Type u) [CommRing S] {A : Type u} [CommRing A] [Algebra S A]
  (hpA : IsUnit (p : A))

def sLift {N : Type} [CommRing N] (θ : N →+* A) : S ⊗[ℤ] N →ₐ[S] A :=
  Algebra.TensorProduct.lift (Algebra.ofId S A) θ.toIntAlgHom (fun _ _ => Commute.all _ _)

@[simp] theorem sLift_tmul {N : Type} [CommRing N] (θ : N →+* A) (s : S) (n : N) :
    sLift S θ (s ⊗ₜ n) = algebraMap S A s * θ n :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem sLift_lTensor {N : Type} [CommRing N] (β ι : UnivBasisRing p →+* N) (c : N)
    (form : UnivBasisRing p →ₗ[ℤ] N) (hform : ∀ t, form t = β t - c * ι t) (θ : N →+* A)
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A) (hD : IsLevelPStructure W p D)
    (W' : WeierstrassCurve A) (hW' : IsUnit W'.Δ) (D' : LevelPData A)
    (hD' : IsLevelPStructure W' p D')
    (hι : θ.comp ι = UnivBasisRing.classify p W (hpA.mul hW) D hD)
    (hβ : θ.comp β = UnivBasisRing.classify p W' (hpA.mul hW') D' hD')
    (g : S ⊗[ℤ] UnivBasisRing p) :
    sLift S θ (LinearMap.lTensor S form g) =
      sClassify p S hpA W' hW' D' hD' g - θ c * sClassify p S hpA W hW D hD g := by
  induction g using TensorProduct.induction_on with
  | zero => simp
  | tmul s t =>
    rw [LinearMap.lTensor_tmul, sLift_tmul, hform, sClassify_tmul, sClassify_tmul, ← hι, ← hβ,
      RingHom.comp_apply, RingHom.comp_apply, map_sub, map_mul]
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]; ring

section VCTarget

variable (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A)
  (hD : IsLevelPStructure W p D) (C : VariableChange A)

def vcTheta : VCRing p →+* A := VCRing.lift p (UnivBasisRing.classify p W (hpA.mul hW) D hD) C

theorem vcTheta_comp_ofUniv : (vcTheta p hpA W hW D hD C).comp (VCRing.ofUniv p) =
    UnivBasisRing.classify p W (hpA.mul hW) D hD :=
  VCRing.lift_comp_ofUniv p _ C

theorem univVC_map_vcTheta : (univVC p).map (vcTheta p hpA W hW D hD C) = C :=
  univVC_map_lift p _ C

theorem vcTheta_units (k : ℤ) :
    vcTheta p hpA W hW D hD C (((univVC p).u⁻¹ ^ k : (VCRing p)ˣ) : VCRing p) =
      ((C.u⁻¹ ^ k : Aˣ) : A) := by
  have hu : Units.map (vcTheta p hpA W hW D hD C : VCRing p →* A) (univVC p).u = C.u :=
    congrArg VariableChange.u (univVC_map_vcTheta p hpA W hW D hD C)
  change (vcTheta p hpA W hW D hD C : VCRing p →* A)
    (((univVC p).u⁻¹ ^ k : (VCRing p)ˣ) : VCRing p) = _
  rw [← Units.coe_map, map_zpow, map_inv, hu]

variable (hV : IsLevelPStructure (univVC p • vcCurve p) p ((vcData p).variableChange (univVC p)))
  (hW' : IsUnit (C • W).Δ) (hD' : IsLevelPStructure (C • W) p (D.variableChange C))

theorem vcTheta_comp_vcClassify : (vcTheta p hpA W hW D hD C).comp (vcClassify p hV) =
    UnivBasisRing.classify p (C • W) (hpA.mul hW') (D.variableChange C) hD' := by
  have hDmap : ∀ {T T' : Type _} [CommRing T] [CommRing T'] (φ : T →+* T') (C₀ : VariableChange T)
      (D₀ : LevelPData T),
      (D₀.variableChange C₀).map φ = (D₀.map φ).variableChange (C₀.map φ) := by
    intro T T' _ _ φ C₀ D₀
    have hu : φ ((C₀.u⁻¹ : Tˣ) : T) = (((C₀.map φ).u⁻¹ : T'ˣ) : T') :=
      (Units.coe_map_inv (φ : T →* T') C₀.u).symm
    refine LevelPData.ext ?_ ?_ ?_ ?_ <;>
      simp only [LevelPData.map_xP, LevelPData.map_yP, LevelPData.map_xQ, LevelPData.map_yQ,
        LevelPData.variableChange_xP, LevelPData.variableChange_yP,
        LevelPData.variableChange_xQ, LevelPData.variableChange_yQ, map_mul, map_sub, map_pow,
        hu, VariableChange.map]
  refine UnivBasisRing.eq_classify p _ _ _ _ ?_ ?_
  · rw [← WeierstrassCurve.map_map, univCurveT_map_vcClassify,
      ← WeierstrassCurve.map_variableChange, univVC_map_vcTheta, vcCurve, WeierstrassCurve.map_map,
      vcTheta_comp_ofUniv, univCurveT_map_classify]
  · rw [← LevelPData.map_map, univData_map_vcClassify, hDmap, univVC_map_vcTheta, vcData,
      LevelPData.map_map, vcTheta_comp_ofUniv, univData_map_classify]

theorem vc_eval (k : ℤ) (g : S ⊗[ℤ] UnivBasisRing p) :
    sClassify p S hpA (C • W) hW' (D.variableChange C) hD' g -
        ((C.u⁻¹ ^ k : Aˣ) : A) * sClassify p S hpA W hW D hD g =
      sLift S (vcTheta p hpA W hW D hD C) (LinearMap.lTensor S (vcForm p hV k) g) := by
  rw [sLift_lTensor p S hpA (vcClassify p hV) (VCRing.ofUniv p) _ (vcForm p hV k)
    (vcForm_apply p hV k) (vcTheta p hpA W hW D hD C) W hW D hD (C • W) hW' _ hD'
    (vcTheta_comp_ofUniv p hpA W hW D hD C)
    (vcTheta_comp_vcClassify p hpA W hW D hD C hV hW' hD') g, vcTheta_units]

end VCTarget

section BorelTarget

variable (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D D' : LevelPData A)
  (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure W p D') {a : ℕ}
  (hu : IsUnit (((univCurveT p).ΨSq a).eval (univData p).xQ))
  (heq : D'.xQ * (W.ΨSq a).eval D.xQ = (W.Φ a).eval D.xQ)

include hu heq in

theorem xQ_eq_classify_borelX :
    D'.xQ = UnivBasisRing.classify p W (hpA.mul hW) D hD (borelX p a) := by
  set φ := UnivBasisRing.classify p W (hpA.mul hW) D hD with hφ
  obtain ⟨v, hv⟩ := hu
  have hWφ : (univCurveT p).map φ = W := univCurveT_map_classify p _ _ _ _
  have hxQ : φ (univData p).xQ = D.xQ :=
    congrArg LevelPData.xQ (univData_map_classify p W (hpA.mul hW) D hD)
  have hΨ : φ (((univCurveT p).ΨSq a).eval (univData p).xQ) = (W.ΨSq a).eval D.xQ := by
    rw [← hxQ, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← WeierstrassCurve.map_ΨSq, hWφ]
  have hΦ : φ (((univCurveT p).Φ a).eval (univData p).xQ) = (W.Φ a).eval D.xQ := by
    rw [← hxQ, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← WeierstrassCurve.map_Φ, hWφ]
  rw [borelX, map_mul, hΦ, ← hv, Ring.inverse_unit]
  set vA : Aˣ := Units.map (φ : UnivBasisRing p →* A) v with hvA
  have hinv : φ ((v⁻¹ : (UnivBasisRing p)ˣ) : UnivBasisRing p) = ((vA⁻¹ : Aˣ) : A) :=
    (Units.coe_map_inv (φ : UnivBasisRing p →* A) v).symm
  have hvA' : (vA : A) = (W.ΨSq a).eval D.xQ := by
    rw [hvA, Units.coe_map, MonoidHom.coe_coe, hv, hΨ]
  have heq' : D'.xQ * (vA : A) = (W.Φ a).eval D.xQ := by rw [hvA']; exact heq
  rw [hinv, ← heq', Units.mul_inv_cancel_right]

include hD' in
theorem isLevelPStructure_map_classify' :
    IsLevelPStructure ((univCurveT p).map (UnivBasisRing.classify p W (hpA.mul hW) D hD)) p D' := by
  rwa [univCurveT_map_classify]

def borelTheta : BorelRing p a →+* A :=
  BorelRing.lift p a (UnivBasisRing.classify p W (hpA.mul hW) D hD) D'
    (isLevelPStructure_map_classify' p hpA W hW D D' hD hD')
    (xQ_eq_classify_borelX p hpA W hW D D' hD hu heq)

theorem borelTheta_comp_ofUniv :
    (borelTheta p hpA W hW D D' hD hD' hu heq).comp (BorelRing.ofUniv p a) =
      UnivBasisRing.classify p W (hpA.mul hW) D hD :=
  BorelRing.lift_comp_ofUniv p a _ _ _ _

variable (hB : IsLevelPStructure (borelCurve p a) p (borelData' p a))

theorem borelTheta_comp_borelClassify :
    (borelTheta p hpA W hW D D' hD hD' hu heq).comp (borelClassify p hB) =
      UnivBasisRing.classify p W (hpA.mul hW) D' hD' := by
  refine UnivBasisRing.eq_classify p _ _ _ _ ?_ ?_
  · rw [← WeierstrassCurve.map_map, univCurveT_map_borelClassify, borelTheta, borelCurve_map_lift,
      univCurveT_map_classify]
  · rw [← LevelPData.map_map, univData_map_borelClassify, borelTheta, borelData'_map_lift]

theorem borel_eval (g : S ⊗[ℤ] UnivBasisRing p) :
    sClassify p S hpA W hW D' hD' g - sClassify p S hpA W hW D hD g =
      sLift S (borelTheta p hpA W hW D D' hD hD' hu heq)
        (LinearMap.lTensor S (borelForm p hB) g) := by
  rw [sLift_lTensor p S hpA (borelClassify p hB) (BorelRing.ofUniv p a) 1 (borelForm p hB)
    (fun t => by rw [borelForm_apply, one_mul]) _ W hW D hD W hW D' hD'
    (borelTheta_comp_ofUniv p hpA W hW D D' hD hD' hu heq)
    (borelTheta_comp_borelClassify p hpA W hW D D' hD hD' hu heq hB) g, map_one, one_mul]

end BorelTarget

end Targets

end LevelP

namespace KatzLevelPForm

open LevelP

variable (p : ℕ) (S : Type u) [CommRing S] (hpS : IsUnit (p : S)) (k : ℤ)

include hpS in
theorem isUnit_natCast_algebra (A : Type u) [CommRing A] [Algebra S A] : IsUnit (p : A) := by
  simpa only [map_natCast] using hpS.map (algebraMap S A)

variable (hV : IsLevelPStructure (univVC p • vcCurve p) p ((vcData p).variableChange (univVC p)))
  (g : S ⊗[ℤ] UnivBasisRing p) (hg : LinearMap.lTensor S (vcForm p hV k) g = 0)

def ofUniv : KatzLevelPForm S p k where
  toFun A _ _ W hW D hD := sClassify p S (isUnit_natCast_algebra p S hpS A) W hW D hD g
  map_toFun A B _ _ _ _ f W hW hW' D hD hD' := by
    rw [← AlgHom.comp_apply,
      comp_sClassify p S _ W hW D hD f (isUnit_natCast_algebra p S hpS B) hW' hD']
  toFun_variableChange A _ _ C W hW hW' D hD hD' := by
    have h := vc_eval p S (isUnit_natCast_algebra p S hpS A) W hW D hD C hV hW' hD' k g
    rw [hg, map_zero, sub_eq_zero] at h
    exact h

theorem ofUniv_toFun {A : Type u} [CommRing A] [Algebra S A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) (D : LevelPData A) (hD : IsLevelPStructure W p D) :
    (ofUniv p S hpS k hV g hg).toFun W hW D hD =
      sClassify p S (isUnit_natCast_algebra p S hpS A) W hW D hD g :=
  rfl

theorem evalUniv_ofUniv : (ofUniv p S hpS k hV g hg).evalUniv = g := by
  rw [KatzLevelPForm.evalUniv, ofUniv_toFun, sClassify_self]
  rfl

variable {p S k} in
include hpS in

theorem ofUniv_evalUniv (F : KatzLevelPForm S p k)
    (hF : LinearMap.lTensor S (vcForm p hV k) F.evalUniv = 0) :
    ofUniv p S hpS k hV F.evalUniv hF = F :=
  KatzLevelPForm.ext fun A _ _ W hW D hD => by
    rw [ofUniv_toFun, ← toFun_eq_sClassify_evalUniv]

theorem dependsOnlyOnSndLine_ofUniv
    (hB : ∀ (a : ℕ), 1 ≤ a → a ≤ (p - 1) / 2 → IsLevelPStructure (borelCurve p a) p (borelData' p a))
    (hu : ∀ (a : ℕ), 1 ≤ a → a ≤ (p - 1) / 2 →
      IsUnit (((univCurveT p).ΨSq a).eval (univData p).xQ))
    (hb : ∀ (a : ℕ) (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2),
      LinearMap.lTensor S (borelForm p (hB a ha ha')) g = 0) :
    (ofUniv p S hpS k hV g hg).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hin
  obtain ⟨a, ha, ha', heq⟩ := hin
  have h := borel_eval p S (isUnit_natCast_algebra p S hpS A) W hW D D' hD hD' (hu a ha ha') heq
    (hB a ha ha') g
  rw [hb a ha ha', map_zero, sub_eq_zero] at h
  exact h

end KatzLevelPForm

end ModularCurve

end


