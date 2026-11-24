-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- name    : Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:28.918051+00:00
-- url     : https://prove2.me/theorems/c9c79b47-dd3a-420d-9e27-4610f8a6e897
-- title:
--   Tie Ops
-- statement:
--   Definitions and structural lemmas for Tie Ops, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_add_left
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_smul_left
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_smul_right
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_symm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last


set_option autoImplicit false
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
noncomputable def qlist (S : Finset (Fin r → ℤ)) (c : ℤ) : List ℤ := ((S.image GlW.casI).erase c).toList
end GlX
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlX
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
def act : List (Fin r × Fin r) → V →ₗ[K] V
  | [] => LinearMap.id
  | ab :: w => G.E ab.1 ab.2 ∘ₗ act w
noncomputable def Lv (v : V) : (List (Fin r × Fin r) →₀ K) →ₗ[K] V :=
  Finsupp.linearCombination K (fun w => act G w v)
noncomputable def tr {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h')) :
    LinearMap.range (Lv G h) →ₗ[K] V :=
  (LinearMap.ker (Lv G h)).liftQ (Lv G h') hk ∘ₗ (Lv G h).quotKerEquivRange.symm.toLinearMap
end GlX
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlX
section Proj
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
end Proj
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open MvPolynomial Finset
section Ext
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
def frst (m : σ →₀ ℕ) : σ →₀ ℕ := m.filter fs
def ltr (m : σ →₀ ℕ) : σ →₀ ℕ := m.filter (fun v => ¬ fs v)
def IsF (g : MvPolynomial σ K) : Prop := ∀ m ∈ g.support, ∀ v, m v ≠ 0 → fs v
def IsL (q : MvPolynomial σ K) : Prop := ∀ m ∈ q.support, ∀ v, m v ≠ 0 → ¬ fs v
noncomputable def ext (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials σ K).constr K (fun m => φ (monomial (frst fs m) 1) * monomial (ltr fs m) 1)
noncomputable def slc (m : σ →₀ ℕ) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials σ K).constr K (fun m' => if ltr fs m' = m then monomial (frst fs m') 1 else 0)
end Ext
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
def fsj (N r j0 : ℕ) : Fin N × Fin r → Prop := fun v => (v.1 : ℕ) < j0
instance (N r j0 : ℕ) : DecidablePred (fsj N r j0) := fun v => Nat.decLt _ _
def wlat (N r j0 : ℕ) : Fin N × Fin r → ℤ := fun v => if (v.1 : ℕ) < j0 then 0 else 1
def wfir (N r j0 : ℕ) : Fin N × Fin r → ℤ := fun v => if (v.1 : ℕ) < j0 then 1 else 0
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
def Mup {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (j0 : ℕ) : Fin q → WithTop ℤ :=
  fun k => if J k < j0 then M k else ⊤
noncomputable def Cset (p : ℕ) [Fact p.Prime] [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Pol p r (Lz L j0) ⊓ ⨅ k, YCond p L (J k) (Mup J M j0 k)
noncomputable def psi (p : ℕ) [Fact p.Prime] (L : Letters N) (j0 : ℕ) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  weightedHomogeneousComponent (wL N r) (fun i => ((Lz L j0).deg i : ℤ))
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlX
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def fockB (p : ℕ) [Fact p.Prime] (σ : Type) [Fintype σ] [DecidableEq σ] :
    MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
  LinearMap.mk₂ ℚ_[p] (fun F G => fock p F G)
    (fun F F' G => gammaIntegralityLemmas.fock_add_left F F' G)
    (fun c F G => by rw [gammaIntegralityLemmas.fock_smul_left, smul_eq_mul])
    (fun F G G' => by
      rw [gammaIntegralityLemmas.fock_symm F (G + G'), gammaIntegralityLemmas.fock_add_left, gammaIntegralityLemmas.fock_symm G F, gammaIntegralityLemmas.fock_symm G' F])
    (fun c F G => by rw [gammaIntegralityLemmas.fock_smul_right, smul_eq_mul])
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
section OpsAux
variable {k σ : Type} [Field k]
end OpsAux
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section Comparison₂
variable (L : Letters N) (T : TieData) (hadm : T.Admissible L) (i : Fin T.t)
include hadm
end Comparison₂
section Tie2
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
end Tie2
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
structure IsProjC [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop where
  comm : ∀ c d x, Pi (glAct p L j0 c d x) = glAct p L j0 c d (Pi x)
  wh : ∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν →
    Pi x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν
  pol : ∀ L' : Letters N, L'.vec = L.vec → ∀ x ∈ Pol p r L', Pi x ∈ Pol p r L'
  ycond : ∀ x k, Pi x ∈ YCond p L (J k) (Mup J M j0 k)
  fix : ∀ L' : Letters N, L'.vec = L.vec → ∀ x ∈ Pol p r L', (∀ k, x ∈ YCond p L (J k) (Mup J M j0 k)) → Pi x = x
  int : ∀ x ∈ PolZ p r L, ((p : ℚ_[p]) ^ e) • Pi x ∈ IntPol p (Fin N × Fin r)
  mul : ∀ g q, IsL (fsj N r j0) q → Pi (g * q) = Pi g * q
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section Leib
variable {σ : Type} (A : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
  (hA : ∀ a b, A (a * b) = a * A b + b * A a)
include hA
end Leib
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def FfL (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero N] (L : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r)
    (n : ℕ) : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] where
  toFun := T.Ffull p L i ρ n
  map_add' := by
    intro f g
    simp only [TieData.Ffull, freeze, map_add, mul_add]
  map_smul' := by
    intro c f
    simp only [TieData.Ffull, freeze, map_smul, mul_smul_comm, RingHom.id_apply]
section Comparison₂
variable [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (ρ : Fin r)
  (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i)
include hadm hS
include hρ
omit hρ
omit hadm hS
end Comparison₂
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
structure IsEqC [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop where
  comm : ∀ x ∈ Cset p L j0 J M, ∀ a b, φ (glAct p L j0 a b x) = glAct p L j0 a b (φ x)
  mem : ∀ x ∈ Cset p L j0 J M, φ x ∈ Cset p L j0 J M
noncomputable def inOp (L : Letters N) (j0 : ℕ)
    (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  φ ∘ₗ Pi ∘ₗ psi p L j0
noncomputable def bigOp (L : Letters N) (j0 : ℕ)
    (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  ext (fsj N r j0) (inOp L j0 Pi φ)
section Gen
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
end Gen
section
variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi) (hφ : IsEqC L j0 J M φ)
include hPi
include hφ
end
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def YYs [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (v : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Y p L J M ⊓ Submodule.span ℚ_[p] {x | ∃ g ∈ (GA p L j0).gS {v},
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q}
section
variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi)
  {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
  (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhC : ∀ i, h i ∈ Cset p L j0 J M)
  (hli : LinearIndependent ℚ_[p] h) (hsp : Cset p (r := r) L j0 J M ≤ ⨆ i, (GA p L j0).gS {h i})
include hPi hh hhC hli hsp
end
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames.TO
namespace Formalism.CountingSumsFrames
end Formalism.CountingSumsFrames


