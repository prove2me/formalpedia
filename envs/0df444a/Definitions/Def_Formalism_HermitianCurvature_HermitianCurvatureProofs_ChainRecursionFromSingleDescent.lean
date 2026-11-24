-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T16:15:44.298024+00:00
-- url     : https://prove2.me/theorems/708ad630-a6bf-42fc-9d97-70d1e72f43de
-- title:
--   Chain Recursion From Single Descent
-- statement:
--   Definitions and structural lemmas for Chain Recursion From Single Descent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_glev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_glev_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_congr_on
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_uw_glev
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_one
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.Qx6
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
def ext0 {m : ℕ} (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, τ)
def phi0 (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (Fin.cycleRange p.1).symm * ext0 p.2
end
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
section lists
variable {n : ℕ}
@[simp] theorem bE_zero {m : ℕ} (e : Fin n) (v : Fin m → Fin n) : bE e v 0 = e := rfl
@[simp] theorem bE_succ {m : ℕ} (e : Fin n) (v : Fin m → Fin n) (j : Fin m) : bE e v j.succ = v j := rfl
@[simp] theorem bS_last {m : ℕ} (e : Fin n) (v : Fin m → Fin n) : bS v e (Fin.last m) = e := by
  simp [bS]
@[simp] theorem bS_castSucc {m : ℕ} (e : Fin n) (v : Fin m → Fin n) (j : Fin m) : bS v e j.castSucc = v j := by
  simp [bS]
end lists
end
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
section exp
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
end exp
end
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
section full
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
end full
end
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
end
section
structure HatData (X : Type*) [AddCommGroup X] [Module ℂ X] where
  G : Submodule ℂ X
  N : X →ₗ[ℂ] X
  N_mem : ∀ x ∈ G, N x ∈ G
  N_idem : ∀ x, N (N x) = N x
namespace HatData
variable {X : Type*} [AddCommGroup X] [Module ℂ X] (H : HatData X)
def V : Submodule ℂ X where
  carrier := {x | x ∈ H.G ∧ H.N x = x}
  zero_mem' := ⟨H.G.zero_mem, map_zero _⟩
  add_mem' := fun ha hb => ⟨H.G.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2]⟩
  smul_mem' := fun s _ ha => ⟨H.G.smul_mem s ha.1, by rw [map_smul, ha.2]⟩
structure Good (T : X → X) : Prop where
  mem : ∀ x ∈ H.G, T x ∈ H.G
  congr : ∀ x ∈ H.G, ∀ y ∈ H.G, H.N x = H.N y → H.N (T x) = H.N (T y)
  lin : ∀ x ∈ H.G, ∀ y ∈ H.G, ∀ s : ℂ, H.N (T (x + s • y)) = H.N (T x) + s • H.N (T y)
def toV (x : X) (hx : x ∈ H.G) : H.V := ⟨H.N x, H.N_mem x hx, H.N_idem x⟩
variable {H}
theorem Good.map_zero {T : X → X} (h : H.Good T) : H.N (T 0) = 0 := by
  have h1 := h.lin 0 H.G.zero_mem 0 H.G.zero_mem 1
  rw [smul_zero, add_zero, one_smul] at h1
  have h2 := congrArg (fun v => v - H.N (T 0)) h1
  simp only [sub_self, add_sub_cancel_right] at h2
  exact h2.symm
theorem Good.map_smul {T : X → X} (h : H.Good T) {x : X} (hx : x ∈ H.G) (s : ℂ) :
    H.N (T (s • x)) = s • H.N (T x) := by
  have h1 := h.lin 0 H.G.zero_mem x hx s
  rw [zero_add, h.map_zero, zero_add] at h1
  exact h1
theorem Good.map_add {T : X → X} (h : H.Good T) {x y : X} (hx : x ∈ H.G) (hy : y ∈ H.G) :
    H.N (T (x + y)) = H.N (T x) + H.N (T y) := by
  simpa only [one_smul] using h.lin x hx y hy 1
variable (H)
open Classical in

def hat (T : X → X) : Module.End ℂ H.V :=
  if h : H.Good T then
    { toFun := fun x => H.toV (T x) (h.mem _ x.2.1)
      map_add' := fun x y => Subtype.ext (h.map_add x.2.1 y.2.1)
      map_smul' := fun s x => Subtype.ext (h.map_smul x.2.1 s) }
  else 0
variable {H}
theorem Good.add {T S : X → X} (hT : H.Good T) (hS : H.Good S) : H.Good (fun x => T x + S x) where
  mem := fun x hx => H.G.add_mem (hT.mem x hx) (hS.mem x hx)
  congr := fun x hx y hy h => by
    rw [_root_.map_add, _root_.map_add, hT.congr x hx y hy h, hS.congr x hx y hy h]
  lin := fun x hx y hy s => by
    rw [_root_.map_add, _root_.map_add, _root_.map_add, hT.lin x hx y hy s, hS.lin x hx y hy s, smul_add]
    abel
theorem Good.smul {T : X → X} (hT : H.Good T) (a : ℂ) : H.Good (fun x => a • T x) where
  mem := fun x hx => H.G.smul_mem a (hT.mem x hx)
  congr := fun x hx y hy h => by
    rw [_root_.map_smul, _root_.map_smul, hT.congr x hx y hy h]
  lin := fun x hx y hy s => by
    rw [_root_.map_smul, _root_.map_smul, _root_.map_smul, hT.lin x hx y hy s, smul_add, smul_comm]
theorem Good.neg {T : X → X} (hT : H.Good T) : H.Good (fun x => -T x) := by
  have e : (fun x => -T x) = fun x => (-1 : ℂ) • T x := by
    funext x
    simp
  rw [e]
  exact hT.smul (-1)
theorem Good.sub {T S : X → X} (hT : H.Good T) (hS : H.Good S) : H.Good (fun x => T x - S x) := by
  have e : (fun x => T x - S x) = fun x => T x + -S x := by
    funext x
    exact sub_eq_add_neg _ _
  rw [e]
  exact hT.add hS.neg
end HatData
end
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
abbrev XX (k r : ℕ) := (Fin r → ℂ) × Mx k r
def gam (k r : ℕ) (i : Fin (r + 1)) (c : Fin r → ℂ) : ℝ :=
  ∏ a : Fin r, (if a.val < i.val then ‖c a‖ ^ (Mdim k r a - 1) else 1)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def Res (k r : ℕ) (l : Fin r) (Ψ : Fn k r E) : Fn k r E :=
  fun c g => ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • Ψ c (w1 k r l (c l) * g)
end
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
def mL (k r : ℕ) (l : Fin r) (x : XX k r) : XX k r := (x.1, w1 k r l (x.1 l) * x.2)
def UU (Dc : (Fin r → ℂ) → Set (Mx k r)) : Set (XX k r) := {x | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1}
def stepD (l : Fin r) (Dc : (Fin r → ℂ) → Set (Mx k r)) : (Fin r → ℂ) → Set (Mx k r) :=
  fun c => {g | w1 k r l (c l) * g ∈ Dc c}
def Dcell (D : Set (Mx k r)) (i : Fin (r + 1)) : (Fin r → ℂ) → Set (Mx k r) :=
  fun c => {g | wCell k r i c * g ∈ D}
section Fam
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Fam
section FF
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
theorem ff_zero (i : Fin (r + 1)) (D : Set (Mx k r)) :
    (fun _ => 0 : Mx k r → (Wq →L[ℂ] Wp)) ∈ FFl k r z z' π π' i D := by
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
  · intro g _ n _
    simp
  · intro g _ n _
    simp
  · intro g _ h _ h' _
    simp
end FF
end
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
section Dir
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Dir
end
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
structure LinRel {X : Type*} [AddCommGroup X] [Module ℂ X] (R : X → X → Prop) : Prop where
  zero : R 0 0
  add : ∀ {a b a' b'}, R a b → R a' b' → R (a + a') (b + b')
  smul : ∀ (s : ℂ) {a b}, R a b → R (s • a) (s • b)
theorem LinRel.neg {X : Type*} [AddCommGroup X] [Module ℂ X] {R : X → X → Prop} (h : LinRel R) {a b : X}
    (hab : R a b) : R (-a) (-b) := by
  simpa using h.smul (-1) hab
theorem LinRel.sub {X : Type*} [AddCommGroup X] [Module ℂ X] {R : X → X → Prop} (h : LinRel R) {a b a' b' : X}
    (hab : R a b) (hab' : R a' b') : R (a - a') (b - b') := by
  simpa [sub_eq_add_neg] using h.add hab (h.neg hab')
def Pres2 {X : Type*} (R : X → X → Prop) (T T' : X → X) : Prop := ∀ a b, R a b → R (T a) (T' b)
section OM
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end OM
section FF
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
theorem ff_add {i : Fin (r + 1)} {D : Set (Mx k r)} {J J' : Mx k r → (Wq →L[ℂ] Wp)}
    (h : J ∈ FFl k r z z' π π' i D) (h' : J' ∈ FFl k r z z' π π' i D) : J + J' ∈ FFl k r z z' π π' i D := by
  obtain ⟨hs, hl, hr, he⟩ := h
  obtain ⟨hs', hl', hr', he'⟩ := h'
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hs g₀ hg₀
    obtain ⟨U', F', hU', hgU', hF', hFe'⟩ := hs' g₀ hg₀
    refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', Set.mem_inter hgU hgU',
      (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hgl => ?_⟩
    show J g + J' g = F g + F' g
    rw [hFe g hg.1 hgl, hFe' g hg.2 hgl]
  · intro g hg n hn
    simp only [Pi.add_apply]
    rw [hl g hg n hn, hl' g hg n hn, smul_add]
  · intro g hg n hn
    simp only [Pi.add_apply]
    rw [hr g hg n hn, hr' g hg n hn, smul_add]
  · intro g hg x hx x' hx'
    simp only [Pi.add_apply]
    rw [he g hg x hx x' hx', he' g hg x hx x' hx', ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
theorem ff_smul {i : Fin (r + 1)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} (s : ℂ)
    (h : J ∈ FFl k r z z' π π' i D) : s • J ∈ FFl k r z z' π π' i D := by
  obtain ⟨hs, hl, hr, he⟩ := h
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hs g₀ hg₀
    refine ⟨U, fun g => s • F g, hU, hgU, hF.const_smul s, fun g hg hgl => ?_⟩
    show s • J g = s • F g
    rw [hFe g hg hgl]
  · intro g hg n hn
    simp only [Pi.smul_apply]
    rw [hl g hg n hn, smul_comm]
  · intro g hg n hn
    simp only [Pi.smul_apply]
    rw [hr g hg n hn, smul_comm]
  · intro g hg x hx x' hx'
    simp only [Pi.smul_apply]
    rw [he g hg x hx x' hx', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
variable {L : Fin (r + 1)} {Dc Dc₀ : (Fin r → ℂ) → Set (Mx k r)}
theorem fam_zero : FamFF k r z z' π π' L Dc 0 := by
  refine And.intro ?_ ?_
  · intro x₀ _ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
  · intro c _
    exact ff_zero L (Dc c)
theorem fam_add {Φ Ψ : Fn k r (Wq →L[ℂ] Wp)} (h : FamFF k r z z' π π' L Dc Φ) (h' : FamFF k r z z' π π' L Dc Ψ) :
    FamFF k r z z' π π' L Dc (Φ + Ψ) := by
  obtain ⟨hs, hf⟩ := h
  obtain ⟨hs', hf'⟩ := h'
  refine And.intro ?_ ?_
  · intro x₀ hx₀ hg
    obtain ⟨U, F, hU, hxU, hF, hFe⟩ := hs x₀ hx₀ hg
    obtain ⟨U', F', hU', hxU', hF', hFe'⟩ := hs' x₀ hx₀ hg
    refine ⟨U ∩ U', fun x => F x + F' x, hU.inter hU', Set.mem_inter hxU hxU',
      (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun x hx hxg => ?_⟩
    show Φ x.1 x.2 + Ψ x.1 x.2 = F x + F' x
    rw [hFe x hx.1 hxg, hFe' x hx.2 hxg]
  · intro c hc
    exact ff_add (hf c hc) (hf' c hc)
theorem fam_smul (s : ℂ) {Φ : Fn k r (Wq →L[ℂ] Wp)} (h : FamFF k r z z' π π' L Dc Φ) :
    FamFF k r z z' π π' L Dc (s • Φ) := by
  obtain ⟨hs, hf⟩ := h
  refine And.intro ?_ ?_
  · intro x₀ hx₀ hg
    obtain ⟨U, F, hU, hxU, hF, hFe⟩ := hs x₀ hx₀ hg
    refine ⟨U, fun x => s • F x, hU, hxU, hF.const_smul s, fun x hx hxg => ?_⟩
    show s • Φ x.1 x.2 = s • F x
    rw [hFe x hx hxg]
  · intro c hc
    exact ff_smul s (hf c hc)
variable (z z' π π') in

def RS (L : Fin (r + 1)) (Dc Dc₀ : (Fin r → ℂ) → Set (Mx k r)) (S : Set (Fin r → ℂ))
    (Φ Ψ : Fn k r (Wq →L[ℂ] Wp)) : Prop :=
  FamFF k r z z' π π' L Dc Φ ∧ FamFF k r z z' π π' L Dc₀ Ψ ∧
    ∀ c ∈ S, ∀ g ∈ Glev k r L, g ∈ Dc c → Φ c g = Ψ c g
variable (z z') in
structure SData (L : Fin (r + 1)) (Dc Dc₀ : (Fin r → ℂ) → Set (Mx k r)) (S : Set (Fin r → ℂ)) : Prop where
  o : IsOpen (UU Dc)
  o₀ : IsOpen (UU Dc₀)
  d : ∀ c ∈ OmX r, IsDom k r z z' L (Dc c)
  d₀ : ∀ c ∈ OmX r, IsDom k r z z' L (Dc₀ c)
  sub : S ⊆ OmX r
  eq : ∀ c ∈ S, Dc c = Dc₀ c
variable {S : Set (Fin r → ℂ)}
end FF
end
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
section Ind
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def Ind (i : ℕ) (Φ : Fn k r E) : Prop :=
  ∀ c ∈ OmX r, ∀ c' ∈ OmX r, (∀ a : Fin r, a.val < i → c a = c' a) → Φ c = Φ c'
end Ind
section Chain
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
def stepOp (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin r) (Y : ℂ) : OM (Fn k r (Wq →L[ℂ] Wp)) :=
  oMul (TLs k l Y) (oMul (QL k r z z' l.succ Y) (TL k l Y))
variable (z z' π π') in

def RK (D : Set (Mx k r)) (l : Fin r) (Φ Ψ : Fn k r (Wq →L[ℂ] Wp)) : Prop :=
  FamFF k r z z' π π' l.castSucc (Dcell D l.castSucc) Φ ∧ Ind l.val Φ ∧
    FamFF k r z z' π π' l.succ (Dcell D l.succ) Ψ ∧
    ∀ c ∈ OmX r, ∀ g ∈ Glev k r l.succ, g ∈ Dcell D l.succ c → Ψ c g = Res k r l Φ c g
end Chain
end
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
theorem one_uw (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ UWset k r z :=
  ⟨WeylGroupFacts.uh_one, fun _ => ⟨by simp, by simp⟩, by simp⟩
theorem one_nlev (i : Fin (r + 1)) : (1 : Mx k r) ∈ Nlev k r i := ⟨WeylGroupFacts.mem_n_one, Qx3.glev_one i⟩
section Dom
variable {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {D : Set (Mx k r)}
theorem dom_left (hD : IsDom k r z z' i D) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) {n : Mx k r}
    (hn : n ∈ Nlev k r i) : n * g ∈ Glev k r i ∩ D := by
  have := hD.2 g hg (1 * n) ⟨1, one_uw z, n, hn, rfl⟩ (1 * 1) ⟨1, one_uw z', 1, one_nlev i, rfl⟩
  exact ⟨Qx3.glev_mul hn.2 hg.1, by simpa using this⟩
theorem dom_right (hD : IsDom k r z z' i D) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) {n : Mx k r}
    (hn : n ∈ Nlev k r i) : g * n ∈ Glev k r i ∩ D := by
  have := hD.2 g hg (1 * 1) ⟨1, one_uw z, 1, one_nlev i, rfl⟩ (1 * n) ⟨1, one_uw z', n, hn, rfl⟩
  exact ⟨Qx3.glev_mul hg.1 hn.2, by simpa using this⟩
theorem dom_uw (hD : IsDom k r z z' i D) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) {h h' : Mx k r}
    (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') : h * g * h' ∈ Glev k r i ∩ D := by
  have := hD.2 g hg (h * 1) ⟨h, hh, 1, one_nlev i, rfl⟩ (h' * 1) ⟨h', hh', 1, one_nlev i, rfl⟩
  exact ⟨Qx3.glev_mul (Qx3.glev_mul (Qx3.uw_glev i hh) hg.1) (Qx3.uw_glev i hh'), by simpa using this⟩
theorem smooth_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (hD : IsOpen D) {f f' : Mx k r → E}
    (h : SmoothLev k r i D f) (he : ∀ g ∈ Glev k r i ∩ D, f' g = f g) : SmoothLev k r i D f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hf⟩ := h g₀ hg₀
  exact ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left,
    fun g hg hgG => (he g ⟨hgG, hg.2⟩).trans (hf g hg.1 hgG)⟩
end Dom
section Cut
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {L : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}
open Classical in

def cutP (L : Fin (r + 1)) (Dc : (Fin r → ℂ) → Set (Mx k r)) : Fn k r E →ₗ[ℂ] Fn k r E where
  toFun := fun Φ c g => if c ∈ OmX r ∧ g ∈ Glev k r L ∧ g ∈ Dc c then Φ c g else 0
  map_add' := fun Φ Ψ => by
    funext c g
    by_cases h : c ∈ OmX r ∧ g ∈ Glev k r L ∧ g ∈ Dc c <;> simp [h]
  map_smul' := fun s Φ => by
    funext c g
    by_cases h : c ∈ OmX r ∧ g ∈ Glev k r L ∧ g ∈ Dc c <;> simp [h]
theorem cutP_on (Φ : Fn k r E) {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r L)
    (hgD : g ∈ Dc c) : cutP L Dc Φ c g = Φ c g := by
  simp [cutP, hc, hg, hgD]
theorem cutP_eq_iff (Φ Ψ : Fn k r E) :
    cutP L Dc Φ = cutP L Dc Ψ ↔ ∀ c ∈ OmX r, ∀ g ∈ Glev k r L, g ∈ Dc c → Φ c g = Ψ c g := by
  constructor
  · intro h c hc g hg hgD
    have h1 := congrFun (congrFun h c) g
    rwa [cutP_on Φ hc hg hgD, cutP_on Ψ hc hg hgD] at h1
  · intro h
    funext c g
    by_cases hh : c ∈ OmX r ∧ g ∈ Glev k r L ∧ g ∈ Dc c
    · rw [cutP_on Φ hh.1 hh.2.1 hh.2.2, cutP_on Ψ hh.1 hh.2.1 hh.2.2]
      exact h c hh.1 g hh.2.1 hh.2.2
    · simp only [cutP, LinearMap.coe_mk, AddHom.coe_mk, if_neg hh]
def mkData (L : Fin (r + 1)) (Dc : (Fin r → ℂ) → Set (Mx k r)) (P : Fn k r E → Prop) (h0 : P 0)
    (hadd : ∀ Φ Ψ, P Φ → P Ψ → P (Φ + Ψ)) (hsmul : ∀ (s : ℂ) Φ, P Φ → P (s • Φ))
    (hN : ∀ Φ, P Φ → P (cutP L Dc Φ)) : HatData (Fn k r E) where
  G := { carrier := {Φ | P Φ}
         zero_mem' := h0
         add_mem' := fun h h' => hadd _ _ h h'
         smul_mem' := fun s _ h => hsmul s _ h }
  N := cutP L Dc
  N_mem := hN
  N_idem := fun Φ => (cutP_eq_iff _ _).2 (fun _ hc _ hg hgD => cutP_on Φ hc hg hgD)
end Cut
section FF
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
theorem ff_congr {i : Fin (r + 1)} {D : Set (Mx k r)} (hD : IsDom k r z z' i D) {J J' : Mx k r → (Wq →L[ℂ] Wp)}
    (h : J ∈ FFl k r z z' π π' i D) (he : ∀ g ∈ Glev k r i ∩ D, J' g = J g) : J' ∈ FFl k r z z' π π' i D := by
  refine ⟨smooth_congr hD.1 h.1 he, ?_, ?_, ?_⟩
  · intro g hg n hn
    rw [he g hg, he _ (dom_left hD hg hn)]
    exact h.2.1 g hg n hn
  · intro g hg n hn
    rw [he g hg, he _ (dom_right hD hg hn)]
    exact h.2.2.1 g hg n hn
  · intro g hg a ha b hb
    rw [he g hg, he _ (dom_uw hD hg ha hb)]
    exact h.2.2.2 g hg a ha b hb
variable {L : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}
theorem fam_congr (hS : SData z z' L Dc Dc (OmX r)) {Φ Ψ : Fn k r (Wq →L[ℂ] Wp)}
    (h : FamFF k r z z' π π' L Dc Φ) (he : ∀ c ∈ OmX r, ∀ g ∈ Glev k r L, g ∈ Dc c → Ψ c g = Φ c g) :
    FamFF k r z z' π π' L Dc Ψ :=
  ⟨Qx3.sf_congr_on hS.o (fun _ hx => hx) (fun x hx hxG => he x.1 hx.1 x.2 hxG hx.2) h.1,
    fun c hc => ff_congr (hS.d c hc) (h.2 c hc) (fun g hg => he c hc g hg.1 hg.2)⟩
variable (π π') in

def famData (hS : SData z z' L Dc Dc (OmX r)) : HatData (Fn k r (Wq →L[ℂ] Wp)) :=
  mkData (E := Wq →L[ℂ] Wp) L Dc (FamFF k r z z' π π' L Dc) fam_zero (fun _ _ h h' => fam_add h h')
    (fun s _ h => fam_smul s h) (fun Φ h => fam_congr hS h (fun _ hc _ hg hgD => cutP_on Φ hc hg hgD))
end FF
end
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
section HatM
variable {X : Type*} [AddCommGroup X] [Module ℂ X] (H : HatData X)
def hatM (M : OM X) : Matrix (Fin 2) (Fin 2) (Module.End ℂ H.V) := fun a b => H.hat (M a b)
variable {H}
end HatM
section CV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (H : HatData (Fn k r E))
def Rp (Y : ℂ) : ℕ → Matrix (Fin 2) (Fin 2) (Module.End ℂ H.V)
  | 0 => 1
  | j + 1 => (if h : j < r then hatM H (TL k ⟨j, h⟩ Y) else 1) * Rp Y j
def Lp (Y : ℂ) : ℕ → Matrix (Fin 2) (Fin 2) (Module.End ℂ H.V)
  | 0 => 1
  | j + 1 => Lp Y j * (if h : j < r then hatM H (TLs k ⟨j, h⟩ Y) else 1)
variable {H}
end CV
end
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
end Formalism.FourierDecayAlt.P.Qx6
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


