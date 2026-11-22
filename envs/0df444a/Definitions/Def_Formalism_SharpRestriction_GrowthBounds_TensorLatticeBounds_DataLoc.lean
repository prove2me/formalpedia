-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
-- name    : Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:31.395613+00:00
-- url     : https://prove2.me/theorems/6ce97c92-2ed8-4c1e-9ced-836cbcb2b5d5
-- title:
--   Data Loc
-- statement:
--   Definitions and structural lemmas for Data Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLoc.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G
section Loc
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
theorem p_ne (h : HidaSetting p n' W Qq O Kf ι σ j w) : (p : Qq) ≠ 0 := by
  have := h.frac_alt
  have h1 : algebraMap W Qq (p : W) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W Qq)).2 h.p_unif.ne_zero
  simpa using h1
def line (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (p : ℕ) (n : ℤ) : Submodule W (Fin 1 → Qq) :=
  Submodule.span W {fun _ => (p : Qq) ^ n}
abbrev places1 (h : HidaSetting p n' W Qq O Kf ι σ j w) : Places p O Kf where
  w := w
  nV := 1
  n' := fun _ => n'
  W := fun _ => W
  Qq := fun _ => Qq
  ι := fun _ => ι
  σ := fun _ => σ
  j := fun _ => j
  setting := fun _ => h
  m := 0
  r := 1
  lam0 := fun _ _ _ => 0
  dom := fun _ _ _ _ _ => le_rfl
def homoth (h : HidaSetting p n' W Qq O Kf ι σ j w) : Multiplicative ℤ →* GL (Fin 1) Qq :=
  (Units.map ((Matrix.scalar (Fin 1) : Qq →+* Matrix (Fin 1) (Fin 1) Qq) : Qq →* Matrix (Fin 1) (Fin 1) Qq)).comp
    (zpowersHom Qqˣ (Units.mk0 (p : Qq) (p_ne h)))
def level1 (h : HidaSetting p n' W Qq O Kf ι σ j w) : Level (places1 h) where
  Γ := Multiplicative ℤ
  act := fun _ => (homoth h : Multiplicative ℤ →* GL (Fin 1) Qq)
  χ := 1
def gat1 (h : HidaSetting p n' W Qq O Kf ι σ j w) : GAtP p where
  O := O
  Kf := Kf
  P := places1 h
  comp := Unit
  lev := fun _ => level1 h
  e := 0
end Loc
def levTriv {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) : Level P where
  Γ := Unit
  act := fun _ => 1
  χ := 1
section Chain
variable {p : ℕ} (G : GAtP p)
def cBound : ℕ := ∑ v, ∑ s, ∑ i, (G.P.lam0 v s i).natAbs
theorem abs_le_cBound (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (i : Fin (G.P.m + 1)) :
    |G.P.lam0 v s i| ≤ (cBound G : ℤ) := by
  have h1 : (G.P.lam0 v s i).natAbs ≤ ∑ i, (G.P.lam0 v s i).natAbs :=
    Finset.single_le_sum (f := fun i => (G.P.lam0 v s i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h2 : ∑ i, (G.P.lam0 v s i).natAbs ≤ ∑ s, ∑ i, (G.P.lam0 v s i).natAbs :=
    Finset.single_le_sum (f := fun s => ∑ i, (G.P.lam0 v s i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  have h3 : ∑ s, ∑ i, (G.P.lam0 v s i).natAbs ≤ cBound G :=
    Finset.single_le_sum (f := fun v => ∑ s, ∑ i, (G.P.lam0 v s i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ v)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h1.trans (h2.trans h3)
theorem liftWt_anti (t m : ℕ) (lam : Fin (m + 1) → ℤ) (hl : Antitone lam) (c : ℤ) (hc : -lam (Fin.last m) ≤ c)
    (j : ℕ) : Antitone (liftWt t m lam (fun _ => c) j) := by
  intro a b hab
  have hab' : a.val ≤ b.val := hab
  unfold liftWt
  split_ifs with h1 h2 h2
  · exact hl (show (⟨a.val, h2⟩ : Fin (m + 1)) ≤ ⟨b.val, h1⟩ from hab')
  · omega
  · have := hl (Fin.le_last (⟨a.val, h2⟩ : Fin (m + 1)))
    show -c ≤ _
    omega
  · exact le_rfl
def fillsOf (TT : ∀ v : Fin G.P.nV, Finset (Fin (G.P.n' v))) (t mm : ℕ) : Fills G where
  TT := TT
  a := fun v s => G.P.lam0 v s 0
  b := fun v s => -G.P.lam0 v s (Fin.last G.P.m)
  c := cBound G
  base := fun v s => ⟨fun _ => ⟨rfl, (neg_neg _).symm, fun i _ _ => abs_le_cBound G v s i⟩,
    fun _ i => abs_le_cBound G v s i⟩
  t := t
  mm := mm
  w := fun v _ s => max (cBound G : ℤ) (-(G.P.lam0 v s (Fin.last G.P.m)))
  w_ge := fun _ _ => le_rfl
  w_mono := fun _ _ _ _ => le_rfl
  domJ := fun j v s => liftWt_anti t G.P.m (G.P.lam0 v s) (G.P.dom v s) _ (le_max_right _ _) j
variable {G}
def levelsOf (Fl : Fills G) : Levels Fl where
  compS := fun _ => Unit
  levS := fun _ _ => levTriv _
def chainOf {Fl : Fills G} (Lv : Levels Fl) : Chain Lv where
  Kz := fun _ => 0
end Chain
end Formalism.MainNotions.G.Inhab
end


