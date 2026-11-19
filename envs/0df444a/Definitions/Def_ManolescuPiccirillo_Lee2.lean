-- Prove2me | Definitions.Def_ManolescuPiccirillo_Lee2
-- name    : ManolescuPiccirillo_Lee2
-- status  : Definition
-- author  : @LG
-- created : 2026-11-16T18:52:04.952203+00:00
-- url     : https://prove2.me/theorems/729de389-8745-4a57-85bd-acce77e154be
-- title:
--   Manolescu–Piccirillo: Lee homology and the Rasmussen $s$-invariant
-- statement:
--   The Lee differential, chain complex, degree-zero Lee homology, its quantum filtration, and the Rasmussen invariant $s=(s_{\max}+s_{\min})/2$.
-- source:
--   Rasmussen, https://doi.org/10.1007/s00222-010-0275-6 ; Lee, https://arxiv.org/abs/math/0210213

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Lee1

open Classical
noncomputable section

namespace ManolescuPiccirillo
namespace PD

variable (D : PD)

instance : Fintype (D.LeeGen) := by unfold LeeGen State; infer_instance
instance : DecidableEq (D.LeeGen) := by unfold LeeGen State; infer_instance

def flip (s : D.State) (ci : Fin D.numCrossings) : D.State :=
  fun j => if j = ci then !s j else s j

def signBefore (s : D.State) (ci : Fin D.numCrossings) : ℚ :=
  (-1 : ℚ) ^ ((List.ofFn (fun j : Fin ci.val => s ⟨j.val, Nat.lt_trans j.isLt ci.isLt⟩)).filter (fun b => b)).length

theorem mem_labels {c : Fin 4 → ℕ} (hc : c ∈ D.crossings) (j : Fin 4) : c j ∈ D.labels := by
  simp only [labels, entries]
  rw [List.mem_toFinset, List.mem_flatMap]
  exact ⟨c, hc, by fin_cases j <;> simp⟩

def labAt (c : Fin 4 → ℕ) (hc : c ∈ D.crossings) (j : Fin 4) : D.labels :=
  ⟨c j, D.mem_labels hc j⟩

def edgeCoeff (ci : Fin D.numCrossings) (g g' : D.LeeGen) : ℚ :=
  if hst : g'.val.1 = D.flip g.val.1 ci then
    let c := D.crossings[ci.val]
    let hc : c ∈ D.crossings := List.getElem_mem _
    let a := D.labAt c hc 0; let b := D.labAt c hc 1
    let cc := D.labAt c hc 2; let d := D.labAt c hc 3
    let conn := D.stateConnected g.val.1
    let touched : Finset D.labels := {a, b, cc, d}
    if hag : ∀ x : D.labels, (∀ t ∈ touched, ¬ conn x.val t.val) → g.val.2 x = g'.val.2 x then
      if hmerge : ¬ conn a.val b.val then
        if g'.val.2 a = g.val.2 a + g.val.2 b then 1 else 0
      else
        let x := g.val.2 a; let y := g'.val.2 a; let z := g'.val.2 cc
        if x = 0 then (if y ≠ z then 1 else 0) else (if y = z then 1 else 0)
    else 0
  else 0

def LeeBasis (i : ℤ) : Type := { g : D.LeeGen // D.homDeg g = i }

instance (i : ℤ) : Fintype (D.LeeBasis i) := Subtype.fintype _
instance (i : ℤ) : DecidableEq (D.LeeBasis i) := inferInstance

def leeMatrix (i : ℤ) : Matrix (D.LeeBasis (i + 1)) (D.LeeBasis i) ℚ :=
  fun gout gin =>
    ∑ ci : Fin D.numCrossings,
      if gin.val.val.1 ci = false ∧ gout.val.val.1 = D.flip gin.val.val.1 ci then
        D.signBefore gin.val.val.1 ci * D.edgeCoeff ci gin.val gout.val
      else 0

abbrev C (i : ℤ) : Type := D.LeeBasis i → ℚ

def d (i : ℤ) : C D i →ₗ[ℚ] C D (i + 1) := Matrix.toLin' (D.leeMatrix i)

abbrev H0 : Type :=
  (LinearMap.ker (d D 0)) ⧸
    (((LinearMap.range (d D (-1)) : Submodule ℚ (C D 0)) ⊓ LinearMap.ker (d D 0)).comap
      (LinearMap.ker (d D 0)).subtype)

def qFilt (q : ℤ) : Submodule ℚ (C D 0) where
  carrier := { f | ∀ b : D.LeeBasis 0, D.qDeg b.val < q → f b = 0 }
  zero_mem' := by intro b hb; rfl
  add_mem' := by intro x y hx hy b hb; simp [hx b hb, hy b hb]
  smul_mem' := by intro a x hx b hb; simp [hx b hb]

def HFilt (q : ℤ) : Submodule ℚ (H0 D) :=
  Submodule.map (Submodule.mkQ _) ((qFilt D q).comap (LinearMap.ker (d D 0)).subtype)

def classDeg (h : H0 D) : ℤ := sSup { q : ℤ | h ∈ HFilt D q }

def sMax : ℤ := sSup (classDeg D '' { h : H0 D | h ≠ 0 })
def sMin : ℤ := sInf (classDeg D '' { h : H0 D | h ≠ 0 })

def rasmussenS : ℤ := (sMax D + sMin D) / 2

end PD
end ManolescuPiccirillo


