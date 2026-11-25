-- Prove2me | Definitions.Def_DetDLP_S8H0_SignalBank
-- name    : DetDLP_S8H0_SignalBank
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:58:35.633872+00:00
-- url     : https://prove2.me/theorems/a7491510-db0c-4866-9c3b-44207cbe62ea
-- title:
--   Boolean registers for elliptic-curve order witnesses
-- statement:
--   Coordinates, gate outputs, remainders, quotients, products, internal multiplier signals and addition carries are stored in Boolean registers. Canonical range checks give a bijection with the typed transcript; imposing the seven arithmetic checks and the curve check on those registers yields a bijection with elliptic-curve points.
-- source:
--   DetDLP elliptic-curve order query, UUID f0e81f0e-6143-4672-a126-0c2b5aa2d552.

import Definitions.Def_DetDLP_S8H0_ResidueWires
import Theorems.Thm_DetDLP_w3_m5_modmul_r2

set_option autoImplicit false
set_option maxHeartbeats 30000
namespace DetDLP.S8H0.SignalBank
open S8H.ECPointArithmetic S8H.ECPointSlots ResidueWires SevenChecks

abbrev MulBank (d : ℕ) (hd : 1 ≤ d) := Bits (2*d) × Bits (w4_M5GraphBounds.graph d hd).nE
abbrev CertBank (d : ℕ) (hd : 1 ≤ d) := (Triple d × Bits d × MulBank d hd × MulBank d hd) × Bool
abbrev AuxBank (d : ℕ) := Bits (2*d) × Bits (d+1) × Bits (d+1) × Bits (d+1)
abbrev RunBank (d : ℕ) (hd : 1 ≤ d) := Triple d × CertBank d hd
abbrev CoordsBank (d : ℕ) := Bool × Triple d × Triple d
abbrev Bank (d : ℕ) (hd : 1 ≤ d) := CoordsBank d × (Fin 7 → RunBank d hd) × (Fin 7 → AuxBank d)

def canonical {d : ℕ} {hd : 1 ≤ d} (p : ℕ) (w : Bank d hd) :=
  (below p w.1.2.1 ∧ below p w.1.2.2) ∧
    ∀ i, below p (w.2.1 i).1 ∧ below p (w.2.1 i).2.1.1

def split {A B : Type} (P : A → Prop) (Q : B → Prop) :
    {v : A × B // P v.1 ∧ Q v.2} ≃ {x // P x} × {y // Q y} where
  toFun v := (⟨v.val.1,v.property.1⟩,⟨v.val.2,v.property.2⟩)
  invFun v := ⟨(v.1.val,v.2.val),v.1.property,v.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def mulEquiv {d : ℕ} (hd : 1 ≤ d) : MulBank d hd ≃ w3_mulRun d hd :=
  (numBits (2*d)).prodCongr (Equiv.refl _)

def auxEquiv (d : ℕ) : AuxBank d ≃ w3_slotHashAux d :=
  (Equiv.refl _).prodCongr ((numBits (d+1)).prodCongr (Equiv.refl _))

abbrev Bounded {d : ℕ} (p : ℕ) := {v : Triple d // below p v}
abbrev CheckedRun (d p : ℕ) (hd : 1 ≤ d) := Bounded (d:=d) p ×
  ((Bounded (d:=d) p × Bits d × MulBank d hd × MulBank d hd) × Bool)

noncomputable def runEquiv {p d : ℕ} [NeZero p] (hd : 1 ≤ d) (hp : p ≤ 2^d) : CheckedRun d p hd ≃ ZMod p × w3_fpHashCert d p hd :=
  (zmodEquiv hp).prodCongr (((finEquiv hp).prodCongr ((numBits d).prodCongr ((mulEquiv hd).prodCongr (mulEquiv hd)))).prodCongr (Equiv.refl _))

abbrev Checked (d p : ℕ) (hd : 1 ≤ d) := (Bool × Bounded (d:=d) p × Bounded (d:=d) p) ×
    (Fin 7 → CheckedRun d p hd) × (Fin 7 → AuxBank d)

def splitBank {d p : ℕ} (hd : 1 ≤ d) : {w : Bank d hd // canonical p w} ≃ Checked d p hd where
  toFun s :=
    ((s.val.1.1,⟨s.val.1.2.1,s.property.1.1⟩,⟨s.val.1.2.2,s.property.1.2⟩),
      (fun i => let v := s.val.2.1 i
                (⟨v.1,(s.property.2 i).1⟩,(⟨v.2.1.1,(s.property.2 i).2⟩,v.2.1.2),v.2.2)),s.val.2.2)
  invFun s := ⟨((s.1.1,s.1.2.1.val,s.1.2.2.val),(fun i => let v := s.2.1 i
              (v.1.val,(v.2.1.1.val,v.2.1.2),v.2.2)),s.2.2),
    ⟨s.1.2.1.property,s.1.2.2.property⟩,fun i => ⟨(s.2.1 i).1.property,(s.2.1 i).2.1.1.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {p : ℕ} [Fact p.Prime]

noncomputable def decode : {w : Bank (width p) (Nat.succ_pos _) // canonical p w} ≃ C p × Transcript p :=
  let hp := (fits p).le
  (splitBank (Nat.succ_pos _)).trans <|
  ((Equiv.refl Bool).prodCongr ((zmodEquiv hp).prodCongr (zmodEquiv hp))).prodCongr
    ((Equiv.piCongrRight (fun _ : Fin 7 => runEquiv (Nat.succ_pos _) hp)).prodCongr
      (Equiv.piCongrRight (fun _ : Fin 7 => auxEquiv (width p))))

variable (E : WeierstrassCurve (ZMod p))

def accepts (w : Bank (width p) (Nat.succ_pos _)) :=
  ∃ h : canonical p w, let v := decode (p:=p) ⟨w,h⟩; physical E v.1 v.2

private noncomputable def restrict {A B : Type} {P : A → Prop} (e : {a // P a} ≃ B) (Q : B → Prop) :
    {a : A // ∃ h : P a, Q (e ⟨a,h⟩)} ≃ {b // Q b} where
  toFun a := ⟨e ⟨a.val,a.property.choose⟩,a.property.choose_spec⟩
  invFun b := ⟨(e.symm b.val).val,(e.symm b.val).property,by simpa only [e.apply_symm_apply] using b.property⟩
  left_inv a := by
    apply Subtype.ext
    exact congrArg (fun z : {a // P a} => z.val) (e.symm_apply_apply ⟨a.val,a.property.choose⟩)
  right_inv b := Subtype.ext (e.apply_symm_apply b.val)

noncomputable def witnessEquiv : {w // accepts E w} ≃ {v : C p × Transcript p // physical E v.1 v.2} :=
  restrict (decode (p:=p)) (fun v => physical E v.1 v.2)

noncomputable def orderPoints [E.IsElliptic] : {w // accepts E w} ≃ E.toAffine.Point :=
  (witnessEquiv E).trans (pointEquiv E w3_m5_modmul_r2)

end DetDLP.S8H0.SignalBank


