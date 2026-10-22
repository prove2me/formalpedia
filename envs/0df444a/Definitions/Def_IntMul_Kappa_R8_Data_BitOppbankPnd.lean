-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
-- name    : IntMul_Kappa_R8_Data_BitOppbankPnd
-- status  : Definition
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:29:02.954202+00:00
-- url     : https://prove2.me/theorems/1351eb81-c6fc-472d-9f10-928a7b41aa70
-- title:
--   R8 honest Pnd(supG)/HasCentre/orthOK — ND Pc ≠ 0 stub
-- statement:
--   Self-contained densified node projectors for opp-bank BitNB at $\mathrm{codeBound}=64251$.
--
--   Supports come from published `BitOppbankSupG` ($39528b46$). Local copies of Defs51 `Bf`/`prjM`/`HasCentre`/`spanS` give
--   $$\mathrm{Pnd}(\mathrm{sup})=\mathrm{prjM}(\mathrm{spanS}\,\mathrm{sup})\quad\text{when }\mathrm{HasCentre}(\mathrm{sup}),\ \text{else }0.$$
--   ND codes use
--   $$\mathrm{Pc}(1773+n)=\mathrm{Pnd}(\mathrm{densSupG}\,n),$$
--   not the ProjB/NetD zero stub. Also densified `orthOK`/`nestOK`/`ch0P`.
-- source:
--   SupG 39528b46; LocSlots; ChkBitArg; QHNet 52d9e9e0; Net0P 373d80bb

-- R8 opp-bank self-contained densified Pnd / HasCentre / orthOK / honest ND Pc.
-- No Defs50/Defs51 import. Supports via BitOppbankSupG.densSupG.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLocSlots
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankChkBitArg
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.dupNamespace false

/-!
# Densified `Pnd(supG)` — honest ND `Pc` (self-contained)

* `densSupG` from published `BitOppbankSupG` (jfstack active DAG, dense $d$ ↔ raw $d+1$)
* `HasCentre` / `spanS` / `Bf` / `prjM` / `Pnd` — Defs51 semantics, local copy (no Defs51)
* `HasCentre` carries `∑ tvQ i = 3` so `centre_span` needs no external `tri_spec`
* `orthOK` / `nestOK` on densified supports
* `Pc (1773+n) = Pnd (densSupG n)` — not the ProjB/NetD zero stub
-/

open Matrix Module
open scoped Kronecker
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.LocSlots
open IntMul.Kappa.R8.Bit.Oppbank.ChkBitArg
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.Pnd

abbrev V23 := Fin 23 → ℚ
abbrev M23 := Matrix (Fin 23) (Fin 23) ℚ
abbrev Pr23 := Fin 23 × Fin 23

def fieldOf (X w i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight X (Nat.mul w i)) (Nat.sub (Nat.shiftLeft 1 w) 1)

def ptsL (T k : ℕ) : ℕ := fieldOf TPTS 5 (Nat.add (Nat.mul 3 T) k)

def triL (T : ℕ) : ℕ :=
  Nat.lor (Nat.lor (Nat.shiftLeft 1 (ptsL T 0)) (Nat.shiftLeft 1 (ptsL T 1)))
    (Nat.shiftLeft 1 (ptsL T 2))

def tvQ (T : ℕ) : V23 := fun p => if (triL T).testBit p.val = true then 1 else 0
def xv (T : ℕ) : V23 := tvQ T
def yv (T : ℕ) : V23 := fun p => (tvQ T p - (∑ q : Fin 23, tvQ T q) / 9) / 2
def Pl (T : ℕ) : M23 := vecMulVec (xv T) (yv T)

def starL (c : ℕ) : ℕ :=
  (List.range 1771).foldl
    (fun acc T =>
      if ptsL T 0 = c ∨ ptsL T 1 = c ∨ ptsL T 2 = c then
        Nat.lor acc (Nat.shiftLeft 1 T)
      else acc)
    0

def exclTL (c t1 t2 : ℕ) : ℕ :=
  Nat.xor (starL c) (Nat.land (starL c) (Nat.lor (starL t1) (starL t2)))

def orthTL (T : ℕ) : ℕ :=
  Nat.lor (Nat.lor (exclTL (ptsL T 0) (ptsL T 1) (ptsL T 2))
      (exclTL (ptsL T 1) (ptsL T 0) (ptsL T 2)))
    (exclTL (ptsL T 2) (ptsL T 0) (ptsL T 1))

noncomputable def orthOK (n T : ℕ) : Bool :=
  Nat.beq (Nat.land (densSupG n) (orthTL T)) (densSupG n)

def argF (n : ℕ) : ℕ := fieldOf ARGT 32 n
def dimF (n : ℕ) : ℕ := fieldOf DIMT 5 n

def argRel (a n : ℕ) : Bool :=
  Nat.beq (Nat.land (argF n) 65535) a || Nat.beq (Nat.shiftRight (argF n) 16) a

def isND (c : ℕ) : Bool := Nat.ble 1773 c && Nat.blt c codeBound
def isPT (c : ℕ) : Bool := Nat.ble 2 c && Nat.blt c 1773

noncomputable def nestOK (o c : ℕ) : Bool :=
  Nat.ble o 1 || Nat.ble c 1 ||
  (isND o && isND c &&
    (argRel (Nat.sub o 1773) (Nat.sub c 1773) || argRel (Nat.sub c 1773) (Nat.sub o 1773))) ||
  (isND o && isPT c && orthOK (Nat.sub o 1773) (Nat.sub c 2)) ||
  (isPT o && isND c && orthOK (Nat.sub c 1773) (Nat.sub o 2))

def dimCF (c : ℕ) : ℕ :=
  if c = 0 then 0
  else if c = 1 then 23
  else if c < 1773 then 22
  else dimF (c - 1773)

noncomputable def rkC (a b : ℕ) : ℕ :=
  let a1 := dimCF a; let b1 := dimCF b
  if a1 < b1 then b1 - a1 else a1 - b1

def bfF (u v : V23) : ℚ := u ⬝ᵥ v - (∑ p, u p) * (∑ p, v p) / 9

noncomputable def Bf : LinearMap.BilinForm ℚ V23 :=
  LinearMap.mk₂ ℚ bfF
    (fun u u' v => by simp only [bfF, add_dotProduct, Pi.add_apply, Finset.sum_add_distrib]; ring)
    (fun c u v => by simp only [bfF, smul_dotProduct, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring)
    (fun u v v' => by simp only [bfF, dotProduct_add, Pi.add_apply, Finset.sum_add_distrib]; ring)
    (fun c u v => by simp only [bfF, dotProduct_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring)

theorem Bf_apply (u v : V23) : Bf u v = bfF u v := rfl

theorem bfF_comm (u v : V23) : bfF u v = bfF v u := by
  simp only [bfF, dotProduct_comm]; ring

theorem Bf_refl : Bf.IsRefl := fun u v h => by rw [Bf_apply, bfF_comm, ← Bf_apply]; exact h

theorem mem_orth {V : Submodule ℚ V23} {w : V23} :
    w ∈ Bf.orthogonal V ↔ ∀ v ∈ V, bfF v w = 0 :=
  LinearMap.BilinForm.mem_orthogonal_iff

theorem bf_pos {c : Fin 23} {v : V23} (hv : ∑ p, v p = 3 * v c) (h0 : bfF v v = 0) : v = 0 := by
  have hsq : ∑ p, v p * v p = v c * v c + ∑ p ∈ Finset.univ.erase c, v p * v p :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ c)).symm
  have hsum : ∑ p, v p = v c + ∑ p ∈ Finset.univ.erase c, v p :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ c)).symm
  have h1 : ∑ p ∈ Finset.univ.erase c, v p * v p = 0 := by
    have : bfF v v = ∑ p ∈ Finset.univ.erase c, v p * v p := by
      simp only [bfF, dotProduct]; rw [hsq, hv]; ring
    rw [← this, h0]
  have h2 : ∀ p ∈ Finset.univ.erase c, v p = 0 := by
    intro p hp
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => mul_self_nonneg (v q))).1 h1 p hp
    exact mul_self_eq_zero.1 this
  have h3 : ∑ p ∈ Finset.univ.erase c, v p = 0 := Finset.sum_eq_zero h2
  have hc : v c = 0 := by rw [hsum, h3] at hv; linarith
  funext p
  by_cases hp : p = c
  · rw [hp, hc]; rfl
  · exact h2 p (Finset.mem_erase.2 ⟨hp, Finset.mem_univ p⟩)

theorem compl_of_centre {V : Submodule ℚ V23} {c : Fin 23}
    (hV : ∀ v ∈ V, ∑ p, v p = 3 * v c) : IsCompl V (Bf.orthogonal V) := by
  rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint Bf_refl, Submodule.disjoint_def]
  intro x hx hxo
  exact bf_pos (hV x hx) (mem_orth.1 hxo x hx)

def IsPrj (P : M23) (V : Submodule ℚ V23) : Prop :=
  (∀ v ∈ V, P *ᵥ v = v) ∧ ∀ w ∈ Bf.orthogonal V, P *ᵥ w = 0

noncomputable def prjM (V : Submodule ℚ V23) (h : IsCompl V (Bf.orthogonal V)) : M23 :=
  LinearMap.toMatrix' (V.projection (Bf.orthogonal V) h)

def spanS (sup : ℕ) : Submodule ℚ V23 :=
  Submodule.span ℚ {v | ∃ i, (sup.testBit i = true) ∧ v = tvQ i}

/-- Centre certificate (Defs51 + weight-3; densified jfstack supports satisfy this). -/
def HasCentre (sup : ℕ) : Prop :=
  ∃ c < 23, ∀ i, (sup.testBit i = true) →
    i < 1771 ∧ (triL i).testBit c = true ∧ (∑ p : Fin 23, tvQ i p = 3)


theorem centre_span {sup : ℕ} (h : HasCentre sup) :
    ∃ c : Fin 23, ∀ v ∈ spanS sup, ∑ p, v p = 3 * v c := by
  obtain ⟨c, hc, hsup⟩ := h
  refine ⟨⟨c, hc⟩, fun v hv => ?_⟩
  let H : Submodule ℚ V23 :=
    { carrier := {v | ∑ p, v p = 3 * v ⟨c, hc⟩}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at *
        rw [ha, hb]; ring
      zero_mem' := by simp
      smul_mem' := fun r a ha => by
        simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at *
        rw [ha]; ring }
  have hle : spanS sup ≤ H := by
    rw [spanS, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨hi1, hic, hsum⟩ := hsup i hi
    show ∑ p, tvQ i p = 3 * tvQ i ⟨c, hc⟩
    rw [hsum]
    simp [tvQ, hic]
  exact hle hv

theorem compl_spanS {sup : ℕ} (h : HasCentre sup) :
    IsCompl (spanS sup) (Bf.orthogonal (spanS sup)) := by
  obtain ⟨c, hc⟩ := centre_span h
  exact compl_of_centre hc

open Classical in
/-- Node support projector (`0` without a centre) — Defs51 `Pnd`. -/
noncomputable def Pnd (sup : ℕ) : M23 :=
  if h : HasCentre sup then prjM (spanS sup) (compl_spanS h) else 0

/-- Honest ND projector on densified support. -/
noncomputable def PndD (n : ℕ) : M23 := Pnd (densSupG n)

/-- Projector named by a code — ND branch is `Pnd(densSupG ·)`, not `0`. -/
noncomputable def Pc (c : ℕ) : M23 :=
  if c = 0 then 0
  else if c = 1 then 1
  else if c < 1773 then 1 - Pl (c - 2)
  else PndD (c - 1773)

noncomputable def Dm (o c : ℕ) : M23 :=
  if dimCF o ≤ dimCF c then Pc c - Pc o else Pc o - Pc c

def K (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (A B : M23) : Matrix (Fin 529) (Fin 529) ℚ :=
  S * (A ⊗ₖ B) * Si

noncomputable def Lab0 : Finset (V23 × V23) :=
  (Finset.range 1771).image fun T => (xv T, yv T)

noncomputable def idxD : Finset (ℕ × ℕ) :=
  ((Finset.range codeBound) ×ˢ (Finset.range codeBound)).filter
    (fun p => nestOK p.1 p.2 = true)

attribute [irreducible] idxD

noncomputable def Pis0 : Finset M23 :=
  idxD.image (fun p => Dm p.1 p.2) ∪ (Finset.range 1771).image Pl

attribute [irreducible] Pis0

abbrev FB0 (S : Matrix (Fin 529) Pr23 ℚ) (Sinv : Matrix Pr23 (Fin 529) ℚ) : Prop :=
  S * Sinv = 1 ∧ Sinv * S = 1 ∧
    (∀ p ∈ Lab0,
      AuxE (h := 19) (S * ((1 : M23) ⊗ₖ (1 - vecMulVec p.1 p.2)) * Sinv) ∧
        AuxE (h := 19) (S * ((1 - vecMulVec p.1 p.2) ⊗ₖ (1 : M23)) * Sinv)) ∧
    (∀ p ∈ Lab0, ∀ A ∈ Pis0,
      SideE (h := 19) (S * (A ⊗ₖ vecMulVec p.1 p.2) * Sinv) A.rank ∧
        SideE (h := 19) (S * (vecMulVec p.1 p.2 ⊗ₖ A) * Sinv) A.rank) ∧
    (∀ p₁ ∈ Lab0, ∀ p₂ ∈ Lab0,
      DataE (h := 19)
        (S * ((1 - vecMulVec p₁.1 p₁.2) ⊗ₖ (1 - vecMulVec p₂.1 p₂.2)) * Sinv))

noncomputable def S0 : Matrix (Fin 529) Pr23 ℚ :=
  Classical.epsilon (fun S => ∃ Sinv, FB0 S Sinv)

noncomputable def Si0 : Matrix Pr23 (Fin 529) ℚ :=
  Classical.epsilon (fun Sinv => FB0 S0 Sinv)

def dfltE : Edge 529 := ⟨1, [], 1⟩

open Classical in
noncomputable def pickE (P : Edge 529 → Prop) : Edge 529 :=
  if h : ∃ e, P e then Classical.choose h else dfltE

def SideR (r : ℕ) (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  ∃ rs', rs = sideRuns 23 529 r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
    (runPairs (sideRuns 23 529 r)).length + rs'.length = r

def DataR (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  ∃ rs', rs = dataRuns 23 529 ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧ rs'.length = 24

def AuxR (rs : List (ℕ × ℕ × ℕ)) : Prop := rs = auxRuns 19

def PE (q : Matrix (Fin 529) (Fin 529) ℚ) (R : List (ℕ × ℕ × ℕ) → Prop)
    (e : Edge 529) : Prop :=
  EdgeQ e q ∧ R e.runs

structure Ch where
  S : Matrix (Fin 529) Pr23 ℚ
  Si : Matrix Pr23 (Fin 529) ℚ
  e1 : ℕ → ℕ → ℕ → Edge 529
  e2 : ℕ → ℕ → ℕ → Edge 529
  ex : ℕ → Edge 529
  en : ℕ → ℕ → Edge 529
  ei : ℕ → Edge 529
  ec : ℕ → ℕ → Edge 529

/-- Opp-bank `ch0P` with honest densified `Pnd`/`Pc`/`orthOK`. -/
noncomputable def ch0P : Ch where
  S := S0
  Si := Si0
  e1 b o c :=
    if b < v ∧ o < codeBound ∧ c < codeBound then
      pickE (PE (K S0 Si0 (Dm o c) (Pl b)) (SideR (rkC o c)))
    else dfltE
  e2 a o c :=
    if a < v ∧ o < codeBound ∧ c < codeBound then
      pickE (PE (K S0 Si0 (Pl a) (Dm o c)) (SideR (rkC o c)))
    else dfltE
  ex b :=
    if b < v then pickE (PE (K S0 Si0 1 (1 - Pl b)) AuxR) else dfltE
  en a t :=
    if a < v ∧ t < v then pickE (PE (K S0 Si0 (1 - Pl a) (1 - Pl t)) DataR) else dfltE
  ei a :=
    if a < v then pickE (PE (K S0 Si0 (1 - Pl a) 1) AuxR) else dfltE
  ec a s :=
    if a < v ∧ s < v then pickE (PE (K S0 Si0 (Pl a) (Pl s)) (SideR 1)) else dfltE

theorem Pc_of_ND (n : ℕ) (hn : 1773 + n < codeBound) :
    Pc (1773 + n) = PndD n := by
  have hne0 : ¬ (1773 + n = 0) := by omega
  have hne1 : ¬ (1773 + n = 1) := by omega
  have hge : ¬ (1773 + n < 1773) := by omega
  simp only [Pc, hne0, hne1, hge, ite_false, PndD]
  simp [Nat.add_sub_cancel]

theorem Pnd_eq_prj {sup : ℕ} (h : HasCentre sup) :
    Pnd sup = prjM (spanS sup) (compl_spanS h) := dif_pos h

theorem Pnd_zero_of_no_centre {sup : ℕ} (h : ¬ HasCentre sup) : Pnd sup = 0 := dif_neg h

/-- ND codes use densified `PndD` (not the ProjB zero stub). -/
theorem Pc_ND_ne_stub (n : ℕ) (hn : 1773 + n < codeBound) (hC : HasCentre (densSupG n)) :
    Pc (1773 + n) = prjM (spanS (densSupG n)) (compl_spanS hC) := by
  rw [Pc_of_ND n hn, PndD, Pnd_eq_prj hC]

end IntMul.Kappa.R8.Bit.Oppbank.Pnd


