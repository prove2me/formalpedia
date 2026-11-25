-- Prove2me | Definitions.Def_DetDLP_S8L_FpPairStage
-- name    : DetDLP_S8L_FpPairStage
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:50:43.568+00:00
-- url     : https://prove2.me/theorems/6ea498ca-3b64-484b-933c-b39ed2ee5741
-- title:
--   Physical wires of a modular multiplication stage
-- statement:
--   Read the quotient from the second multiplier input and read both full products from the output wires. For fixed operands, modulus, and a remainder fitting the column width, physical assignments satisfying the two multipliers, the column adder, and the bus equalities are in bijection with the checked modular multiplication certificates. The adder contributes exactly one carry string.

import Definitions.Def_DetDLP_S8L_FpPairTiles

set_option autoImplicit false
namespace DetDLP.S8L.FpPair.Stage
open S8J HashGateLayout w4_M5PortTensor w4_ConvolutionArithmetic S8C.AddLayout

abbrev Vec (n : ℕ) := Fin n → Bool
abbrev Mul {d : ℕ} (hd : 1 ≤ d) := Vec (w3_fpMulLayout d hd).nb
abbrev StageBits {d : ℕ} (hd : 1 ≤ d) := Vec (stage d hd).nb
abbrev Cert (d : ℕ) (hd : 1 ≤ d) := Fin (2^d) × w3_mulRun d hd × w3_mulRun d hd

def readWord {n : ℕ} (w : Vec n) : Fin (2^n) := ⟨bitsToNat w,bitsToNat_lt_pow w⟩
@[simp] theorem read_bit {n : ℕ} (w : Vec n) (i : Fin n) : (readWord w).val.testBit i.val = w i := by
  simpa only [readWord,canonicalBits,← Nat.testBit_eq_decide_div_mod_eq] using congrFun (canonicalBits_bitsToNat w) i
@[simp] theorem read_word {n : ℕ} (v : Fin (2^n)) : readWord (fun i : Fin n => v.val.testBit i.val) = v := by
  apply Fin.ext
  change bitsToNat _ = _
  rw [show (fun i : Fin n => v.val.testBit i.val) = canonicalBits n v.val from
    funext fun i => Nat.testBit_eq_decide_div_mod_eq .., bitsToNat_canonicalBits v.isLt]

def input {d : ℕ} (hd : 1 ≤ d) (w : Mul hd) (b : Bool) (i : Fin d) := w (ext hd (inPos b i))
def output {d : ℕ} (hd : 1 ≤ d) (w : Mul hd) (i : Fin (2*d)) := w (ext hd (outPos i))

theorem bus_iff {d : ℕ} (hd : 1 ≤ d) (w : Mul hd) (a b c : ℕ) :
    (∀ i, w (ext hd i) = w3_mulBus d a b c i) ↔
    (∀ i, input hd w false i = a.testBit i.val) ∧ (∀ i, input hd w true i = b.testBit i.val) ∧
      ∀ i, output hd w i = c.testBit i.val := by
  constructor
  · intro H; refine ⟨fun i => ?_,fun i => ?_,fun i => ?_⟩
    · simpa [input,inPos,w3_mulBus,i.isLt] using H (inPos false i)
    · simpa [input,inPos,w3_mulBus,show d+i.val < 2*d by omega] using H (inPos true i)
    · simpa [output,outPos,w3_mulBus,show ¬ (2*d+i.val < d) by omega] using H (outPos i)
  · rintro ⟨h,k,l⟩ i
    by_cases hl : i.val < d
    · simpa [input,inPos,w3_mulBus,hl] using h ⟨i.val,hl⟩
    · by_cases hm : i.val < 2*d
      · have He : inPos true (⟨i.val-d,by omega⟩ : Fin d) = i := Fin.ext (by simp [inPos]; omega)
        simpa [input,He,w3_mulBus,hl,hm] using k ⟨i.val-d,by omega⟩
      · have He : outPos (⟨i.val-2*d,by omega⟩ : Fin (2*d)) = i := Fin.ext (by simp [outPos]; omega)
        simpa [output,He,w3_mulBus,hl,hm] using l ⟨i.val-2*d,by omega⟩

/-- Both multipliers keep their own physical wire assignments. -/
def tests {d : ℕ} (hd : 1 ≤ d) : w3_factorTest (stage d hd) :=
  joinTest (joinTest (w3_fpMulTests d hd) (w3_fpMulTests d hd)) (test false)

def assemble {d : ℕ} (hd : 1 ≤ d) (u v : Mul hd) (w : Vec (2*d*4)) : StageBits hd :=
  Fin.append (Fin.append u v) w

abbrev first {d : ℕ} (hd : 1 ≤ d) (w : StageBits hd) : Mul hd := (w ∘ Fin.castAdd _) ∘ Fin.castAdd _
abbrev second {d : ℕ} (hd : 1 ≤ d) (w : StageBits hd) : Mul hd := (w ∘ Fin.castAdd _) ∘ Fin.natAdd _
abbrev columns {d : ℕ} (hd : 1 ≤ d) (w : StageBits hd) : Vec (2*d*4) := w ∘ Fin.natAdd _

/-- Pin the public modulus, expose both operands and the remainder, and connect the two raw products to the column adder. -/
def buses {d : ℕ} (hd : 1 ≤ d) (p x y z : ℕ) (w : StageBits hd) :=
  (∀ i, input hd (first hd w) false i = x.testBit i.val) ∧
  (∀ i, input hd (first hd w) true i = y.testBit i.val) ∧
  (∀ i, input hd (second hd w) true i = p.testBit i.val) ∧
  (∀ i, columns hd w (reg i 0) = output hd (second hd w) i) ∧
  (∀ i, columns hd w (reg i 1) = z.testBit i.val) ∧
  (∀ i, columns hd w (reg i 2) = output hd (first hd w) i)

def certificate {d : ℕ} (hd : 1 ≤ d) (w : StageBits hd) : Cert d hd :=
  (readWord (input hd (second hd w) false),
    (readWord (output hd (first hd w)),first hd w), (readWord (output hd (second hd w)),second hd w))

theorem decode {d : ℕ} (hd : 1 ≤ d) {p x y z : ℕ} (hz : z < 2^(2*d)) (w : StageBits hd)
    (hw : Accept _ (tests hd) w) (hbus : buses hd p x y z w) :
    w3_modTwo hd p x y z (certificate hd w) := by
  obtain ⟨hm,ha⟩ := (join_iff _ _ w).mp hw
  obtain ⟨hf,hs⟩ := (join_iff _ _ _).mp hm
  obtain ⟨hx,hy,hp,hq,hr,hu⟩ := hbus
  let r := certificate hd w
  refine ⟨(w3_fpMulPins_inc hd _ _ _).mpr ⟨(bus_iff hd _ ..).mpr ⟨hx,hy,fun i => (read_bit _ i).symm⟩,hf⟩,
    (w3_fpMulPins_inc hd _ _ _).mpr ⟨(bus_iff hd _ ..).mpr ⟨fun i => (read_bit _ i).symm,hp,fun i => (read_bit _ i).symm⟩,hs⟩,?_⟩
  have H := (S8C.AddLayout.test_iff false _).mp ha
  change Columns false (fun i => columns hd w (reg i 0)) (fun i => columns hd w (reg i 1)) (fun i => columns hd w (reg i 2)) _ at H
  simp only [hq,hr,hu] at H
  have HC : w3_addColumns (2*d) r.2.2.1.val z r.2.1.1.val false (fun i => columns hd w (reg i 3)) := by
    rw [← S8C.AddLayout.columns_iff (by omega : 0 < 2*d)]
    simp only [r,certificate,read_bit]
    exact H
  simpa only [Bool.toNat_false,Nat.add_zero] using w3_addColumns_sound r.2.2.1.isLt hz r.2.1.1.isLt HC

@[simp] theorem first_assemble {d : ℕ} (hd : 1 ≤ d) (u v : Mul hd) (w : Vec (2*d*4)) :
    first hd (assemble hd u v w) = u := by unfold first assemble; erw [appendL,appendL]
@[simp] theorem second_assemble {d : ℕ} (hd : 1 ≤ d) (u v : Mul hd) (w : Vec (2*d*4)) :
    second hd (assemble hd u v w) = v := by unfold second assemble; erw [appendL,appendR]
@[simp] theorem columns_assemble {d : ℕ} (hd : 1 ≤ d) (u v : Mul hd) (w : Vec (2*d*4)) :
    columns hd (assemble hd u v w) = w := by unfold columns assemble; exact appendR ..

theorem addRegs {n : ℕ} (a b z : ℕ) (c : Vec n) (i : Fin n) :
    addBits a b z c (reg i 0) = a.testBit i.val ∧ addBits a b z c (reg i 1) = b.testBit i.val ∧
    addBits a b z c (reg i 2) = z.testBit i.val ∧ addBits a b z c (reg i 3) = c i := by
  have hh (j : Fin 4) : (reg i j).val/4 = i.val ∧ (reg i j).val%4 = j.val := by simp only [reg]; omega
  simp only [addBits,(hh _).1,(hh _).2]; repeat' constructor

def encode {d : ℕ} (hd : 1 ≤ d) (z : ℕ) (r : Cert d hd) (c : Vec (2*d)) : StageBits hd :=
  assemble hd r.2.1.2 r.2.2.2 (addBits r.2.2.1.val z r.2.1.1.val c)

theorem lift {d : ℕ} (hd : 1 ≤ d) {p x y z : ℕ} (hz : z < 2^(2*d)) {r : Cert d hd}
    (hr : w3_modTwo hd p x y z r) : ∃ w : StageBits hd,
    (Accept _ (tests hd) w ∧ buses hd p x y z w) ∧ certificate hd w = r := by
  obtain ⟨hf,hs,c,hc,_⟩ := (w3_addColumns_modTwo hd hz r).mp hr
  obtain ⟨f,ft⟩ := (w3_fpMulPins_inc hd _ _ _).mp hf
  obtain ⟨s,st⟩ := (w3_fpMulPins_inc hd _ _ _).mp hs
  obtain ⟨fx,fy,fo⟩ := (bus_iff hd _ ..).mp f
  obtain ⟨sq,sp,so⟩ := (bus_iff hd _ ..).mp s
  refine ⟨encode hd z r c,⟨?_,?_⟩,?_⟩
  · unfold tests encode assemble stage
    erw [joined,joined]; exact ⟨⟨ft,st⟩,(addBits_iff (by omega) ..).mpr hc⟩
  · unfold buses encode; erw [first_assemble,second_assemble,columns_assemble]
    exact ⟨fx,fy,sp,fun i => (addRegs _ _ _ _ i).1.trans (so i).symm,
      fun i => (addRegs _ _ _ _ i).2.1,fun i => (addRegs _ _ _ _ i).2.2.1.trans (fo i).symm⟩
  · unfold certificate encode
    erw [first_assemble,second_assemble,funext sq,funext fo,funext so,read_word,read_word,read_word]

theorem wires_ext {d : ℕ} (hd : 1 ≤ d) {w v : StageBits hd} (h : first hd w = first hd v)
    (k : second hd w = second hd v) (l : columns hd w = columns hd v) : w = v := by
  funext i; induction i using Fin.addCases with
  | left i => induction i using Fin.addCases with
    | left i => exact congrFun h i
    | right i => exact congrFun k i
  | right i => exact congrFun l i

theorem inject {d : ℕ} (hd : 1 ≤ d) {p x y z : ℕ} (hz : z < 2^(2*d)) {v w : StageBits hd}
    (hv : Accept _ (tests hd) v ∧ buses hd p x y z v) (hw : Accept _ (tests hd) w ∧ buses hd p x y z w)
    (he : certificate hd v = certificate hd w) : v = w := by
  have hf := congrArg (fun r : Cert d hd => r.2.1.2) he
  have hs := congrArg (fun r : Cert d hd => r.2.2.2) he
  change first hd v = first hd w at hf
  change second hd v = second hd w at hs
  let c (t : StageBits hd) (i : Fin (2*d)) := columns hd t (reg i 3)
  let r := certificate hd w
  have cols (t : StageBits hd) (ht : Accept _ (tests hd) t ∧ buses hd p x y z t) :
      w3_addColumns (2*d) (certificate hd t).2.2.1.val z (certificate hd t).2.1.1.val false (c t) := by
    obtain ⟨_,_,_,a,b,e⟩ := ht.2
    have H := (S8C.AddLayout.test_iff false _).mp ((join_iff _ _ t).mp ht.1).2
    change Columns false (fun i => columns hd t (reg i 0)) (fun i => columns hd t (reg i 1)) (fun i => columns hd t (reg i 2)) (c t) at H
    simp only [a,b,e] at H
    rw [← S8C.AddLayout.columns_iff (by omega : 0 < 2*d)]; simp only [certificate,read_bit]; exact H
  have hc := cols v hv
  rw [he] at hc
  have hcw := cols w hw
  have uniq := w3_addColumns_unique r.2.2.1.isLt hz r.2.1.1.isLt (w3_addColumns_sound r.2.2.1.isLt hz r.2.1.1.isLt hcw)
  have ce : c v = c w := uniq.unique hc hcw
  apply wires_ext hd hf hs
  funext k
  let i : Fin (2*d) := ⟨k.val/4,by omega⟩
  have hreg (j : Fin 4) (h : k.val%4 = j.val) : k = reg i j := Fin.ext (by change k.val = 4*(k.val/4)+j.val; omega)
  obtain ⟨_,_,_,a,b,e⟩ := hv.2
  obtain ⟨_,_,_,a',b',e'⟩ := hw.2
  have hk : k.val%4 < 4 := by omega
  interval_cases hj : k.val%4
  · rw [hreg 0 rfl,a,a',hs]
  · rw [hreg 1 rfl,b,b']
  · rw [hreg 2 rfl,e,e',hf]
  · rw [hreg 3 rfl]; exact congrFun ce i

noncomputable def equiv {d : ℕ} (hd : 1 ≤ d) (p x y z : ℕ) (hz : z < 2^(2*d)) :
    {w : StageBits hd // Accept _ (tests hd) w ∧ buses hd p x y z w} ≃
    {r : Cert d hd // w3_modTwo hd p x y z r} := by
  apply Equiv.ofBijective (fun w => ⟨certificate hd w.val,decode hd hz w.val w.property.1 w.property.2⟩)
  exact ⟨fun v w h => Subtype.ext (inject hd hz v.property w.property (congrArg Subtype.val h)),
    fun r => by obtain ⟨w,hw,he⟩ := lift hd hz r.property; exact ⟨⟨w,hw⟩,Subtype.ext he⟩⟩

end DetDLP.S8L.FpPair.Stage


