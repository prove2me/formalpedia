-- Prove2me | Definitions.Def_SubspaceEvasion312_GMC_reloc
-- name    : SubspaceEvasion312_GMC_reloc
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-22T23:13:02.575731+00:00
-- url     : https://prove2.me/theorems/e871db9d-35c7-4987-a55a-a584c1ccd833
-- title:
--   Four-instruction relocation blocks and call context
-- statement:
--   A nested machine instruction is translated into a block of at most four instructions. Natural and field registers of the nested program occupy disjoint regions above caller bases. Natural input indices are directed to designated caller registers, field inputs return zero, and output instructions copy the latest emitted value into designated caller registers. Loads and stores are rebased into the nested field region. The module also records the relation between caller and callee states and elementary one- through four-step execution constructors.
-- source:
--   Supporting operational infrastructure for STOC 2027 submission #312, Theorem 17's explicit linear encoders (printed p.10, PDF p.11), using the machine and charged execution model formalized for the paper's Theorems 8–9.

import Definitions.Def_SubspaceEvasion312_GMC_core

namespace SubspaceEvasion312.Explicit.Dev.GMC
open SubspaceEvasion312.Explicit

variable {F : Type} [Field F]

def tr2 (natBase fieldBase na : ℕ) (nm : ℕ → ℕ) (fo no : ℕ) (base exit : ℕ)
    (p : ℕ) : Instruction F → List (Instruction F)
  | .halt => [.jump exit]
  | .literal d v => [.literal (N natBase d) v, .jump (base+4*p+4)]
  | .inputNat d i => if i < na then
      [.addNat (N natBase d) (nm i) 0, .jump (base+4*p+4)] else
      [.literal (N natBase d) 0, .jump (base+4*p+4)]
  | .addNat d a b => [.addNat (N natBase d) (N natBase a) (N natBase b), .jump (base+4*p+4)]
  | .subNat d a b => [.subNat (N natBase d) (N natBase a) (N natBase b), .jump (base+4*p+4)]
  | .mulNat d a b => [.mulNat (N natBase d) (N natBase a) (N natBase b), .jump (base+4*p+4)]
  | .divNat d a b => [.divNat (N natBase d) (N natBase a) (N natBase b), .jump (base+4*p+4)]
  | .modNat d a b => [.modNat (N natBase d) (N natBase a) (N natBase b), .jump (base+4*p+4)]
  | .branchNat a b y n => [.branchNat (N natBase a) (N natBase b) (base+4*y) (base+4*n)]
  | .constant d v => [.constant (A fieldBase d) v, .jump (base+4*p+4)]
  | .add d a b => [.add (A fieldBase d) (A fieldBase a) (A fieldBase b), .jump (base+4*p+4)]
  | .sub d a b => [.sub (A fieldBase d) (A fieldBase a) (A fieldBase b), .jump (base+4*p+4)]
  | .mul d a b => [.mul (A fieldBase d) (A fieldBase a) (A fieldBase b), .jump (base+4*p+4)]
  | .inv d a => [.inv (A fieldBase d) (A fieldBase a), .jump (base+4*p+4)]
  | .load d a => [.literal natBase fieldBase, .addNat natBase natBase (N natBase a),
      .load (A fieldBase d) natBase, .jump (base+4*p+4)]
  | .store a s => [.literal natBase fieldBase, .addNat natBase natBase (N natBase a),
      .store natBase (A fieldBase s), .jump (base+4*p+4)]
  | .input d a => [.constant (A fieldBase d) 0, .jump (base+4*p+4)]
  | .branch a b y n => [.branch (A fieldBase a) (A fieldBase b) (base+4*y) (base+4*n)]
  | .jump q => [.jump (base+4*q)]
  | .output s => [.add fo (A fieldBase s) 0, .jump (base+4*p+4)]
  | .outputNat s => [.addNat no (N natBase s) 0, .jump (base+4*p+4)]

def blk2 (natBase fieldBase na : ℕ) (nm : ℕ → ℕ) (fo no base exit p : ℕ)
    (i : Instruction F) : List (Instruction F) := pad (tr2 natBase fieldBase na nm fo no base exit p i)

theorem tr2_length (natBase fieldBase na : ℕ) (nm : ℕ → ℕ) (fo no base exit p : ℕ)
    (i : Instruction F) : (tr2 natBase fieldBase na nm fo no base exit p i).length ≤ 4 := by
  cases i <;> simp [tr2] <;> split_ifs <;> simp
theorem blk2_length (natBase fieldBase na : ℕ) (nm : ℕ → ℕ) (fo no base exit p : ℕ)
    (i : Instruction F) : (blk2 natBase fieldBase na nm fo no base exit p i).length = 4 := by
  have h := tr2_length natBase fieldBase na nm fo no base exit p i
  simp [blk2, pad]; omega

structure RnB (natBase fieldBase fo no B base : ℕ)
    (z w₀ w : MachineState F) : Prop where
  pc : w.pc = base + 4*z.pc
  subN : ∀ j, w.natReg (N natBase j) = z.natReg j
  mainN : ∀ a < natBase, w.natReg a = if a = no then z.natOut.reverse.getD 0 0 else w₀.natReg a
  subF : ∀ j, w.fieldReg (A fieldBase j) = z.fieldReg j
  mainF : ∀ a < fieldBase, w.fieldReg a = if a = fo then z.out.reverse.getD 0 0 else w₀.fieldReg a
  bnd : ∀ j, w.natReg j ≤ B
  out : w.out = w₀.out
  nout : w.natOut = w₀.natOut

structure Ctx (natBase fieldBase na no : ℕ) (nm : ℕ → ℕ) (B Bs : ℕ)
    (w₀ : MachineState F) : Prop where
  hno : no < natBase
  hnm : ∀ i < na, nm i < natBase
  hnmno : ∀ i < na, nm i ≠ no
  hzeroN : w₀.natReg 0 = 0
  hzeroF : w₀.fieldReg 0 = 0
  hb₀ : ∀ i, w₀.natReg i ≤ B
  hBs : Bs ≤ B
  haddr : fieldBase + Bs ≤ B

lemma bnd_upd {f : ℕ → ℕ} {B j v : ℕ} (h : ∀ i, f i ≤ B) (hv : v ≤ B) :
    ∀ i, Function.update f j v i ≤ B := by
  intro i; rw [Function.update_apply]; split_ifs <;> [exact hv; exact h i]

lemma one {Q : Program F} {B bp : ℕ} {w : MachineState F} {X : Instruction F}
    (hb : ∀ i, w.natReg i ≤ B) (hpc : w.pc = bp) (c0 : Q[bp]? = some X) (hX : X ≠ .halt) :
    reach Q [] [] B 1 w (eff [] [] w X) :=
  reach.succ X hb (hpc ▸ c0) hX (reach.zero _)

lemma two {Q : Program F} {B bp bp1 q : ℕ} {w : MachineState F} {X : Instruction F}
    (hb : ∀ i, w.natReg i ≤ B) (hpc : w.pc = bp) (c0 : Q[bp]? = some X) (hX : X ≠ .halt)
    (hb1 : ∀ i, (eff [] [] w X).natReg i ≤ B) (hpc1 : (eff [] [] w X).pc = bp1)
    (c1 : Q[bp1]? = some (.jump q)) :
    reach Q [] [] B 2 w {eff [] [] w X with pc := q} :=
  reach.succ X hb (hpc ▸ c0) hX
    (reach.succ (.jump q) hb1 (hpc1 ▸ c1) (by simp) (reach.zero _))

lemma three {Q : Program F} {B bp bp1 bp2 q : ℕ} {w : MachineState F} {X Y : Instruction F}
    (hb : ∀ i, w.natReg i ≤ B) (hpc : w.pc = bp) (c0 : Q[bp]? = some X) (hX : X ≠ .halt)
    (hb1 : ∀ i, (eff [] [] w X).natReg i ≤ B) (hpc1 : (eff [] [] w X).pc = bp1)
    (c1 : Q[bp1]? = some Y) (hY : Y ≠ .halt)
    (hb2 : ∀ i, (eff [] [] (eff [] [] w X) Y).natReg i ≤ B)
    (hpc2 : (eff [] [] (eff [] [] w X) Y).pc = bp2) (c2 : Q[bp2]? = some (.jump q)) :
    reach Q [] [] B 3 w {eff [] [] (eff [] [] w X) Y with pc := q} :=
  reach.succ X hb (hpc ▸ c0) hX
    (reach.succ Y hb1 (hpc1 ▸ c1) hY
      (reach.succ (.jump q) hb2 (hpc2 ▸ c2) (by simp) (reach.zero _)))

lemma four {Q : Program F} {B bp bp1 bp2 bp3 q : ℕ} {w : MachineState F} {X Y Z : Instruction F}
    (hb : ∀ i, w.natReg i ≤ B) (hpc : w.pc = bp) (c0 : Q[bp]? = some X) (hX : X ≠ .halt)
    (hb1 : ∀ i, (eff [] [] w X).natReg i ≤ B) (hpc1 : (eff [] [] w X).pc = bp1)
    (c1 : Q[bp1]? = some Y) (hY : Y ≠ .halt)
    (hb2 : ∀ i, (eff [] [] (eff [] [] w X) Y).natReg i ≤ B)
    (hpc2 : (eff [] [] (eff [] [] w X) Y).pc = bp2) (c2 : Q[bp2]? = some Z) (hZ : Z ≠ .halt)
    (hb3 : ∀ i, (eff [] [] (eff [] [] (eff [] [] w X) Y) Z).natReg i ≤ B)
    (hpc3 : (eff [] [] (eff [] [] (eff [] [] w X) Y) Z).pc = bp3)
    (c3 : Q[bp3]? = some (.jump q)) :
    reach Q [] [] B 4 w {eff [] [] (eff [] [] (eff [] [] w X) Y) Z with pc := q} :=
  reach.succ X hb (hpc ▸ c0) hX
    (reach.succ Y hb1 (hpc1 ▸ c1) hY
      (reach.succ Z hb2 (hpc2 ▸ c2) hZ
        (reach.succ (.jump q) hb3 (hpc3 ▸ c3) (by simp) (reach.zero _))))

lemma code {Q : Program F} {bp : ℕ} {l : List (Instruction F)}
    (hc : ∀ r < 4, Q[bp+r]? = (pad l)[r]?) (hl : l.length ≤ 4) (r : ℕ) (hr : r < l.length) :
    Q[bp+r]? = l[r]? := by
  rw [hc r (by omega)]; simp [pad, List.getElem?_append_left hr]

lemma input_ns (na : ℕ) (nm : ℕ → ℕ) (w₀ : MachineState F) (i : ℕ) :
    ((List.range na).map fun a => w₀.natReg (nm a)).getD i 0 =
      if i < na then w₀.natReg (nm i) else 0 := by
  by_cases hi : i < na <;>
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, hi]

end SubspaceEvasion312.Explicit.Dev.GMC


