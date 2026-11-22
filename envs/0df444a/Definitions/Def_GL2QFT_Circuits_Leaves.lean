-- Prove2me | Definitions.Def_GL2QFT_Circuits_Leaves
-- name    : GL2QFT_Circuits_Leaves
-- status  : Definition
-- author  : @dmitry
-- created : 2026-11-22T05:58:16.35418+00:00
-- url     : https://prove2.me/theorems/fe3f5f37-3e76-4919-b7e0-e23dc236fa0e
-- title:
--   GL2QFT leaf circuit codes, canonical branching/fixing matrices, and Mackey factorization maps
-- statement:
--   Leaf-level register codes and exact isometric operator definitions decomposing the four heavy Track 3 uniformity results of `GL2QFT` (`arXiv:2608.28573`, Sections 6.4–6.5):
--
--   1. **Modular QFT (Section 6.4.1)**: binary cyclic encoding `zmodCode` and the cyclic Fourier transform `qftModMat N` on $\mathbb{Z}/N\mathbb{Z}$.
--
--   2. **Theorem 6.34 ($A_\gamma$ hard block, Section 6.5)**: quadratic extension register code `fq2Code`, exact branching domain `BranchSrc` (cardinality $2q$), coherent stage codes (`gammaFqCode`, `gammaFq2BranchCode`, `branchPairCode`, `gammaExtCode`), and canonical branching/fixing transforms `canonMbr`, `canonMbrCore`, `BgateSub`, and `canonRfix` (routing fixed points via $W_q$ and symmetric/antisymmetric split and cuspidal pairs into $\mathrm{Irr} \sqcup \mathrm{Irr}$).
--
--   3. **Theorem 6.14 (`totalA` routing, Section 6.4.4)**: decidable partition `isHardIn` / `isHardOut`, `splitInA`, and `mergeOutA` separating one-/two-dimensional blocks from two-dimensional Borel hard blocks $(\rho_\gamma, \rho_\gamma)$.
--
--   4. **Theorem 6.1 ($F_{\mathrm{GL}_2(\mathbb{F}_q)}$ Mackey bridge, Section 6.4.3)**: coset transversal `CosetT`, `cosetRep`, `cosetCode`, intermediate Mackey codes `mackeyMidCode` / `mackeyOutCode`, and the exact isometric stage matrices `mackeyEncMat`, `mackeyNopMat`, and `mackeyReindexMat`.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, Sections 6.4-6.5 (pp. 41-55)

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_GL2QFT_Supplement_TotalA
import Definitions.Def_GL2QFT_Supplement_AGammaGates
set_option autoImplicit false
noncomputable section
open Classical
namespace GL2QFT
namespace Circuits
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms
def zmodCode (W N : ℕ) (x : ZMod N) : Qubits W := fun i => Nat.testBit (ZMod.val x) i.val
def qftModMat (N : ℕ) : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.of fun y x => FieldData.isqrt N *
    Complex.exp (2 * Real.pi * Complex.I * ((ZMod.val x * ZMod.val y : ℕ) : ℂ) / (N : ℂ))
def fq2Code (D : FieldData) (z : D.Fq2) : Qubits (2 * D.r * D.labW) :=
  packNat (2 * D.r) D.labW fun i =>
    if i.val < D.r then D.digit ((AdjoinRoot.modByMonicHom D.F_monic z).coeff 0) i.val
    else D.digit ((AdjoinRoot.modByMonicHom D.F_monic z).coeff 1) (i.val - D.r)
def gammaFqCode (D : FieldData) : D.Lab × D.Fq → Qubits (1 * D.labW + (D.r + 1) * D.labW) :=
  appendCode (fun γ : D.Lab => packNat 1 D.labW ![γ.val]) (fun a : D.Fq => D.tagCode (.inl a))
abbrev BranchSrc (D : FieldData) : Type :=
  {p : Bool × D.Fq2 // (p.1 = false ∧ ∃ r : D.Fq, r ≠ 0 ∧ p.2 = algebraMap D.Fq D.Fq2 r) ∨
    (p.1 = true ∧ p.2 ≠ 0 ∧ p.2 ^ (D.q + 1) = 1)}
def gammaFq2BranchCode (D : FieldData) (p : D.Lab × BranchSrc D) :
    Qubits (1 * D.labW + (1 + 2 * D.r * D.labW)) :=
  appendCode (fun γ : D.Lab => packNat 1 D.labW ![γ.val]) (boolAppCode (fq2Code D)) (p.1, p.2.1)
abbrev BranchPair (D : FieldData) : Type := Σ γ : D.Lab, BranchOut D γ
def branchPairCode (D : FieldData) : BranchPair D → Qubits (3 * D.labW)
  | ⟨γ, .inl δ⟩ => packNat 3 D.labW ![γ.val, 0, δ.val]
  | ⟨γ, .inr θ⟩ => packNat 3 D.labW ![γ.val, 1, θ.1.val]
def gammaExtCode (D : FieldData) (p : D.Lab × (D.Irr ⊕ D.Irr)) : Qubits (4 * D.labW + 1) :=
  match p.2 with
  | .inl μ => Fin.append (D.gammaIrrCode (p.1, μ)) (fun (_ : Fin 1) => false)
  | .inr μ => Fin.append (D.gammaIrrCode (p.1, μ)) (fun (_ : Fin 1) => true)
def canonMbr (D : FieldData) (γ : D.Lab) : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ :=
  Matrix.of fun o br => match o, br with
    | .inl δ, (false, r) =>
        if h : ∃ x : D.Fq, x ≠ 0 ∧ algebraMap D.Fq D.Fq2 x = r then
          FieldData.isqrt (D.q - 1) * D.chi δ (Classical.choose h) else 0
    | .inr θ, (true, r) =>
        if r ≠ 0 ∧ r ^ (D.q + 1) = 1 then FieldData.isqrt (D.q + 1) * kerChar D (θ.1 - theta0Lab D γ) r else 0
    | _, _ => 0
def canonMbrCore (D : FieldData) (γ : D.Lab) : Matrix (BranchOut D γ) (BranchSrc D) ℂ :=
  (canonMbr D γ).submatrix id Subtype.val
def BgateSub (D : FieldData) (γ : D.Lab) : Matrix (BranchSrc D) D.Fq ℂ :=
  (Bgate D γ).submatrix Subtype.val id
private def rfixPair {T : Type} (x y : T) (vx vy : ℂ) (o : T) : ℂ :=
  (if o = x then vx else 0) + (if o = y then vy else 0)
def canonRfix (D : FieldData) (γ : D.Lab) : Matrix (D.Irr ⊕ D.Irr) (BranchOut D γ) ℂ :=
  Matrix.of fun o i => match i with
    | .inl δ =>
        if δ = γ - δ then rfixPair (.inl (.inr (.inl δ))) (.inl (.inl δ))
          (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q))) (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q))) o
        else if hlt : δ.val < (γ - δ).val then rfixPair (.inl (.inr (.inr (.inl ⟨(δ, γ - δ), hlt⟩))))
          (.inr (.inr (.inr (.inl ⟨(δ, γ - δ), hlt⟩)))) (FieldData.isqrt 2) (FieldData.isqrt 2) o
        else if hgt : (γ - δ).val < δ.val then rfixPair (.inl (.inr (.inr (.inl ⟨(γ - δ, δ), hgt⟩))))
          (.inr (.inr (.inr (.inl ⟨(γ - δ, δ), hgt⟩)))) (FieldData.isqrt 2) (-FieldData.isqrt 2) o
        else 0
    | .inr θ =>
        if D.q + 1 ∣ θ.1.val then
          let δ : D.Lab := ((θ.1.val / (D.q + 1) : ℕ) : D.Lab)
          rfixPair (.inl (.inr (.inl δ))) (.inl (.inl δ))
            (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q))) (-(Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)))) o
        else if hcusp1 : D.IsCuspLabel θ.1 then
          rfixPair (.inl (.inr (.inr (.inr ⟨θ.1, hcusp1⟩)))) (.inr (.inr (.inr (.inr ⟨θ.1, hcusp1⟩))))
            (FieldData.isqrt 2) (FieldData.isqrt 2) o
        else if hcusp2 : D.IsCuspLabel ((D.q : D.Lab2) * θ.1) then
          rfixPair (.inl (.inr (.inr (.inr ⟨_, hcusp2⟩)))) (.inr (.inr (.inr (.inr ⟨_, hcusp2⟩))))
            (FieldData.isqrt 2) (-FieldData.isqrt 2) o
        else 0
def isHardIn (D : FieldData) (x : InReg D) : Bool :=
  match x.1.1, x.1.2.2.2 with | .inr _, .inr _ => true | _, _ => false
def isHardOut (D : FieldData) (y : OutReg D) : Bool :=
  match y.1, y.2.2 with | .inr _, .inr _ => true | _, _ => false
abbrev InRegNonHard (D : FieldData) := {x : InReg D // isHardIn D x = false}
abbrev InRegHard (D : FieldData) := {x : InReg D // isHardIn D x = true}
abbrev OutRegNonHard (D : FieldData) := {y : OutReg D // isHardOut D y = false}
abbrev OutRegHard (D : FieldData) := {y : OutReg D // isHardOut D y = true}
def splitInA (D : FieldData) (x : InReg D) : InRegNonHard D ⊕ InRegHard D :=
  if h : isHardIn D x then .inr ⟨x, h⟩ else .inl ⟨x, Bool.eq_false_iff.mpr h⟩
def mergeOutA (D : FieldData) : OutRegNonHard D ⊕ OutRegHard D → OutReg D := Sum.elim Subtype.val Subtype.val
abbrev CosetT (D : FieldData) : Type := Unit ⊕ D.Fq
def cosetRep (D : FieldData) : CosetT D → D.G
  | .inl () => 1
  | .inr x => ⟨!![x, 1; 1, 0], !![0, 1; 1, -x],
      by ext i j; fin_cases i <;> fin_cases j <;> simp, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
def cosetCode (D : FieldData) : CosetT D → Qubits (1 + (D.r + 1) * D.labW)
  | .inl () => boolAppCode (fun a : D.Fq => D.tagCode (.inl a)) (false, 0)
  | .inr x => boolAppCode (fun a : D.Fq => D.tagCode (.inl a)) (true, x)
def bbasLab (D : FieldData) : ∀ l : D.BIrr, D.BBas l → D.Lab
  | .inl _, _ => 0 | .inr _, δ => δ
abbrev MackeyMid (D : FieldData) : Type := Σ x : InReg D, D.BBas x.1.2.2.2 × D.BBas x.1.1
def mackeyMidEmb (D : FieldData) (m : MackeyMid D) : (D.Lab × D.Lab) × InReg D :=
  ((bbasLab D m.1.1.2.2.2 m.2.1, bbasLab D m.1.1.1 m.2.2), m.1)
abbrev MackeyOut (D : FieldData) : Type :=
  {m : Σ y : OutReg D, D.BBas y.2.2 × D.BBas y.1 //
    (labMu D m.1.2.1 m.1.2.2 m.2.1).isSome ∧ (labMu D m.1.2.1 m.1.1 m.2.2).isSome}
def mackeyOutEmb (D : FieldData) (m : MackeyOut D) : (D.Lab × D.Lab) × OutReg D :=
  ((bbasLab D m.1.1.2.2 m.1.2.1, bbasLab D m.1.1.1 m.1.2.2), m.1.1)
def mackeyMidCode (D : FieldData) (m : MackeyMid D) : Qubits (2 * D.labW + 10 * D.labW) :=
  appendCode (fun p : D.Lab × D.Lab => packNat 2 D.labW ![p.1.val, p.2.val]) (inCodeA D) (mackeyMidEmb D m)
def mackeyOutCode (D : FieldData) (m : MackeyOut D) : Qubits (2 * D.labW + 9 * D.labW) :=
  appendCode (fun p : D.Lab × D.Lab => packNat 2 D.labW ![p.1.val, p.2.val]) (outCodeA D) (mackeyOutEmb D m)
def mackeyEncMat (D : FieldData) : Matrix (CosetT D × D.BElt) D.G ℂ :=
  Matrix.of fun tb g =>
    if (g : Matrix (Fin 2) (Fin 2) D.Fq) = (cosetRep D tb.1 : Matrix (Fin 2) (Fin 2) D.Fq) * D.bmat tb.2 then 1 else 0
def mackeyNopMat (D : FieldData) : Matrix (MackeyMid D) (CosetT D × D.BOutLabel) ℂ :=
  Matrix.of fun m tb =>
    if hl : tb.2.1 = m.1.1.1 then
      let P : D.BBas m.1.1.1 := cast (congrArg D.BBas hl) tb.2.2.1
      if m.2.2 = cast (congrArg D.BBas hl) tb.2.2.2 then
        match tb.1 with
        | .inl () =>
            if m.1.1.2.2.1 = false then
              if hlt : m.1.1.2.2.2 = m.1.1.1 then
                if m.2.1 = cast (congrArg D.BBas hlt.symm) P then 1 else 0 else 0 else 0
        | .inr x =>
            if m.1.1.2.2.1 = true then match m.1.1.2.1 with
              | .inl ab => match tLab D m.1.1.2.2.2 ab with
                  | some Pt => FieldData.isqrt D.q * (Real.sqrt (Fintype.card (D.BBas m.1.1.2.2.2) : ℝ) : ℂ) *
                      D.RB m.1.1.2.2.2 !![1, x; 0, 1] m.2.1 Pt * utwW D m.1.1.1 ab P
                  | none => 0
              | .inr _ => 0 else 0
      else 0 else 0
def mackeyReindexFun (D : FieldData) (m : MackeyOut D) : D.OutLabel :=
  ⟨m.1.1.2.1, Option.get _ m.2.1, Option.get _ m.2.2⟩
def mackeyReindexMat (D : FieldData) : Matrix D.OutLabel (MackeyOut D) ℂ := permMat (mackeyReindexFun D)
end Circuits
end GL2QFT


