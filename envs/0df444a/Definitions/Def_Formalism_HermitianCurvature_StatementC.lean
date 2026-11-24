-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementC
-- name    : Formalism_HermitianCurvature_StatementC
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:10:18.850255+00:00
-- url     : https://prove2.me/theorems/a7dc382c-97c9-4c58-a913-7897998e3125
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementC.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.C
open Finset Filter Topology NumberField MeasureTheory
open scoped ComplexOrder ComplexConjugate
noncomputable section
open Classical
abbrev Letter := Bool × ℝ
abbrev Word (f : ℕ) := Fin f → List Letter
def Word.cnt {f : ℕ} (w : Word f) : ℕ := univ.sup fun v => (w v).length
def Word.emp (f : ℕ) : Word f := fun _ => []
def Word.size {f : ℕ} (P : Fin f → ℝ → ℝ) (w : Word f) : ℝ :=
  ∏ v, ((w v).map fun a => |P v a.2|).prod
def listsUpTo (S : Finset ℝ) (n : ℕ) : Finset (List Letter) :=
  (range (n + 1)).biUnion fun m =>
    (Fintype.piFinset fun _ : Fin m => (univ : Finset Bool) ×ˢ S).image List.ofFn
def wall {f : ℕ} (grid : Fin f → Finset ℝ) (n : ℕ) : Finset (Word f) :=
  Fintype.piFinset fun v => listsUpTo (grid v) n
def gridL (α β : ℝ) (N a : ℕ) : ℝ := α + (β - α) / 3 + (2 * (a : ℝ) - 2) * ((β - α) / (6 * N))
abbrev LPt := List (ℕ × ℂ)
def loc {E : Type} [Field E] (σ : E →+* ℂ) (p : TB.Pt E) : LPt := p.map fun b => (b.1, σ b.2)
def Mlev (k r j : ℕ) : ℤ := (k : ℤ) + 1 + 2 * ((r : ℤ) + 1 - j)
def nAux (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) : ℕ → LPt → ℝ
  | _, [] => 1
  | b, (s, t) :: rest =>
      (if b + s - 1 = r + 1 ∧ s = 1 then GG ^ (k - 1)
        else (fr b s * ‖t‖) ^ (2 * (s : ℤ) * (Mlev k r (b + s - 1) + s - 3))) * nAux k r GG fr (b + s) rest
def nLoc (k r : ℕ) (fr : ℕ → ℕ → ℝ) (G : LPt → ℝ) (p : LPt) : ℝ := nAux k r (G p) fr 1 p
structure PlaceData (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] where

  bs : B.RealPlaceData k r Wp Wq

  f0 : B.Mat k r → (Wq →L[ℂ] Wp)

  G : LPt → ℝ

  RR : ℝ → ℕ → List Letter → LPt → LPt → ℂ
structure HidaSetting (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] where
  f : ℕ
  pl : Fin f ≃ InfinitePlace E

  emb : Fin f → (E →+* ℂ)

  hemb : ∀ v, InfinitePlace.mk (emb v) = pl v

  G : Sz.Glob (InfinitePlace E)

  CA : ℝ
  de : ℕ → ℝ
  de' : ℕ → ℝ
  T : ℝ
  T' : ℝ

  l : ℕ

  grid : Fin f → ℕ → Finset ℝ

  grid1 : Fin f → Finset ℝ

  pd : ∀ v : Fin f, PlaceData G.k G.r (Wp (pl v)) (Wq (pl v))

  hv : G.v = S6.rd E / 2

  hT : ∀ v, Formalism.QuantumDeterminants.Tz G.k G.r (pd v).bs.z = T ∧ Formalism.QuantumDeterminants.Tz G.k G.r (pd v).bs.z' = T'
def Kst : ℕ := 5
namespace HidaSetting
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  (S : HidaSetting E Wp Wq)
def σ (v : Fin S.f) : E →+* ℂ := S.emb v
def r : ℕ := S.G.r
def P (v : Fin S.f) : ℝ → ℝ := (S.G.place (S.pl v)).P
def g : ℕ := S.G.g1 * S.G.g2
def fr (b s : ℕ) : ℝ := S6.rd E ^ (-(S6.nuBlock (S.G.r : ℤ) (b : ℤ) (s : ℤ) : ℝ))
def gramLoc (v : Fin S.f) (ε : ℝ) (i : ℕ) (a : List Letter) (p q : LPt) : ℂ :=
  ((√(nLoc S.G.k S.G.r S.fr (S.pd v).G p) * √(nLoc S.G.k S.G.r S.fr (S.pd v).G q) : ℝ) : ℂ) *
    (S.pd v).RR ε i a p q
def gram (ε : ℝ) (i : ℕ) (w : Word S.f) (p q : TB.Pt E) : ℂ :=
  if i ≤ S.G.r + 1 then ∏ v, S.gramLoc v ε i (w v) (loc (S.σ v) p) (loc (S.σ v) q) else 0
def N1 (ε : ℝ) (i : ℕ) (w : Word S.f) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ)
    (c : J.CV E) : ℂ :=
  (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w v)
      (loc (S.σ v) h ++ [(1, c (S.pl v))]) (loc (S.σ v) h' ++ [(1, c (S.pl v))])) /
    (Word.size S.P w : ℂ)
def psiInf (l : E) (c : J.CV E) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
    (((∑ v, 2 * (S.σ v l * c (S.pl v)).re) / (S.g : ℝ) : ℝ) : ℂ))
def Nhat (ε : ℝ) (i : ℕ) (w : Word S.f) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (l : E) : ℂ :=
  ((ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) : ℝ) : ℂ)⁻¹ *
    ∫ c : J.CV E, S.N1 ε i w Y κ c * S.psiInf l c
end HidaSetting
namespace HidaSetting
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  (S : HidaSetting E Wp Wq)
def Ntop : ℕ := 4 * Kst * (S.G.r + 1)
def cutLo (v : Fin S.f) : ℝ := 5 / 2 - (S.G.place (S.pl v)).v S.l
def cutHi (v : Fin S.f) : ℝ := (S.G.place (S.pl v)).Del / 2 - (S.G.place (S.pl v)).v S.l
def admitted (w : Word S.f) : Prop :=
  (∀ v, ∀ j (hj : j < (w v).length),
    (if ((w v)[j]'hj).1 then ((w v)[j]'hj).2 else ((w v)[j]'hj).2 - 1) ∈
      S.grid v ((w v).length - j) ∪ S.grid1 v) ∧
  ∀ v, ∀ j j' : ℕ, ∀ (hj : j < (w v).length) (hj' : j' < (w v).length), j ≠ j' →
    ∀ δ : ℤ, -2 ≤ δ → δ ≤ 2 → 2 < |((w v)[j]'hj).2 - ((w v)[j']'hj').2 + δ|
def AdmN (w : Word S.f) : Prop := S.admitted w ∧ w.cnt ≤ S.Ntop
abbrev W := {w : Word S.f // S.AdmN w}
def empW : S.W := ⟨Word.emp S.f, by simp [AdmN, admitted, Word.emp, Word.cnt]⟩
def nodes (v : Fin S.f) : Finset ℝ := (range (S.Ntop + 1)).biUnion (S.grid v) ∪ S.grid1 v
def pts (v : Fin S.f) : Finset ℝ := S.nodes v ∪ (S.nodes v).image (· + 1)
def mkData (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ) (hK0 : Kr 0 [] [] = 1)
    (Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ) (e : ℕ → ℝ) : TB.Data E S.W where
  r := S.G.r
  f := S.f
  K := Kst
  av v l := S.pl v l
  wt w := Word.size S.P w.1
  cnt w := w.1.cnt
  Wall := (wall S.pts S.Ntop).subtype S.AdmN
  emp := S.empW
  emp_mem := by
    rw [Finset.mem_subtype]
    simp only [empW, wall, Fintype.mem_piFinset, listsUpTo, mem_biUnion, mem_range, mem_image]
    intro v
    exact ⟨0, by omega, Fin.elim0, by simp, by simp [Word.emp]⟩
  cnt_emp := by simp [empW, Word.cnt, Word.emp]
  wt_emp := by simp [empW, Word.size, Word.emp]
  gram ε i w := S.gram ε i w.1
  Kr := Kr
  K0 := hK0
  Th := Th
  e := e
  La b s := J.LaB E S.g S.G.r b s
  Lap b s := J.LapB E S.g S.G.r b s
  Lad b := J.LadB E S.g S.G.r b
  Nhat ε i w := S.Nhat ε i w.1
  szD b v := J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b 1 (S.pl v)
  szL b s v := if b + s ≤ S.G.r + 1 then J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b (s + 1) (S.pl v)
    else 2 * J.thrP S.G S.CA S.de S.de' S.T S.T' S.l b (S.pl v)
  vol b s := (∏ w, J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w) ^ 2 /
    (FractionalIdeal.absNorm (S6.dualIdl E S.g (S6.nuBlock S.G.r b s)) : ℝ)
def base : TB.Data E S.W :=
  S.mkData (fun i _ _ => if i = 0 then 1 else 0) (by simp) (fun _ _ _ _ _ => 0) (fun _ => 0)
def sizeAt (v : Fin S.f) (a : List Letter) : ℝ := (a.map fun x => |S.P v x.2|).prod
def bigPlaces (i : ℕ) (l : E) : Finset (Fin S.f) :=
  univ.filter fun v => J.thrS S.G S.CA S.de S.de' S.T S.T' S.l i 1 (S.pl v) < S.pl v l
end HidaSetting
section abelianHodgeDeRham'
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
def ThmPPos (S : HidaSetting E Wp Wq) : Prop :=
  ∀ v, ∀ ε, 0 < ε → ∀ i, i ≤ S.G.r + 1 → ∀ w : S.W, ∀ Y : Finset LPt,
    TB.PSDOn Y (S.gramLoc v ε i (w.1 v))
def GridsOK (S : HidaSetting E Wp Wq) : Prop :=
  ∀ v,
    6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop ≤ S.cutHi v - S.cutLo v ∧
    (∀ a, ∀ y ∈ S.grid v a, 1 ≤ a ∧ a ≤ S.Ntop ∧ gridL (S.cutLo v) (S.cutHi v) S.Ntop a ≤ y ∧
      y ≤ gridL (S.cutLo v) (S.cutHi v) S.Ntop a + (S.cutHi v - S.cutLo v) / (6 * S.Ntop) - 1) ∧
    (∀ y ∈ S.grid1 v, y ∈ (S.G.place (S.pl v)).cutIntervalLong S.l S.Ntop ∧
      y + 1 ∈ (S.G.place (S.pl v)).cutIntervalLong S.l S.Ntop) ∧
    (∀ y ∈ S.grid1 v, ∀ y' ∈ S.grid1 v, y ≠ y' → ∀ e ∈ ({0, 1} : Finset ℝ), ∀ e' ∈ ({0, 1} : Finset ℝ),
      (S.Ntop : ℝ) ^ 2 / 8 ≤ |(y + e) - (y' + e')|) ∧
    (∀ y ∈ S.grid1 v, ∀ a, ∀ y' ∈ S.grid v a, ∀ e ∈ ({0, 1} : Finset ℝ), ∀ e' ∈ ({0, 1} : Finset ℝ),
      (S.Ntop : ℝ) ^ 2 + 1 ≤ |(y + e) - (y' + e')|) ∧
    (∀ y, ((∃ a, y ∈ S.grid v a) ∨ y ∈ S.grid1 v) →
      y ∈ (S.G.place (S.pl v)).cutI S.l ∧ y + 1 ∈ (S.G.place (S.pl v)).cutI S.l ∧
        S.P v y ≠ 0 ∧ S.P v (y + 1) ≠ 0)
def ThmPInt (S : HidaSetting E Wp Wq) : Prop :=
  ∀ ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ w : S.W, ∀ Y : Finset (TB.Pt E),
    (∀ h ∈ Y, TB.level h = i - 1) → ∀ κ, TB.PSDOn Y κ →
      (∃ φ : J.CV E → ℂ, Continuous φ ∧
        (∀ c : J.CV E, (∀ v, c (S.pl v) ≠ 0) → φ c = S.N1 ε i w.1 Y κ c) ∧
        ∃ Cφ : ℝ, ∀ c : J.CV E, ‖φ c‖ ≤ Cφ * ∏ v, ((1 + ‖c (S.pl v)‖) ^ 3)⁻¹) ∧
      S.Nhat ε i w.1 Y κ 0 = (S.base.N0 ε (i - 1) w Y κ : ℂ)
def PlaneWaveBoundAllPlaces (S : HidaSetting E Wp Wq) : Prop :=
  ∀ ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ w ∈ S.base.Wall, S.base.cnt w + Kst ≤ S.Ntop →
    ∃ θ : Finset (Fin S.f) → S.W → ℝ, (∀ A, TB.IsProb (S.base.Wb (S.base.cnt w + Kst)) (θ A)) ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ l ∈ S.base.Lad i, l ≠ 0 →
          ‖S.Nhat ε i w.1 Y κ l‖ ≤ S.base.maj (S.base.szD i) l *
            ∑ w' ∈ S.base.Wb (S.base.cnt w + Kst), θ (S.bigPlaces i l) w' * S.base.N0 ε (i - 1) w' Y κ
def OffDiagonalLiftBound (S : HidaSetting E Wp Wq) : Prop := S.base.EstLift
def CorollaryT (S : HidaSetting E Wp Wq) (C₄ : ℝ) : Prop := S.base.EstBlock C₄
def LemmaE (S : HidaSetting E Wp Wq) (jv : Fin S.f → ℝ) : Prop :=
  ∀ w : S.W, ∀ v,
    Tendsto (fun ε => (S.pd v).RR ε 0 (w.1 v) [] []) (𝓝[>] 0)
      (𝓝 ((S.sizeAt v (w.1 v) * jv v : ℝ) : ℂ))
def EnergyLinkC [∀ x, FiniteDimensional ℂ (Wq x)] (S : HidaSetting E Wp Wq) (jv cE : Fin S.f → ℝ) : Prop :=
  ∀ v, 0 < cE v ∧ B.normSq (S.pd v).bs (S.pd v).f0 ≠ ⊤ ∧
    jv v = cE v * (B.normSq (S.pd v).bs (S.pd v).f0).toReal
def PropGram (S : HidaSetting E Wp Wq) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Vt : TB.Pt E → H) : Prop :=
  ∀ Y : Finset (TB.Pt E), (∀ p ∈ Y, TB.IsPt p (S.G.r + 1)) →
    ∀ᶠ ε in 𝓝[>] 0, ∀ p ∈ Y, ∀ q ∈ Y,
      S.gram ε (S.G.r + 1) (Word.emp S.f) p q = inner ℂ (Vt q) (Vt p)
end abelianHodgeDeRham'
def GramPSDOfParts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : HidaSetting E Wp Wq),
    ThmPPos S → GridsOK S → ∀ Kr hK0 Th e, (S.mkData Kr hK0 Th e).GramPSD
def WordsPosOfParts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : HidaSetting E Wp Wq),
    GridsOK S → ∀ Kr hK0 Th e, (S.mkData Kr hK0 Th e).WordsPos
def EstWaveOfParts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : HidaSetting E Wp Wq),
    GridsOK S → ThmPInt S → PlaneWaveBoundAllPlaces S → ∀ Kr hK0 Th e, (S.mkData Kr hK0 Th e).EstWave
def PoissonInputOfParts : Prop :=
  J.EmbFacts → J.EuclidFrame → J.TraceDual → S6.LatticesGeneral →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : HidaSetting E Wp Wq),
    0 < S.G.g1 → 0 < S.G.g2 → ThmPPos S → GridsOK S → ThmPInt S →
    ∀ Kr hK0 Th e, PB.PoissonInput (S.mkData Kr hK0 Th e)
def EstLiftOfParts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : HidaSetting E Wp Wq),
    OffDiagonalLiftBound S → ∀ Kr hK0 Th e, (S.mkData Kr hK0 Th e).EstLift
def EstBlockOfParts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : HidaSetting E Wp Wq)
    (C₄ : ℝ), CorollaryT S C₄ → ∀ Kr hK0 Th e, (S.mkData Kr hK0 Th e).EstBlock C₄
def EstEOfParts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : HidaSetting E Wp Wq) (jv : Fin S.f → ℝ), GridsOK S → LemmaE S jv →
    ∀ Kr hK0 Th e, (S.mkData Kr hK0 Th e).EstE (∏ v, jv v)
def CutoffOfParts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : HidaSetting E Wp Wq)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H), PropGram S Vt →
    ∀ Kr hK0 Th e, (S.mkData Kr hK0 Th e).Cutoff Vt
def RealInputsConcrete : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : HidaSetting E Wp Wq) (jv : Fin S.f → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Vt : TB.Pt E → H) (C₄ : ℝ),
    0 < S.G.g1 → 0 < S.G.g2 →
    ThmPPos S → GridsOK S → ThmPInt S → PlaneWaveBoundAllPlaces S → OffDiagonalLiftBound S → CorollaryT S C₄ → LemmaE S jv →
    PropGram S Vt →
    ∀ Kr hK0 Th e, PB.RealInputs (S.mkData Kr hK0 Th e) C₄ (∏ v, jv v) Vt
def RealInputsConcreteOfParts : Prop :=
  J.EmbFacts → J.EuclidFrame → J.TraceDual → S6.LatticesGeneral →
  GramPSDOfParts → WordsPosOfParts → EstWaveOfParts → PoissonInputOfParts → EstLiftOfParts →
  EstBlockOfParts → EstEOfParts → CutoffOfParts → RealInputsConcrete
def TheoremAConcrete : Prop :=
  ∀ C₁ C₄ : ℝ, 1 ≤ C₁ → 1 ≤ C₄ → ∃ C C' : ℝ,
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : HidaSetting E Wp Wq) (jv cE : Fin S.f → ℝ) (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ) (hK0 : Kr 0 [] [] = 1)
    (Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ) (e : ℕ → ℝ) (Θ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : TB.Pt E → H)
    (c : ℕ → TB.Pt E → ℂ),
    1 ≤ S.f → 0 < S.G.g1 → 0 < S.G.g2 → 0 < Θ → C' ≤ Θ → ((S.G.r : ℝ) + 1) * (C / Θ) ^ S.f ≤ 1 →
    (S.mkData Kr hK0 Th e).SizesBelow Θ →
    ThmPPos S → GridsOK S → ThmPInt S → PlaneWaveBoundAllPlaces S → OffDiagonalLiftBound S → CorollaryT S C₄ → LemmaE S jv →
    EnergyLinkC S jv cE → PropGram S Vt →
    TC.KrPSD (S.mkData Kr hK0 Th e) → (S.mkData Kr hK0 Th e).KernelSupport → TC.EBounds (S.mkData Kr hK0 Th e) →
    TC.DomAfter (S.mkData Kr hK0 Th e) →
    (S.mkData Kr hK0 Th e).LatticeSums ((C₁ * Θ ^ (-((Kst : ℝ) - 5 / 2))) ^ S.f) →
    (S.mkData Kr hK0 Th e).LeadingDomination Vt c →
    ∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤
      (1 + C * ((S.G.r : ℝ) + 1) * (C / Θ) ^ S.f) * (∏ i ∈ Icc 1 (S.G.r + 1), (1 + e i)) * ∏ v, jv v
def TheoremAConcreteOfParts : Prop :=
  TC.TheoremAAfter → F7.PoissonStepText → J.PoissonJoint → J.PoissonStepJoint → RealInputsConcrete →
  TheoremAConcrete
end
end Formalism.FourierDecayAlt.C


