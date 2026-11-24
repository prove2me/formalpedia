-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementMA
-- name    : Formalism_HermitianCurvature_StatementMA
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:45:28.369922+00:00
-- url     : https://prove2.me/theorems/891056ba-ccb1-4951-98ad-896aefa61ff0
-- title:
--   Statement MA
-- statement:
--   Definitions and structural lemmas for Statement MA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementMA.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.MA
open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr MeasureTheory
open scoped ComplexConjugate
noncomputable section
structure DAlg (r : ℕ) where

  R : Type
  [cr : CommRing R]
  [alg : Algebra ℂ R]

  x : M.Var r → R

  ev : M.Var r → Module.End ℂ R
attribute [instance] DAlg.cr DAlg.alg
namespace DAlg
variable {r : ℕ} (D : DAlg r)
def gg (TT : ℝ) : D.R := D.x M.vz * D.x M.vzb - algebraMap ℂ D.R (TT : ℂ)
def inv (f : D.R) : D.R := Ring.inverse f
structure Laws (TT : ℝ) : Prop where
  leibniz : ∀ v f g, D.ev v (f * g) = D.ev v f * g + f * D.ev v g
  coord : ∀ v w, D.ev v (D.x w) = if v = w then D.x w else 0
  comm : ∀ v w, D.ev v * D.ev w = D.ev w * D.ev v
  unit_alt_bis : ∀ v, IsUnit (D.x v)
  unit_gg : IsUnit (D.gg TT)
  nontrivial : Nontrivial D.R
abbrev Op : Type := Module.End ℂ D.R
def Pr : Type := D.Op × D.Opᵐᵒᵖ
instance : Ring D.Pr := inferInstanceAs (Ring (D.Op × D.Opᵐᵒᵖ))
instance : Algebra ℂ D.Pr :=
  RingHom.toAlgebra' ((algebraMap ℂ D.Op).prod ((algebraMap ℂ D.Opᵐᵒᵖ).comp (starRingEnd ℂ)))
    (fun z x => Prod.ext (Algebra.commutes z x.1) (Algebra.commutes (starRingEnd ℂ z) x.2))
instance : StarRing D.Pr where
  star x := (x.2.unop, MulOpposite.op x.1)
  star_involutive _ := rfl
  star_mul _ _ := rfl
  star_add _ _ := rfl
instance : StarModule ℂ D.Pr where
  star_smul z x := by
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, Algebra.commutes]
    congr 1
    refine Prod.ext ?_ ?_
    · show ((algebraMap ℂ D.Opᵐᵒᵖ) (starRingEnd ℂ z)).unop = algebraMap ℂ D.Op (star z)
      rfl
    · show MulOpposite.op (algebraMap ℂ D.Op z) = (algebraMap ℂ D.Opᵐᵒᵖ) (starRingEnd ℂ (star z))
      simp
def mulOp (f : D.R) : D.Op := LinearMap.mulLeft ℂ f
def mkP (X Xs : D.Op) : D.Pr := (X, MulOpposite.op Xs)
def fnP (f fb : D.R) : D.Pr := D.mkP (D.mulOp f) (D.mulOp fb)
def cP (l : Fin r) : D.Pr := D.fnP (D.x (M.vc l)) (D.x (M.vcb l))
def ciP (l : Fin r) : D.Pr := D.fnP (D.inv (D.x (M.vc l))) (D.inv (D.x (M.vcb l)))
def cbP (l : Fin r) : D.Pr := D.fnP (D.x (M.vcb l)) (D.x (M.vc l))
def cbiP (l : Fin r) : D.Pr := D.fnP (D.inv (D.x (M.vcb l))) (D.inv (D.x (M.vc l)))
def zP : D.Pr := D.fnP (D.x M.vz) (D.x M.vzb)
def ziP : D.Pr := D.fnP (D.inv (D.x M.vz)) (D.inv (D.x M.vzb))
def zbP : D.Pr := D.fnP (D.x M.vzb) (D.x M.vz)
def zbiP : D.Pr := D.fnP (D.inv (D.x M.vzb)) (D.inv (D.x M.vz))
def ggP (TT : ℝ) : D.Pr := D.fnP (D.gg TT) (D.gg TT)
def ggiP (TT : ℝ) : D.Pr := D.fnP (D.inv (D.gg TT)) (D.inv (D.gg TT))
def pP (l : Fin r) : D.Pr := D.mkP (D.ev (M.vc l)) (-D.ev (M.vcb l))
def pbP (l : Fin r) : D.Pr := D.mkP (D.ev (M.vcb l)) (-D.ev (M.vc l))
def dzP : D.Pr := D.mkP (D.mulOp (D.inv (D.x M.vz)) * D.ev M.vz) (-(D.mulOp (D.inv (D.x M.vzb)) * D.ev M.vzb))
def dzbP : D.Pr := D.mkP (D.mulOp (D.inv (D.x M.vzb)) * D.ev M.vzb) (-(D.mulOp (D.inv (D.x M.vz)) * D.ev M.vz))
def gens (TT : ℝ) : Set D.Pr :=
  Set.range D.cP ∪ Set.range D.ciP ∪ Set.range D.cbP ∪ Set.range D.cbiP ∪ Set.range D.pP ∪ Set.range D.pbP ∪
    {D.zP, D.ziP, D.zbP, D.zbiP, D.ggP TT, D.ggiP TT, D.dzP, D.dzbP}
end DAlg
section Model
variable (P : M.Par) (D : DAlg P.r)
abbrev A : Type := Matrix (M.Ty P) (M.Ty P) D.Pr
def sc (w : D.Pr) : A P D := Matrix.scalar (M.Ty P) w
def kap : (M.Ty P → ℂ) →ₐ[ℂ] A P D :=
  (Matrix.diagonalAlgHom ℂ).comp ((Algebra.ofId ℂ D.Pr).compLeft (M.Ty P))
def pA (l : Fin P.r) : A P D := sc P D (D.pP l)
def pbA (l : Fin P.r) : A P D := sc P D (D.pbP l)
def cA (l : Fin P.r) : A P D := sc P D (D.cP l)
def ciA (l : Fin P.r) : A P D := sc P D (D.ciP l)
def cbA (l : Fin P.r) : A P D := sc P D (D.cbP l)
def cbiA (l : Fin P.r) : A P D := sc P D (D.cbiP l)
def zA : A P D := sc P D D.zP
def ziA : A P D := sc P D D.ziP
def zbA : A P D := sc P D D.zbP
def zbiA : A P D := sc P D D.zbiP
def ggA : A P D := sc P D (D.ggP P.TT)
def ggiA : A P D := sc P D (D.ggiP P.TT)
def nabA : A P D := Matrix.diagonal fun π => D.dzP + (M.aC P π : ℂ) • (D.zbP * D.ggiP P.TT)
def nabsA : A P D := Matrix.diagonal fun π => -D.dzbP + (M.aC P π : ℂ) • (D.zP * D.ggiP P.TT)
def IsModelLevel (L : LevelData (A P D) P.r) : Prop :=
  L.p = pA P D ∧ L.pb = pbA P D ∧ L.c = cA P D ∧ L.ci = ciA P D ∧ L.cb = cbA P D ∧ L.cbi = cbiA P D ∧
    L.ζ = zA P D ∧ L.ζi = ziA P D ∧ L.ζb = zbA P D ∧ L.ζbi = zbiA P D ∧ L.GG = ggA P D ∧ L.GGi = ggiA P D ∧
    L.nab = nabA P D ∧ L.nabs = nabsA P D ∧ L.TT = (P.TT : ℂ)
def SS (l : ℕ) : A P D :=
  Matrix.of fun π' π => if M.Up P l π π' then algebraMap ℂ D.Pr ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) else 0
def l0A (Y : ℂ) : A P D := -nabA P D - algebraMap ℂ (A P D) (Y + 1 / 2) * (zbA P D * ggiA P D)
def m0A (Y : ℂ) : A P D := -nabsA P D - algebraMap ℂ (A P D) (Y - 1 / 2) * (zA P D * ggiA P D)
def xA (Y : ℂ) : A P D := kap P D fun π => M.xC P π Y
def weightedSumBis (Y : ℂ) : A P D := ∑ l ∈ Icc 1 (P.k - 1), SS P D l * kap P D fun π => M.xEx P {l} π Y
def S12 (Y : ℂ) : A P D := ∑ l ∈ Icc 1 (P.k - 1), (kap P D fun π => M.xEx P {l} π Y) * star (SS P D l)
def S4 (Y : ℂ) : A P D :=
  ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ (Icc 1 (P.k - 1)).erase l,
    star (SS P D l) * SS P D j * kap P D fun π => M.xEx P {l, j} π Y
def t22 (Y : ℂ) : A P D := ggA P D * xA P D Y
def t21 (Y : ℂ) : A P D := ggA P D * xA P D Y * l0A P D Y + weightedSumBis P D Y
def t12 (Y : ℂ) : A P D := ggA P D * xA P D Y * m0A P D Y + S12 P D Y
def t11 (Y : ℂ) : A P D :=
  ggiA P D * (kap P D fun π => M.wC P π Y) + ggA P D * xA P D Y * m0A P D Y * l0A P D Y +
    ggA P D * m0A P D Y * ggiA P D * weightedSumBis P D Y + S12 P D Y * l0A P D Y + ggiA P D * S4 P D Y
def QQr (Y : ℂ) : M2 (A P D) := !![t11 P D Y, t12 P D Y; t21 P D Y, t22 P D Y]
def eeA (Y : ℂ) : A P D :=
  zA P D * zbiA P D * ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (M.rho P π j : ℂ))⁻¹) * SS P D j
def startM (l : ℕ) : Start (A P D) where
  QQ Y := M.sgn P l • QQr P D Y
  q := M.qC P
  x Y := kap P D fun π => M.x0 P l π Y
  xi Y := kap P D fun π => (M.x0 P l π Y)⁻¹
  ee := eeA P D
  inv := {Y | ∀ π, M.xC P π Y ≠ 0}
def siteA (l : Fin P.r) : Site (A P D) := ⟨pA P D l, cA P D l, ciA P D l⟩
def sites : List (Site (A P D)) := (List.ofFn (siteA P D)).reverse
def FrameConcl (l : ℕ) (L : LevelData (A P D) P.r) {S : Type} [Fintype S] [DecidableEq S]
    (w : List (Letter ℂ S)) : Prop :=
  IsFrame L (ofWord L (startM P D l) w) ∧
  RRw (startM P D l).QQ w = star (ofWord L (startM P D l) w).F *
    (wt L ^ w.length * (ofWord L (startM P D l) w).c) * (ofWord L (startM P D l) w).F ∧
  (ofWord L (startM P D l) w).c = (Matrix.diagonal fun e => kap P D fun π => cs (M.x0 P l π) (M.qC P) w e) ∧
  ∀ (e : Ix S) (π : M.Ty P), Pos (cs (M.x0 P l π) (M.qC P) w e)
end Model
def hahn (r : ℕ) : DAlg r where
  R := M.Fn r
  x := M.coord
  ev := M.euler
abbrev E (r : ℕ) : Type := (Fin r → ℂ) × ℂ
def Qset (r : ℕ) (TT : ℝ) : Set (E r) := {x | (∀ l, x.1 l ≠ 0) ∧ TT < Complex.normSq x.2}
theorem Qset_open (r : ℕ) (TT : ℝ) : IsOpen (Qset r TT) := by
  have h1 : IsOpen {x : E r | ∀ l, x.1 l ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun l =>
      isOpen_ne_fun ((continuous_apply l).comp continuous_fst) continuous_const
  have h2 : IsOpen {x : E r | TT < Complex.normSq x.2} :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd)
  exact h1.inter h2
abbrev Qp (r : ℕ) (TT : ℝ) : Type := ↥(Qset r TT)
def sm : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)
open scoped Classical in

def ext {r : ℕ} {TT : ℝ} (f : Qp r TT → ℂ) : E r → ℂ :=
  fun x => if h : x ∈ Qset r TT then f ⟨x, h⟩ else 0
def smSub (r : ℕ) (TT : ℝ) : Subalgebra ℂ (Qp r TT → ℂ) where
  carrier := {f | ContDiffOn ℝ sm (ext f) (Qset r TT)}
  mul_mem' {f g} hf hg := (hf.mul hg).congr fun x hx => by simp [ext, hx]
  add_mem' {f g} hf hg := (hf.add hg).congr fun x hx => by simp [ext, hx]
  algebraMap_mem' z := (contDiffOn_const (c := z)).congr fun x hx => by simp [ext, hx]
abbrev SmQ (r : ℕ) (TT : ℝ) : Type := ↥(smSub r TT)
variable {r : ℕ} {TT : ℝ}
def zE (v : M.Var r) (x : E r) : ℂ := if h : ((ofLex v).1 : ℕ) < r then x.1 ⟨_, h⟩ else x.2
def coordE (v : M.Var r) (x : E r) : ℂ := if (ofLex v).2 = 0 then zE v x else conj (zE v x)
def dirE (v : M.Var r) : E r :=
  if h : ((ofLex v).1 : ℕ) < r then (Pi.single ⟨_, h⟩ 1, 0) else (0, 1)
def wirt (v : M.Var r) (f : E r → ℂ) (x : E r) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f x (dirE v) +
    (if (ofLex v).2 = 0 then -Complex.I else Complex.I) * fderiv ℝ f x (Complex.I • dirE v))
theorem coordE_smooth (v : M.Var r) : ContDiff ℝ sm (coordE v) := by
  have hz : ContDiff ℝ sm (zE v) := by
    by_cases h : ((ofLex v).1 : ℕ) < r
    · have he : zE v = fun x : E r => x.1 ⟨_, h⟩ := by
        funext x
        simp [zE, h]
      rw [he]
      exact (contDiff_pi.mp contDiff_id (⟨_, h⟩ : Fin r)).comp contDiff_fst
    · have he : zE v = fun x : E r => x.2 := by
        funext x
        simp [zE, h]
      rw [he]
      exact contDiff_snd
  by_cases h : (ofLex v).2 = 0
  · have he : coordE v = zE v := by
      funext x
      simp [coordE, h]
    rw [he]
    exact hz
  · have he : coordE v = Complex.conjCLE ∘ zE v := by
      funext x
      simp [coordE, h]
    rw [he]
    exact Complex.conjCLE.contDiff.comp hz
theorem ext_smooth_diff {f : Qp r TT → ℂ} (hf : f ∈ smSub r TT) (x : E r) (hx : x ∈ Qset r TT) :
    DifferentiableAt ℝ (ext f) x := by
  have h1 : ContDiffOn ℝ sm (ext f) (Qset r TT) := hf
  have hn : sm ≠ 0 := by
    unfold sm
    simp
  exact (h1.contDiffAt ((Qset_open r TT).mem_nhds hx)).differentiableAt hn
theorem wirt_smooth {f : Qp r TT → ℂ} (hf : f ∈ smSub r TT) (v : M.Var r) :
    ContDiffOn ℝ sm (wirt v (ext f)) (Qset r TT) := by
  have hf' : ContDiffOn ℝ sm (ext f) (Qset r TT) := hf
  have hd : ContDiffOn ℝ sm (fun y => fderiv ℝ (ext f) y) (Qset r TT) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen (Qset_open r TT)).mp hf').2
  have h1 : ContDiffOn ℝ sm (fun y => fderiv ℝ (ext f) y (dirE v)) (Qset r TT) :=
    hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ sm (fun y => fderiv ℝ (ext f) y (Complex.I • dirE v)) (Qset r TT) :=
    hd.clm_apply contDiffOn_const
  exact contDiffOn_const.mul (h1.add (contDiffOn_const.mul h2))
def coordQ (v : M.Var r) : SmQ r TT :=
  ⟨fun q => coordE v q.1, ((coordE_smooth v).contDiffOn).congr fun x hx => by simp [ext, hx]⟩
def eulerQ (v : M.Var r) : Module.End ℂ (SmQ r TT) where
  toFun f := ⟨fun q => coordE v q.1 * wirt v (ext f.1) q.1,
    (((coordE_smooth v).contDiffOn).mul (wirt_smooth f.2 v)).congr fun x hx => by simp [ext, hx]⟩
  map_add' f g := by
    apply Subtype.ext; funext q
    have he : ext ((f : Qp r TT → ℂ) + (g : Qp r TT → ℂ)) = ext f.1 + ext g.1 := by
      funext x; by_cases hx : x ∈ Qset r TT <;> simp [ext, hx]
    simp only [Subalgebra.coe_add, Pi.add_apply]
    rw [he]
    simp only [wirt, fderiv_add (ext_smooth_diff f.2 q.1 q.2) (ext_smooth_diff g.2 q.1 q.2),
      _root_.add_apply]
    ring
  map_smul' z f := by
    apply Subtype.ext; funext q
    have he : ext (z • (f : Qp r TT → ℂ)) = z • ext f.1 := by
      funext x; by_cases hx : x ∈ Qset r TT <;> simp [ext, hx]
    simp only [Subalgebra.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [he]
    simp only [wirt, fderiv_const_smul (ext_smooth_diff f.2 q.1 q.2) z, _root_.smul_apply,
      smul_eq_mul]
    ring
def anQ (r : ℕ) (TT : ℝ) : DAlg r where
  R := SmQ r TT
  x := coordQ
  ev := eulerQ
def dens0 (x : E r) : ENNReal := ∏ l, ENNReal.ofReal (Complex.normSq (x.1 l))⁻¹
def mu0 (r : ℕ) (TT : ℝ) : Measure (Qp r TT) := Measure.comap Subtype.val ((volume : Measure (E r)).withDensity dens0)
def Mdim (k r : ℕ) (l : Fin r) : ℕ := 2 * (r - (l : ℕ)) + k + 1
def wq (k : ℕ) (x : E r) (TT : ℝ) : ℝ :=
  (∏ l, Complex.normSq (x.1 l) ^ (Mdim k r l - 1)) * (Complex.normSq x.2 - TT) ^ (k - 1)
def muq (k r : ℕ) (TT : ℝ) : Measure (Qp r TT) :=
  Measure.comap Subtype.val ((volume : Measure (E r)).withDensity fun x => dens0 x * ENNReal.ofReal (wq k x TT))
def Test (r : ℕ) (TT : ℝ) : Set (SmQ r TT) :=
  {f | HasCompactSupport (ext (f : Qp r TT → ℂ)) ∧ tsupport (ext (f : Qp r TT → ℂ)) ⊆ Qset r TT}
def ip0 (f g : SmQ r TT) : ℂ := ∫ q, (f : Qp r TT → ℂ) q * conj ((g : Qp r TT → ℂ) q) ∂mu0 r TT
def IsAdj (a : (anQ r TT).Pr) : Prop :=
  (∀ f ∈ Test r TT, a.1 f ∈ Test r TT) ∧ (∀ g ∈ Test r TT, a.2.unop g ∈ Test r TT) ∧
    ∀ f ∈ Test r TT, ∀ g ∈ Test r TT, ip0 (a.1 f) g = ip0 f (a.2.unop g)
section Energy
variable (P : M.Par)
abbrev DQ : DAlg P.r := anQ P.r P.TT
def actA (a : A P (DQ P)) (f : M.Ty P → SmQ P.r P.TT) : M.Ty P → SmQ P.r P.TT :=
  fun π => ∑ π', (a π π').1 (f π')
def ipA (f g : M.Ty P → SmQ P.r P.TT) : ℂ := ∑ π, ip0 (f π) (g π)
def IsAdjA (a : A P (DQ P)) : Prop := ∀ π π', IsAdj (a π π')
def Gq (q : Qp P.r P.TT) : ℝ := (∏ l, Complex.normSq (q.1.1 l)) * (Complex.normSq q.1.2 - P.TT)
def Wq (q : Qp P.r P.TT) : ℝ := Complex.normSq q.1.2 / (Complex.normSq q.1.2 - P.TT)
theorem Gq_pos (q : Qp P.r P.TT) : 0 < Gq P q := by
  have hq : (∀ l, q.1.1 l ≠ 0) ∧ P.TT < Complex.normSq q.1.2 := q.2
  exact mul_pos (Finset.prod_pos fun l _ => Complex.normSq_pos.mpr (hq.1 l)) (sub_pos.mpr hq.2)
theorem Gq_meas : Measurable (Gq P) := by
  apply Continuous.measurable
  exact (continuous_finset_prod _ fun l _ => Complex.continuous_normSq.comp
      ((continuous_apply l).comp (continuous_fst.comp continuous_subtype_val))).mul
    ((Complex.continuous_normSq.comp (continuous_snd.comp continuous_subtype_val)).sub continuous_const)
def baseQ : LE.Base where
  Ω := Qp P.r P.TT
  μ := mu0 P.r P.TT
  G := Gq P
  G_pos := Gq_pos P
  G_meas := Gq_meas P
def Iota : ℕ → Type
  | 0 => M.Ty P
  | N + 1 => Bool × Iota N
@[reducible] def iotaFintype : (N : ℕ) → Fintype (Iota P N)
  | 0 => inferInstanceAs (Fintype (M.Ty P))
  | N + 1 => @instFintypeProd Bool (Iota P N) _ (iotaFintype N)
instance (N : ℕ) : Fintype (Iota P N) := iotaFintype P N
def ixOf : (N : ℕ) → Iota P N → Ix (Fin N) × M.Ty P
  | 0, π => (fun i => i.elim0, π)
  | N + 1, (b, i) => (Fin.snoc (α := fun _ => Fin 2) (ixOf N i).1 (if b then 1 else 0), (ixOf N i).2)
def iotaOf : (N : ℕ) → Ix (Fin N) → M.Ty P → Iota P N
  | 0, _, π => π
  | N + 1, e, π => (decide (e (Fin.last N) = 1), iotaOf N (Fin.init e) π)
def wordS : (w : List (Bool × ℝ)) → List (Letter ℂ (Fin w.length))
  | [] => []
  | x :: w => ⟨x.1, Fin.last w.length, (x.2 : ℂ)⟩ ::
      (wordS w).map fun lt => ⟨lt.plus, lt.intersection_update_fsHerm_neg_one.castSucc, lt.pt⟩
def wordP (w : List ℝ) : List (Letter ℂ (Fin w.length)) :=
  (wordS (LE.plus w)).map fun lt => ⟨lt.plus, Fin.cast (by simp [LE.plus]) lt.intersection_update_fsHerm_neg_one, lt.pt⟩
open scoped Classical in

def toSm (u : Qp P.r P.TT → ℂ) : SmQ P.r P.TT := if h : u ∈ smSub P.r P.TT then ⟨u, h⟩ else 0
def evQ (f : SmQ P.r P.TT) : Qp P.r P.TT → ℂ := f.1
def wordModuleApply {N : ℕ} (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (X : Qp P.r P.TT → Iota P N → ℂ) :
    Qp P.r P.TT → Iota P N → ℂ :=
  fun q i => ∑ e', ∑ π', evQ P (((b (ixOf P N i).1 e') (ixOf P N i).2 π').1 (toSm P fun q' => X q' (iotaOf P N e' π'))) q
def ptMat {N : ℕ} (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (q : Qp P.r P.TT) : Matrix (Iota P N) (Iota P N) ℂ :=
  fun i i' => evQ P (((b (ixOf P N i).1 (ixOf P N i').1) (ixOf P N i).2 (ixOf P N i').2).1 1) q
variable (l : ℕ) (L : LevelData (A P (DQ P)) P.r)
def frW (w : List ℝ) : FrameData (Fin w.length) (A P (DQ P)) := ofWord L (startM P (DQ P) l) (wordP w)
def g1 (w : List ℝ) (Y : ℝ) : SlopeTestRemainingChoices (Fin w.length) (A P (DQ P)) := io (L.Di * L.Ahat (Y : ℂ))
def g2 (w : List ℝ) (Y : ℝ) : SlopeTestRemainingChoices (Fin w.length) (A P (DQ P)) :=
  io (L.Dbi * L.R0 (Y : ℂ)) + (frW P l L w).ee (Y : ℂ) * io (L.Di * L.Ahat (Y : ℂ))
def gL (w : List ℝ) (Y : ℝ) (X : Qp P.r P.TT → Iota P w.length → ℂ) : Qp P.r P.TT → Iota P (w.length + 1) → ℂ :=
  fun q bi => wordModuleApply P (if bi.1 then g2 P l L w Y else g1 P L w Y) X q bi.2
def gstL (w : List ℝ) (Y : ℝ) (U : Qp P.r P.TT → Iota P (w.length + 1) → ℂ) : Qp P.r P.TT → Iota P w.length → ℂ :=
  fun q i => wordModuleApply P (star (g1 P L w Y)) (fun q' i' => U q' (false, i')) q i +
    wordModuleApply P (star (g2 P l L w Y)) (fun q' i' => U q' (true, i')) q i
def Xw (u : Qp P.r P.TT → M.Ty P → ℂ) : (w : List ℝ) → Qp P.r P.TT → Iota P w.length → ℂ
  | [] => u
  | Y :: w => gL P l L w Y (Xw u w)
def dwW (w : List ℝ) (q : Qp P.r P.TT) (i : Iota P w.length) : ℝ :=
  Wq P q ^ w.length * (cs (M.x0 P l (ixOf P _ i).2) (M.qC P) (wordP w) (ixOf P _ i).1).re
end Energy
section Sys
variable (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT)
  (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β : ℝ) (Lb : ℝ)
def ju : Qp P.r P.TT → M.Ty P → ℂ := fun q π => (j π).1 q
def stepQ (w : List ℝ) : LE.Step (baseQ P) where
  ι := Iota P w.length
  r := P.r
  X := Xw P l L (ju P j) w
  dw := dwW P l w
  g := fun Y => gL P l L w Y
  gst := fun Y => gstL P l L w Y
  d := fun Y => dwW P l (Y :: w)
  ee := fun Y => ptMat P ((frW P l L w).ee (Y : ℂ))
  P := fun Y => ∏ s, (Y + lam s)
  a := α + (β - α) / 3 + 2 * (w.length : ℝ) * Lb
  L := Lb
theorem iota_len (N : ℕ) (Y : Fin N → ℝ) : Iota P N = Iota P (List.ofFn Y).length := by
  rw [List.length_ofFn]
def famPre (N : ℕ) (m : (Fin N → ℝ) → Qp P.r P.TT → Iota P N → ℂ)
    (Bm : (Fin N → ℝ) → Qp P.r P.TT → Matrix (Iota P N) (Iota P N) ℂ) : LE.Fam (baseQ P) N where
  R := M.Ty P
  ι := Iota P N
  r := P.r
  u := ju P j
  gw := fun Y u q i => Xw P l L u (List.ofFn Y) q (cast (iota_len P N Y) i)
  Wt := Wq P
  cw := fun Y i => (cs (M.x0 P l (ixOf P _ (cast (iota_len P N Y) i)).2) (M.qC P) (wordP (List.ofFn Y))
    (ixOf P _ (cast (iota_len P N Y) i)).1).re
  mon := m
  BN := Bm
  J := fun a => Set.Icc (α + (β - α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * Lb)
    (α + (β - α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * Lb + Lb)
def FacOK (N : ℕ) (mB : ((Fin N → ℝ) → Qp P.r P.TT → Iota P N → ℂ) ×
    ((Fin N → ℝ) → Qp P.r P.TT → Matrix (Iota P N) (Iota P N) ℂ)) : Prop :=
  (famPre P l L j α β Lb N mB.1 mB.2).Meas ∧ (famPre P l L j α β Lb N mB.1 mB.2).Factor ∧ (famPre P l L j α β Lb N mB.1 mB.2).BNBounded ∧
    (famPre P l L j α β Lb N mB.1 mB.2).MonPoly
def famQ (N : ℕ) : LE.Fam (baseQ P) N :=
  famPre P l L j α β Lb N (Classical.epsilon (FacOK P l L j α β Lb N)).1 (Classical.epsilon (FacOK P l L j α β Lb N)).2
def chiJ (c : LE.Cut) (ε : ℝ) : M.Ty P → SmQ P.r P.TT :=
  fun π => toSm P fun q => (c.sc ε 1 (Gq P q) : ℂ) * (j π).1 q
def cutoffEnergyForm (c : LE.Cut) (ε : ℝ) (w : List (Bool × ℝ)) : ℝ :=
  (ipA P (actA P ((w.reverse.map fun x => C0 (startM P (DQ P) l).QQ (sites P (DQ P)) (x.2 : ℂ)).prod) (chiJ P j c ε))
    (chiJ P j c ε)).re
def sysQ (c : LE.Cut) (Ntot : ℕ) : LE.Sys where
  B := baseQ P
  c := c
  k := P.k
  r := P.r
  lam := lam
  α := α
  β := β
  Ntot := Ntot
  L := Lb
  principalHermitianLattice := cutoffEnergyForm P l j c
  step := stepQ P l L j lam α β Lb
  fam := famQ P l L j α β Lb
  step_r _ := rfl
  step_P _ _ := rfl
  step_a _ := rfl
  step_L _ := rfl
  step_new _ _ _ := rfl
  fam_r _ := rfl
  fam_J _ _ := rfl
  fam_dens N Y ω := by
    unfold LE.sq
    refine (Fintype.sum_equiv (Equiv.cast (iota_len P N Y)) _ _ fun i => ?_).symm
    simp [famQ, famPre, stepQ, LE.Fam.dw, dwW, List.length_ofFn]
end Sys
end
def HahnLaws : Prop := ∀ (r : ℕ) (TT : ℝ), (hahn r).Laws TT
def HahnJoint : Prop :=
  ∀ P : M.Par, (∀ l, pA P (hahn P.r) l = M.pA P l) ∧ (∀ l, pbA P (hahn P.r) l = M.pbA P l) ∧
    (∀ l, cA P (hahn P.r) l = M.cA P l) ∧ (∀ l, ciA P (hahn P.r) l = M.ciA P l) ∧
    (∀ l, cbA P (hahn P.r) l = M.cbA P l) ∧ (∀ l, cbiA P (hahn P.r) l = M.cbiA P l) ∧
    zA P (hahn P.r) = M.zA P ∧ ziA P (hahn P.r) = M.ziA P ∧ zbA P (hahn P.r) = M.zbA P ∧
    zbiA P (hahn P.r) = M.zbiA P ∧ ggA P (hahn P.r) = M.ggA P ∧ ggiA P (hahn P.r) = M.ggiA P ∧
    nabA P (hahn P.r) = M.nabA P ∧ nabsA P (hahn P.r) = M.nabsA P ∧ (∀ l, SS P (hahn P.r) l = M.SS P l) ∧
    ∀ l, startM P (hahn P.r) l = M.startM P l
def LevelExistsD : Prop :=
  ∀ (P : M.Par) (D : DAlg P.r), D.Laws P.TT → ∃ L : LevelData (A P D) P.r, IsModelLevel P D L
def LevelStarD : Prop :=
  ∀ (P : M.Par) (D : DAlg P.r), D.Laws P.TT → ∀ L : LevelData (A P D) P.r, IsModelLevel P D L → IsStarLevel L
def StartOKD : Prop :=
  ∀ P : M.Par, P.OK → ∀ D : DAlg P.r, D.Laws P.TT → ∀ (l : ℕ) (L : LevelData (A P D) P.r), IsModelLevel P D L →
    IsLevelStart L (startM P D l)
def SitesOKD : Prop :=
  ∀ (P : M.Par) (D : DAlg P.r), D.Laws P.TT → ∀ l : ℕ, SitesOK (K := ℂ) (startM P D l).QQ (sites P D)
def AdmJoint : Prop :=
  ∀ (P : M.Par) (D : DAlg P.r) (l : ℕ) (S : Type) [Fintype S] [DecidableEq S] (w : List (Letter ℂ S)),
    admitted (startM P D l) w ↔ admitted (M.startM P l) w
def ModelFrameD : Prop :=
  ∀ P : M.Par, P.OK → ∀ l, 1 ≤ l → l ≤ P.k → ∀ D : DAlg P.r, D.Laws P.TT →
    ∃ L : LevelData (A P D) P.r, IsModelLevel P D L ∧ IsStarLevel L ∧ IsLevelStart L (startM P D l) ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Letter ℂ S)), M.CutWord P l w → FrameConcl P D l L w
def ModelFrameDOfParts : Prop :=
  I.InterlaceSign → I.QPositive → QPositiveShift → CPos → CPosCut → FrameAll → FrameWord → CDiag →
  M.TyInterlaces → M.RealPoints → M.CutAdm → AdmJoint → LevelExistsD → LevelStarD → StartOKD → ModelFrameD
def ModelWordsD : Prop :=
  ∀ P : M.Par, P.OK → ∀ D : DAlg P.r, D.Laws P.TT → ∀ (l : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (w : List (Letter ℂ S)), Good w →
    (∑ e, ∑ e', star (uw (sites P D) w e) * RRw (startM P D l).QQ w e e' * uw (sites P D) w e' =
      (w.reverse.map fun a => C0 (startM P D l).QQ (sites P D) a.pt).prod) ∧
    ∀ Y, Reg w Y → star Y = Y → ∀ z : Ix S,
      (∑ z', Cw (startM P D l).QQ (sites P D) w Y z z' * uw (sites P D) w z') =
        uw (sites P D) w z * C0 (startM P D l).QQ (sites P D) Y
def AnLeibniz : Prop :=
  ∀ (r : ℕ) (TT : ℝ) (v : M.Var r) (f g : SmQ r TT), eulerQ v (f * g) = eulerQ v f * g + f * eulerQ v g
def AnCoord : Prop :=
  ∀ (r : ℕ) (TT : ℝ) (v w : M.Var r), eulerQ (TT := TT) v (coordQ w) = if v = w then coordQ w else 0
def AnComm : Prop :=
  ∀ (r : ℕ) (TT : ℝ) (v w : M.Var r), (eulerQ v * eulerQ w : Module.End ℂ (SmQ r TT)) = eulerQ w * eulerQ v
def AnUnits : Prop :=
  ∀ (r : ℕ) (TT : ℝ), 0 ≤ TT → (∀ v : M.Var r, IsUnit (coordQ (TT := TT) v)) ∧ IsUnit ((anQ r TT).gg TT)
def AnNontrivial : Prop := ∀ (r : ℕ) (TT : ℝ), Nontrivial (SmQ r TT)
def AnLaws : Prop := ∀ (r : ℕ) (TT : ℝ), 0 ≤ TT → (anQ r TT).Laws TT
def AnLawsOfParts : Prop := AnLeibniz → AnCoord → AnComm → AnUnits → AnNontrivial → AnLaws
def ModelFrameAn : Prop :=
  ∀ P : M.Par, P.OK → ∀ l, 1 ≤ l → l ≤ P.k →
    ∃ L : LevelData (A P (DQ P)) P.r, IsModelLevel P (DQ P) L ∧ IsStarLevel L ∧ IsLevelStart L (startM P (DQ P) l) ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Letter ℂ S)), M.CutWord P l w → FrameConcl P (DQ P) l L w
def ModelFrameAnOfParts : Prop := ModelFrameD → AnLaws → ModelFrameAn
def AdjGens : Prop := ∀ (r : ℕ) (TT : ℝ), 0 ≤ TT → ∀ a ∈ (anQ r TT).gens TT, IsAdj a
def AdjClosed : Prop :=
  ∀ (r : ℕ) (TT : ℝ), IsAdj (1 : (anQ r TT).Pr) ∧
    (∀ a b : (anQ r TT).Pr, IsAdj a → IsAdj b → IsAdj (a + b) ∧ IsAdj (a * b)) ∧
    (∀ (z : ℂ) (a : (anQ r TT).Pr), IsAdj a → IsAdj (z • a)) ∧ ∀ a : (anQ r TT).Pr, IsAdj a → IsAdj (star a)
def AdjAlg : Prop := ∀ (r : ℕ) (TT : ℝ), 0 ≤ TT → ∀ a ∈ Algebra.adjoin ℂ ((anQ r TT).gens TT), IsAdj a
def AdjAlgOfParts : Prop := AdjGens → AdjClosed → AdjAlg
def AdjMatrix : Prop :=
  ∀ (P : M.Par) (a : A P (DQ P)), IsAdjA P a → ∀ f g : M.Ty P → SmQ P.r P.TT, (∀ π, f π ∈ Test P.r P.TT) →
    (∀ π, g π ∈ Test P.r P.TT) → ipA P (actA P a f) g = ipA P f (actA P (star a) g)
def MeasureJoint : Prop :=
  ∀ (k r : ℕ) (TT : ℝ) (f : Qp r TT → ℂ), Measurable f →
    ∫⁻ q, ENNReal.ofReal (‖f q‖ ^ 2) ∂muq k r TT =
      ∫⁻ q, ENNReal.ofReal (‖((Real.sqrt (wq k q.1 TT) : ℝ) : ℂ) * f q‖ ^ 2) ∂mu0 r TT
section EnergyProps
variable (P : M.Par)
def HidaSetting (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β : ℝ) : Prop :=
  P.OK ∧ 1 ≤ l ∧ l ≤ P.k ∧ IsModelLevel P (DQ P) L ∧ C7.LamInterlaces P.k P.r P.u lam ∧
    C7.LamInterlaces P.k P.r P.u' lam ∧ α < β ∧ ∀ Y ∈ Set.Icc α β, I.OnCut P.u P.u' l Y
def hatSet (L : LevelData (A P (DQ P)) P.r) : Set (A P (DQ P)) :=
  Set.range L.Ahat ∪ Set.range L.R0 ∪ Set.range L.Ahatv ∪ Set.range L.R0v
def JDecay (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT) (m : ℕ) : Prop :=
  ∀ w : List (A P (DQ P)), w.length ≤ m → (∀ a ∈ w, a ∈ hatSet P L) → ∀ π,
    Integrable (fun q => ‖evQ P (actA P w.prod j π) q‖ ^ 2) (mu0 P.r P.TT)
def bddSet (L : LevelData (A P (DQ P)) P.r) : Set (A P (DQ P)) :=
  {L.ζi, L.ζbi, L.D * L.Dbi, L.Db * L.Di} ∪ Set.range (kap P (DQ P)) ∪
    (fun i => L.Drb * L.Dri * SS P (DQ P) i) '' Set.Icc 1 (P.k - 1) ∪
    (fun i => star (L.Drb * L.Dri * SS P (DQ P) i)) '' Set.Icc 1 (P.k - 1)
def JAdj (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT) (m : ℕ) : Prop :=
  ∀ (φ : ℝ → ℝ) (ε : ℝ), 0 < ε → LE.SmoothLog φ → (∀ x, x ≤ ε → φ x = 0) →
    (∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C) →
    ∀ b ∈ Submonoid.closure (bddSet P L), ∀ X ∈ hatSet P L, ∀ v w : List (A P (DQ P)), v.length + w.length + 1 ≤ m →
      (∀ a ∈ v ++ w, a ∈ hatSet P L) →
      ipA P (actA P X fun π => toSm P (fun q => (φ (Gq P q) : ℂ)) * actA P (b * v.prod) j π) (actA P w.prod j) =
        ipA P (fun π => toSm P (fun q => (φ (Gq P q) : ℂ)) * actA P (b * v.prod) j π) (actA P (star X * w.prod) j)
def JEigen (j : M.Ty P → SmQ P.r P.TT) (lam : Fin (P.k + 2 * P.r + 1) → ℝ) : Prop :=
  ∀ Y : ℝ, actA P (C0 (QQr P (DQ P)) (sites P (DQ P)) (Y : ℂ)) j = fun π => (∏ s, ((Y : ℂ) + lam s)) • j π
def Hyps (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT) (lam : Fin (P.k + 2 * P.r + 1) → ℝ)
    (α β Lb : ℝ) (Ntot : ℕ) : Prop :=
  HidaSetting P l L lam α β ∧ JDecay P L j (2 * Ntot + 2) ∧ JAdj P L j (2 * Ntot + 2) ∧ JEigen P j lam ∧ P.r + 1 ≤ Ntot ∧ (Ntot : ℝ) ≤ Lb ∧ 2 < Lb ∧
    ((P.k + 2 * P.r + 1 : ℕ) : ℝ) * Lb ≤ β - α ∧ 6 * (Ntot : ℝ) * Lb ≤ β - α
def ForSteps (Φ : ℝ → LE.Cut → LE.Step (baseQ P) → Prop) : Prop :=
  ∀ (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT) (lam : Fin (P.k + 2 * P.r + 1) → ℝ)
    (α β Lb : ℝ) (c : LE.Cut) (Ntot : ℕ), Hyps P l L j lam α β Lb Ntot →
    ∀ w : List ℝ, (sysQ P l L j lam α β Lb c Ntot).OnBoxes w → w.length < Ntot →
      Φ (4 * Ntot) c ((sysQ P l L j lam α β Lb c Ntot).step w)
def ForSys (Φ : LE.Sys → Prop) : Prop :=
  ∀ (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT) (lam : Fin (P.k + 2 * P.r + 1) → ℝ)
    (α β Lb : ℝ) (c : LE.Cut) (Ntot : ℕ), Hyps P l L j lam α β Lb Ntot → Φ (sysQ P l L j lam α β Lb c Ntot)
end EnergyProps
def MeasQ : Prop := ∀ P : M.Par, ForSteps P fun _ _ S => S.Meas
def WPosQ : Prop := ∀ P : M.Par, ForSteps P fun _ _ S => S.WPos
def PRegQ : Prop := ∀ P : M.Par, ForSteps P fun _ _ S => S.PReg
def PRatioQ : Prop := ∀ P : M.Par, ForSteps P fun _ _ S => S.PRatio (Real.exp 3)
def SignedEnergyIdentity : Prop :=
  ∀ (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT)
    (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β Lb : ℝ) (c : LE.Cut) (Ntot : ℕ), Hyps P l L j lam α β Lb Ntot →
    ∀ w : List ℝ, (sysQ P l L j lam α β Lb c Ntot).OnBoxes w → w.length < Ntot →
      ∀ Y ∈ ((sysQ P l L j lam α β Lb c Ntot).step w).J, ∀ ω i,
        ((sysQ P l L j lam α β Lb c Ntot).step w).gst Y
            (fun ω k => (((sysQ P l L j lam α β Lb c Ntot).step w).d Y ω k : ℂ) *
              ((sysQ P l L j lam α β Lb c Ntot).step w).gX Y ω k) ω i =
          (((-1 : ℝ) ^ (P.k - l) * ∏ s, (Y + lam s)) * ((sysQ P l L j lam α β Lb c Ntot).step w).dw ω i : ℝ) *
            ((sysQ P l L j lam α β Lb c Ntot).step w).X ω i
def EnergyAbsoluteIdentity : Prop := ∀ P : M.Par, ForSteps P fun _ _ S => S.I3
def EnergyAbsoluteIdentityFromComponents : Prop := SignedEnergyIdentity → C7.PSign → M.TyInterlaces → LE.BoxesFit → EnergyAbsoluteIdentity
def AdjBQ : Prop := ∀ P : M.Par, ForSteps P fun σ c S => S.AdjB c σ
def JetQ : Prop := ∀ P : M.Par, ForSteps P fun _ _ S => S.Jet
def EnergyPolynomialInParameter : Prop := ∀ P : M.Par, ForSteps P fun _ _ S => S.I4
def I4'Q : Prop := ∀ P : M.Par, ForSteps P fun σ _ S => S.I4' σ
def EnergyShiftDifference : Prop := ∀ P : M.Par, ForSteps P fun _ _ S => S.ShiftFormula
def ResiduesQ : Prop := ∃ CR : ℝ, 0 ≤ CR ∧ ∀ P : M.Par, ForSteps P fun _ _ S => S.Residues CR
def WeightRatioQ : Prop := ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ P : M.Par, ForSteps P fun _ _ S => S.WeightRatio Cd
def StepImportsQ : Prop :=
  ∃ CR Cd CP : ℝ, 0 ≤ CR ∧ 0 ≤ Cd ∧ 0 ≤ CP ∧ ∀ P : M.Par, ForSteps P fun σ c S => S.Imports c σ CR Cd CP
def StepImportsQOfParts : Prop :=
  MeasQ → WPosQ → PRegQ → EnergyAbsoluteIdentity → AdjBQ → JetQ → EnergyPolynomialInParameter → I4'Q → EnergyShiftDifference → ResiduesQ → WeightRatioQ → PRatioQ →
    StepImportsQ
def FactorExistsQ : Prop :=
  ∀ (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT)
    (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β Lb : ℝ) (Ntot : ℕ), Hyps P l L j lam α β Lb Ntot →
    ∀ N, N ≤ Ntot → ∃ mB, FacOK P l L j α β Lb N mB
def FactorChosen : Prop :=
  FactorExistsQ → ∀ (P : M.Par), ForSys P fun S => ∀ N, N ≤ S.Ntot →
    (S.fam N).Meas ∧ (S.fam N).Factor ∧ (S.fam N).BNBounded ∧ (S.fam N).MonPoly
def FamRestQ : Prop :=
  ∀ P : M.Par, ForSys P fun S => ∀ N, N ≤ S.Ntot → (S.fam N).Pos ∧ (S.fam N).Jet
def FamImportsQ : Prop := ∀ P : M.Par, ForSys P fun S => S.FamImports
def FamImportsQOfParts : Prop := FactorExistsQ → FactorChosen → FamRestQ → FamImportsQ
def RootsOutQ : Prop := ∀ P : M.Par, ForSys P fun S => S.RootsOut
def RootsOutQOfParts : Prop := C7.RootsOutJoint → RootsOutQ
def EnergyPolynomialInPoints : Prop := ∀ P : M.Par, ForSys P fun S => S.I1
def SourceSquareIntegrable : Prop := ∀ P : M.Par, ForSys P fun S => S.BaseDensityIntegrable
def EmptyWordEnergyDensity : Prop := ∀ P : M.Par, ForSys P fun S => S.J0
def JnNorm : Prop :=
  ∀ P : M.Par, ∀ (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT)
    (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β Lb : ℝ) (c : LE.Cut) (Ntot : ℕ),
    (sysQ P l L j lam α β Lb c Ntot).jn = ∫ q, ∑ π, ‖(j π : Qp P.r P.TT → ℂ) q‖ ^ 2 ∂mu0 P.r P.TT
def JAdjZero : Prop :=
  ∀ (P : M.Par) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT) (m : ℕ), P.r = 0 → 0 ≤ P.TT →
    IsModelLevel P (DQ P) L → JDecay P L j m → JAdj P L j m
def HypsNonvacuous : Prop :=
  ∀ (Ntot : ℕ) (Lb B : ℝ), 1 ≤ Ntot → (Ntot : ℝ) ≤ Lb → 2 < Lb →
    ∃ (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT)
      (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β : ℝ), Hyps P l L j lam α β Lb Ntot ∧ j ≠ 0 ∧ B ≤ β - α
noncomputable section ThmPForms
variable (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT) (c : LE.Cut)
def dRing {N : ℕ} (Y : Fin N → ℝ) : SlopeTestRemainingChoices (Fin (List.ofFn Y).length) (A P (DQ P)) :=
  wt L ^ (List.ofFn Y).length * (frW P l L (List.ofFn Y)).c
def gRing {N : ℕ} (Y : Fin N → ℝ) (e : Ix (Fin (List.ofFn Y).length)) : A P (DQ P) :=
  ∑ e', (frW P l L (List.ofFn Y)).F e e' * uw (sites P (DQ P)) (wordP (List.ofFn Y)) e'
def formFdF {N : ℕ} (Y : Fin N → ℝ) (ε : ℝ) : ℝ :=
  (ipA P (actA P (∑ e, ∑ e', star (gRing P l L Y e) * dRing P l L Y e e' * gRing P l L Y e') (chiJ P j c ε))
    (chiJ P j c ε)).re
def formDF {N : ℕ} (Y : Fin N → ℝ) (ε : ℝ) : ℝ :=
  (∑ e, ipA P (actA P (∑ e', dRing P l L Y e e' * gRing P l L Y e') (chiJ P j c ε))
    (actA P (gRing P l L Y e) (chiJ P j c ε))).re
end ThmPForms
def ForWords (Φ : (P : M.Par) → ℕ → LevelData (A P (DQ P)) P.r → (M.Ty P → SmQ P.r P.TT) →
    (Fin (P.k + 2 * P.r + 1) → ℝ) → ℝ → ℝ → ℝ → LE.Cut → ℕ → (N : ℕ) → (Fin N → ℝ) → ℝ → Prop) : Prop :=
  ∀ (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT)
    (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β Lb : ℝ) (c : LE.Cut) (Ntot : ℕ), Hyps P l L j lam α β Lb Ntot →
    ∀ (N : ℕ) (Y : Fin N → ℝ), N ≤ Ntot → (sysQ P l L j lam α β Lb c Ntot).OnBoxes (List.ofFn Y) →
      ∀ ε : ℝ, 0 < ε → Φ P l L j lam α β Lb c Ntot N Y ε
def ThmPForm : Prop :=
  ForWords fun P l L j _ _ _ _ c _ _ Y ε => cutoffEnergyForm P l j c ε (LE.plus (List.ofFn Y)) = formFdF P l L j c Y ε
def ThmPAdj : Prop := ForWords fun P l L j _ _ _ _ c _ _ Y ε => formFdF P l L j c Y ε = formDF P l L j c Y ε
def ThmPGw : Prop :=
  ForWords fun P l L j lam α β Lb c Ntot N Y ε =>
    formDF P l L j c Y ε =
      ∫ ω, LE.sq (baseQ P) (((sysQ P l L j lam α β Lb c Ntot).fam N).dw Y)
        (((sysQ P l L j lam α β Lb c Ntot).fam N).gw Y
          (LE.mulF (baseQ P) (c.sc ε 1) ((sysQ P l L j lam α β Lb c Ntot).fam N).u)) ω ∂(baseQ P).μ
def ThmPQ : Prop := ∀ P : M.Par, ForSys P fun S => S.ThmP
def ThmPQOfParts : Prop := ThmPForm → ThmPAdj → ThmPGw → ThmPQ
def LemmaEModel : Prop :=
  ∃ C₂ C₆ : ℝ, 0 < C₂ ∧ 0 < C₆ ∧
    ∀ (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT)
      (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β : ℝ) (c : LE.Cut) (Ntot : ℕ),
      HidaSetting P l L lam α β → JDecay P L j (2 * Ntot + 2) → JAdj P L j (2 * Ntot + 2) → JEigen P j lam →
      P.r + 1 ≤ Ntot →
      C₆ * ((P.k : ℝ) * Ntot * ((P.r : ℝ) + 1) ^ 2 + (Ntot : ℝ) ^ 2 * ((P.r : ℝ) + 1) ^ 2) ≤ β - α →
      ∀ w : List (Bool × ℝ),
        (sysQ P l L j lam α β (C₂ * Ntot * ((P.r : ℝ) + 1) ^ 2) c Ntot).admitted w → w.length ≤ Ntot →
        Filter.Tendsto (fun ε : ℝ => cutoffEnergyForm P l j c ε w) (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((sysQ P l L j lam α β (C₂ * Ntot * ((P.r : ℝ) + 1) ^ 2) c Ntot).size w *
            ∫ q, ∑ π, ‖(j π : Qp P.r P.TT → ℂ) q‖ ^ 2 ∂mu0 P.r P.TT))
def LemmaEModelOfParts : Prop :=
  LE.LemmaE → LE.Constants → StepImportsQ → FamImportsQ → RootsOutQ → EnergyPolynomialInPoints → SourceSquareIntegrable → ThmPQ → JnNorm → LemmaEModel
end Formalism.FourierDecayAlt.MA


