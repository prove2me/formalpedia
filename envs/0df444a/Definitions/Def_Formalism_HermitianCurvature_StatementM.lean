-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementM
-- name    : Formalism_HermitianCurvature_StatementM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:40:26.674925+00:00
-- url     : https://prove2.me/theorems/1d9cab7d-8c6e-4b7c-9e98-fc95d450a85d
-- title:
--   Statement M
-- statement:
--   Definitions and structural lemmas for Statement M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementM.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.M
open Matrix Finset Polynomial Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
abbrev Var (r : ℕ) : Type := Fin (r + 1) ×ₗ Fin 2
abbrev Expo (r : ℕ) : Type := Lex (Var r → ℤ)
abbrev Fn (r : ℕ) : Type := HahnSeries (Expo r) ℂ
abbrev Op (r : ℕ) : Type := Module.End ℂ (Fn r)
variable {r : ℕ}
def vc (l : Fin r) : Var r := toLex (l.castSucc, 0)
def vcb (l : Fin r) : Var r := toLex (l.castSucc, 1)
def vz : Var r := toLex (Fin.last r, 0)
def vzb : Var r := toLex (Fin.last r, 1)
def coord (v : Var r) : Fn r := HahnSeries.single (toLex (Pi.single v (1 : ℤ))) (1 : ℂ)
def gg (TT : ℝ) : Fn r := coord vz * coord vzb - algebraMap ℂ (Fn r) (TT : ℂ)
def mulOp (f : Fn r) : Op r := LinearMap.mulLeft ℂ f
def euler (v : Var r) : Op r where
  toFun f := ⟨fun γ => ((ofLex γ v : ℤ) : ℂ) * f.coeff γ, f.isPWO_support.mono (by
    intro γ h
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at h
    exact h.2)⟩
  map_add' f g := by ext γ; simp [mul_add]
  map_smul' z f := by ext γ; simp [mul_left_comm]
def Pr (r : ℕ) : Type := Op r × (Op r)ᵐᵒᵖ
instance : Ring (Pr r) := inferInstanceAs (Ring (Op r × (Op r)ᵐᵒᵖ))
instance : Algebra ℂ (Pr r) :=
  RingHom.toAlgebra' ((algebraMap ℂ (Op r)).prod ((algebraMap ℂ (Op r)ᵐᵒᵖ).comp (starRingEnd ℂ)))
    (fun z x => Prod.ext (Algebra.commutes z x.1) (Algebra.commutes (starRingEnd ℂ z) x.2))
instance : StarRing (Pr r) where
  star x := (x.2.unop, MulOpposite.op x.1)
  star_involutive _ := rfl
  star_mul _ _ := rfl
  star_add _ _ := rfl
instance : StarModule ℂ (Pr r) where
  star_smul z x := by
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, Algebra.commutes]
    congr 1
    refine Prod.ext ?_ ?_
    · show ((algebraMap ℂ (Op r)ᵐᵒᵖ) (starRingEnd ℂ z)).unop = algebraMap ℂ (Op r) (star z)
      rfl
    · show MulOpposite.op (algebraMap ℂ (Op r) z) = (algebraMap ℂ (Op r)ᵐᵒᵖ) (starRingEnd ℂ (star z))
      simp
def mk (X Xs : Op r) : Pr r := (X, MulOpposite.op Xs)
def fnP (f fb : Fn r) : Pr r := mk (mulOp f) (mulOp fb)
def cP (l : Fin r) : Pr r := fnP (coord (vc l)) (coord (vcb l))
def ciP (l : Fin r) : Pr r := fnP (coord (vc l))⁻¹ (coord (vcb l))⁻¹
def cbP (l : Fin r) : Pr r := fnP (coord (vcb l)) (coord (vc l))
def cbiP (l : Fin r) : Pr r := fnP (coord (vcb l))⁻¹ (coord (vc l))⁻¹
def zP : Pr r := fnP (coord vz) (coord vzb)
def ziP : Pr r := fnP (coord vz)⁻¹ (coord vzb)⁻¹
def zbP : Pr r := fnP (coord vzb) (coord vz)
def zbiP : Pr r := fnP (coord vzb)⁻¹ (coord vz)⁻¹
def ggP (TT : ℝ) : Pr r := fnP (gg TT) (gg TT)
def ggiP (TT : ℝ) : Pr r := fnP (gg TT)⁻¹ (gg TT)⁻¹
def pP (l : Fin r) : Pr r := mk (euler (vc l)) (-euler (vcb l))
def pbP (l : Fin r) : Pr r := mk (euler (vcb l)) (-euler (vc l))
def dzP : Pr r := mk (mulOp (coord vz)⁻¹ * euler vz) (-(mulOp (coord vzb)⁻¹ * euler vzb))
def dzbP : Pr r := mk (mulOp (coord vzb)⁻¹ * euler vzb) (-(mulOp (coord vz)⁻¹ * euler vz))
structure Par where
  k : ℕ
  r : ℕ
  T : ℝ
  T' : ℝ
  u : ℕ → ℝ
  u' : ℕ → ℝ
namespace Par
variable (P : Par)
def TT : ℝ := P.T * P.T'
def lo (i : ℕ) : ℝ := max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2
def hi (i : ℕ) : ℝ := min (P.u i) (P.u' i) - 1 / 2
def wid (i : ℕ) : ℕ := ⌊P.hi i - P.lo i⌋₊
structure OK : Prop where
  k_pos : 1 ≤ P.k
  T_pos : 0 < P.T
  T'_pos : 0 < P.T'
  int_u : ∀ i ∈ Icc 1 P.k, ∃ n : ℤ, P.u i - P.u 1 = n
  int_u' : ∀ i ∈ Icc 1 P.k, ∃ n : ℤ, P.u' i - P.u 1 = n
  gap : ∀ i ∈ Icc 1 (P.k - 1), P.lo i ≤ P.hi i
end Par
abbrev Ty (P : Par) : Type := (i : Fin (P.k - 1)) → Fin (P.wid ((i : ℕ) + 1) + 1)
variable (P : Par)
def rho (π : Ty P) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ P.k - 1 then P.lo i + (((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) : ℝ) else 0
def Up (l : ℕ) (π π' : Ty P) : Prop :=
  ∀ i : Fin (P.k - 1), ((π' i : Fin _) : ℕ) = ((π i : Fin _) : ℕ) + if (i : ℕ) + 1 = l then 1 else 0
instance (l : ℕ) (π π' : Ty P) : Decidable (Up P l π π') := by unfold Up; infer_instance
def xC (π : Ty P) (Y : ℂ) : ℂ := ∏ i ∈ Icc 1 (P.k - 1), (Y + (rho P π i : ℂ))
def xEx (ex : Finset ℕ) (π : Ty P) (Y : ℂ) : ℂ := ∏ i ∈ Icc 1 (P.k - 1) \ ex, (Y + (rho P π i : ℂ))
def qC (Y : ℂ) : ℂ :=
  -((P.T : ℂ) * P.T') * ∏ i ∈ Icc 1 P.k, ((Y + 1 / 2 + (P.u i : ℂ)) * (Y + 1 / 2 + (P.u' i : ℂ)))
def aC (π : Ty P) : ℝ := (∑ i ∈ Icc 1 P.k, (P.u i + P.u' i)) / 2 - ∑ i ∈ Icc 1 (P.k - 1), rho P π i
def Nrm (l : ℕ) (π : Ty P) : ℝ :=
  -I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l - 1) /
    ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l - 1))
def NrmDown (l : ℕ) (π : Ty P) : ℝ :=
  -I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l) /
    ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l))
abbrev A (P : Par) : Type := Matrix (Ty P) (Ty P) (Pr P.r)
def sc (w : Pr P.r) : A P := Matrix.scalar (Ty P) w
def kap : (Ty P → ℂ) →ₐ[ℂ] A P :=
  (Matrix.diagonalAlgHom ℂ).comp ((Algebra.ofId ℂ (Pr P.r)).compLeft (Ty P))
def pA (l : Fin P.r) : A P := sc P (pP l)
def pbA (l : Fin P.r) : A P := sc P (pbP l)
def cA (l : Fin P.r) : A P := sc P (cP l)
def ciA (l : Fin P.r) : A P := sc P (ciP l)
def cbA (l : Fin P.r) : A P := sc P (cbP l)
def cbiA (l : Fin P.r) : A P := sc P (cbiP l)
def zA : A P := sc P zP
def ziA : A P := sc P ziP
def zbA : A P := sc P zbP
def zbiA : A P := sc P zbiP
def ggA : A P := sc P (ggP P.TT)
def ggiA : A P := sc P (ggiP P.TT)
def nabA : A P := Matrix.diagonal fun π => dzP + (aC P π : ℂ) • (zbP * ggiP P.TT)
def nabsA : A P := Matrix.diagonal fun π => -dzbP + (aC P π : ℂ) • (zP * ggiP P.TT)
def IsModelLevel (L : LevelData (A P) P.r) : Prop :=
  L.p = pA P ∧ L.pb = pbA P ∧ L.c = cA P ∧ L.ci = ciA P ∧ L.cb = cbA P ∧ L.cbi = cbiA P ∧
    L.ζ = zA P ∧ L.ζi = ziA P ∧ L.ζb = zbA P ∧ L.ζbi = zbiA P ∧ L.GG = ggA P ∧ L.GGi = ggiA P ∧
    L.nab = nabA P ∧ L.nabs = nabsA P ∧ L.TT = (P.TT : ℂ)
def SS (l : ℕ) : A P :=
  Matrix.of fun π' π => if Up P l π π' then algebraMap ℂ (Pr P.r) ((Real.sqrt (Nrm P l π) : ℝ) : ℂ) else 0
def l0A (Y : ℂ) : A P := -nabA P - algebraMap ℂ (A P) (Y + 1 / 2) * (zbA P * ggiA P)
def m0A (Y : ℂ) : A P := -nabsA P - algebraMap ℂ (A P) (Y - 1 / 2) * (zA P * ggiA P)
def xA (Y : ℂ) : A P := kap P fun π => xC P π Y
def weightedSumBis (Y : ℂ) : A P := ∑ l ∈ Icc 1 (P.k - 1), SS P l * kap P fun π => xEx P {l} π Y
def S12 (Y : ℂ) : A P := ∑ l ∈ Icc 1 (P.k - 1), (kap P fun π => xEx P {l} π Y) * star (SS P l)
def S4 (Y : ℂ) : A P :=
  ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ (Icc 1 (P.k - 1)).erase l,
    star (SS P l) * SS P j * kap P fun π => xEx P {l, j} π Y
def coordinatePolynomial (π : Ty P) : ℂ[X] := ∏ i ∈ Icc 1 (P.k - 1), (X + C ((rho P π i : ℂ) + 1))
def qP : ℂ[X] :=
  C (-((P.T : ℂ) * P.T')) * ∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))
def wNum (π : Ty P) : ℂ[X] :=
  qP P + ∑ l ∈ Icc 1 (P.k - 1), C ((Nrm P l π : ℝ) : ℂ) *
    ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C (rho P π j : ℂ))) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C ((rho P π j : ℂ) + 1)))
def wC (π : Ty P) (Y : ℂ) : ℂ := (wNum P π /ₘ coordinatePolynomial P π).eval Y
def t22 (Y : ℂ) : A P := ggA P * xA P Y
def t21 (Y : ℂ) : A P := ggA P * xA P Y * l0A P Y + weightedSumBis P Y
def t12 (Y : ℂ) : A P := ggA P * xA P Y * m0A P Y + S12 P Y
def t11 (Y : ℂ) : A P :=
  ggiA P * (kap P fun π => wC P π Y) + ggA P * xA P Y * m0A P Y * l0A P Y +
    ggA P * m0A P Y * ggiA P * weightedSumBis P Y + S12 P Y * l0A P Y + ggiA P * S4 P Y
def QQr (Y : ℂ) : M2 (A P) := !![t11 P Y, t12 P Y; t21 P Y, t22 P Y]
def lA (Y : ℂ) : A P :=
  l0A P Y + ggiA P * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j
def mA (Y : ℂ) : A P :=
  m0A P Y + ggiA P * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * star (SS P j)
def sgn (l : ℕ) : ℂ := (-1) ^ (P.k - l)
def x0 (l : ℕ) (π : Ty P) (Y : ℂ) : ℂ := (-1) ^ (P.k - l) * ∏ i ∈ Icc 1 (P.k - 1), (Y + (rho P π i : ℂ))
def eeA (Y : ℂ) : A P :=
  zA P * zbiA P * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j
def startM (l : ℕ) : Start (A P) where
  QQ Y := sgn P l • QQr P Y
  q := qC P
  x Y := kap P fun π => x0 P l π Y
  xi Y := kap P fun π => (x0 P l π Y)⁻¹
  ee := eeA P
  inv := {Y | ∀ π, xC P π Y ≠ 0}
def siteA (l : Fin P.r) : Site (A P) := ⟨pA P l, cA P l, ciA P l⟩
def sitesFrom (i : ℕ) : List (Site (A P)) := ((List.ofFn (siteA P)).drop i).reverse
def QQlev (l i : ℕ) (Y : ℂ) : M2 (A P) :=
  (((sitesFrom P i).map fun σ => Ts σ (star Y)).prod)ᴴ * (startM P l).QQ Y *
    ((sitesFrom P i).map fun σ => Ts σ Y).prod
def CutWord {S : Type} (l : ℕ) (w : List (Letter ℂ S)) : Prop :=
  (w.map Letter.intersection_update_fsHerm_neg_one).Nodup ∧ (∀ a ∈ w, a.pt.im = 0 ∧ I.OnCut P.u P.u' l a.pt.re) ∧
    w.Pairwise fun a a' => 2 < |a.pt.re - a'.pt.re|
def CutWordBase {S : Type} (l : ℕ) (w : List (Letter ℂ S)) : Prop :=
  (w.map Letter.intersection_update_fsHerm_neg_one).Nodup ∧
    (∀ a ∈ w, a.pt.im = 0 ∧ (I.OnCut P.u P.u' l (ypt a).re ∨ I.OnCut P.u P.u' l ((ypt a).re + 1))) ∧
    w.Pairwise fun a a' => 2 < |(ypt a).re - (ypt a').re|
def fnsA : Set (A P) :=
  Set.range (cA P) ∪ Set.range (ciA P) ∪ Set.range (cbA P) ∪ Set.range (cbiA P) ∪
    {zA P, ziA P, zbA P, zbiA P, ggA P, ggiA P}
def zfnsA : Set (A P) := {zA P, ziA P, zbA P, zbiA P, ggA P, ggiA P}
end
def MulOpHom : Prop :=
  ∀ (r : ℕ) (f g : Fn r) (z : ℂ), mulOp (f * g) = mulOp f * mulOp g ∧ mulOp (f + g) = mulOp f + mulOp g ∧
    mulOp (1 : Fn r) = 1 ∧ mulOp (algebraMap ℂ (Fn r) z) = algebraMap ℂ (Op r) z
def EulerLeibniz : Prop :=
  ∀ (r : ℕ) (v : Var r) (f g : Fn r), euler v (f * g) = euler v f * g + f * euler v g
def EulerCoord : Prop :=
  ∀ (r : ℕ) (v w : Var r) (z : ℂ), euler v (coord w) = (if v = w then coord w else 0) ∧
    euler v (algebraMap ℂ (Fn r) z) = 0
def EulerComm : Prop := ∀ (r : ℕ) (v w : Var r), euler v * euler w = euler w * euler v
def EulerMul : Prop :=
  ∀ (r : ℕ) (v : Var r) (f : Fn r), euler v * mulOp f = mulOp f * euler v + mulOp (euler v f)
def FnNonzero : Prop := ∀ (r : ℕ) (v : Var r) (TT : ℝ), coord v ≠ 0 ∧ (gg TT : Fn r) ≠ 0
def ModelNontrivial : Prop :=
  ∀ P : Par, Nontrivial (A P) ∧ ∀ f fb : Fn P.r, sc P (fnP f fb) = 0 → f = 0
def LevFns : Prop :=
  ∀ P : Par, (∀ x ∈ fnsA P, ∀ y ∈ fnsA P, x * y = y * x) ∧
    (∀ l, cA P l * ciA P l = 1 ∧ ciA P l * cA P l = 1 ∧ cbA P l * cbiA P l = 1 ∧ cbiA P l * cbA P l = 1) ∧
    zA P * ziA P = 1 ∧ ziA P * zA P = 1 ∧ zbA P * zbiA P = 1 ∧ zbiA P * zbA P = 1 ∧
    ggA P * ggiA P = 1 ∧ ggiA P * ggA P = 1 ∧ ggA P = zA P * zbA P - algebraMap ℂ (A P) (P.TT : ℂ)
def LevP : Prop :=
  ∀ (P : Par) (l : Fin P.r),
    (∀ m, pA P l * cA P m = cA P m * pA P l + (if l = m then cA P m else 0)) ∧
    (∀ m, pA P l * ciA P m = ciA P m * pA P l - (if l = m then ciA P m else 0)) ∧
    ∀ x ∈ Set.range (cbA P) ∪ Set.range (cbiA P) ∪ zfnsA P, pA P l * x = x * pA P l
def LevPb : Prop :=
  ∀ (P : Par) (l : Fin P.r),
    (∀ m, pbA P l * cbA P m = cbA P m * pbA P l + (if l = m then cbA P m else 0)) ∧
    (∀ m, pbA P l * cbiA P m = cbiA P m * pbA P l - (if l = m then cbiA P m else 0)) ∧
    ∀ x ∈ Set.range (cA P) ∪ Set.range (ciA P) ∪ zfnsA P, pbA P l * x = x * pbA P l
def LevPP : Prop :=
  ∀ (P : Par) (l m : Fin P.r), pA P l * pA P m = pA P m * pA P l ∧ pA P l * pbA P m = pbA P m * pA P l ∧
    pbA P l * pbA P m = pbA P m * pbA P l ∧ pA P l * nabA P = nabA P * pA P l ∧
    pbA P l * nabA P = nabA P * pbA P l ∧ pA P l * nabsA P = nabsA P * pA P l ∧
    pbA P l * nabsA P = nabsA P * pbA P l
def LevNab : Prop :=
  ∀ P : Par, nabA P * zA P = zA P * nabA P + 1 ∧ nabA P * ziA P = ziA P * nabA P - ziA P * ziA P ∧
    nabA P * zbA P = zbA P * nabA P ∧ nabA P * zbiA P = zbiA P * nabA P ∧
    nabA P * ggA P = ggA P * nabA P + zbA P ∧
    nabA P * ggiA P = ggiA P * nabA P - zbA P * ggiA P * ggiA P ∧
    ∀ x ∈ Set.range (cA P) ∪ Set.range (ciA P) ∪ Set.range (cbA P) ∪ Set.range (cbiA P),
      nabA P * x = x * nabA P
def LevNabs : Prop :=
  ∀ P : Par, nabsA P * zbA P = zbA P * nabsA P - 1 ∧ nabsA P * zbiA P = zbiA P * nabsA P + zbiA P * zbiA P ∧
    nabsA P * zA P = zA P * nabsA P ∧ nabsA P * ziA P = ziA P * nabsA P ∧
    nabsA P * ggA P = ggA P * nabsA P - zA P ∧
    nabsA P * ggiA P = ggiA P * nabsA P + zA P * ggiA P * ggiA P ∧
    ∀ x ∈ Set.range (cA P) ∪ Set.range (ciA P) ∪ Set.range (cbA P) ∪ Set.range (cbiA P),
      nabsA P * x = x * nabsA P
def LevelExists : Prop := ∀ P : Par, ∃ L : LevelData (A P) P.r, IsModelLevel P L
def LevelAssemble : Prop := LevFns → LevP → LevPb → LevPP → LevNab → LevNabs → LevelExists
def StarGens : Prop :=
  ∀ P : Par, (∀ l, star (cA P l) = cbA P l ∧ star (ciA P l) = cbiA P l ∧ star (pA P l) = -pbA P l) ∧
    star (zA P) = zbA P ∧ star (ziA P) = zbiA P ∧ star (ggA P) = ggA P ∧ star (ggiA P) = ggiA P ∧
    star (nabA P) = nabsA P
def LevelStar : Prop := ∀ (P : Par) (L : LevelData (A P) P.r), IsModelLevel P L → IsStarLevel L
def TyInterlaces : Prop := ∀ P : Par, P.OK → ∀ π : Ty P, I.Interlaces P.k P.u P.u' (rho P π)
def TyComplete : Prop :=
  ∀ P : Par, P.OK → (∀ ρ : ℕ → ℝ, I.Interlaces P.k P.u P.u' ρ →
    (∀ i ∈ Icc 1 (P.k - 1), ∃ n : ℤ, ρ i - P.u 1 - 1 / 2 = n) →
    ∃ π : Ty P, ∀ i ∈ Icc 1 (P.k - 1), ρ i = rho P π i) ∧
    ∀ π π' : Ty P, (∀ i ∈ Icc 1 (P.k - 1), rho P π i = rho P π' i) → π = π'
def RhoUp : Prop :=
  ∀ (P : Par) (l : ℕ) (π π' : Ty P), Up P l π π' → ∀ i ∈ Icc 1 (P.k - 1),
    rho P π' i = rho P π i + if i = l then 1 else 0
def NrmFacts : Prop :=
  ∀ P : Par, P.OK → ∀ l ∈ Icc 1 (P.k - 1), ∀ π : Ty P,
    (∀ π', Up P l π π' → 0 < Nrm P l π ∧ NrmDown P l π' = Nrm P l π) ∧
    ((¬ ∃ π', Up P l π π') → Nrm P l π = 0) ∧ ((¬ ∃ π', Up P l π' π) → NrmDown P l π = 0)
def RealPoints : Prop :=
  ∀ (P : Par) (π : Ty P) (Y : ℝ), xC P π (Y : ℂ) = (I.xpoly P.k (rho P π) Y : ℝ) ∧
    qC P (Y : ℂ) = (I.qpoly P.k P.T P.T' P.u P.u' Y : ℝ)
def WExact : Prop := ∀ P : Par, P.OK → ∀ π : Ty P, wNum P π = coordinatePolynomial P π * (wNum P π /ₘ coordinatePolynomial P π)
def InterlaceSignTwo : Prop :=
  ∀ (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k → I.Interlaces k u u' ρ →
    I.OnCut u u' l Y → ∀ e ∈ ({-2, 2} : Finset ℝ), 0 < (-1 : ℝ) ^ (k - l) * I.xpoly k ρ (Y + e)
def SSScalar : Prop := ∀ (P : Par) (l : ℕ) (w : Pr P.r), Commute (SS P l) (sc P w)
def SSShift : Prop :=
  ∀ (P : Par) (l : ℕ) (f g : Ty P → ℂ), (∀ π π', Up P l π π' → g π' = f π) →
    kap P g * SS P l = SS P l * kap P f
def SSNorm : Prop :=
  ∀ P : Par, P.OK → ∀ l ∈ Icc 1 (P.k - 1),
    star (SS P l) * SS P l = (kap P fun π => ((Nrm P l π : ℝ) : ℂ)) ∧
    SS P l * star (SS P l) = kap P fun π => ((NrmDown P l π : ℝ) : ℂ)
def SSComm : Prop :=
  ∀ P : Par, P.OK → ∀ l ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1), j ≠ l →
    SS P j * SS P l * (kap P fun π => ((rho P π j - rho P π l - 1 : ℝ) : ℂ)) =
      SS P l * SS P j * kap P fun π => ((rho P π j - rho P π l + 1 : ℝ) : ℂ)
def SSMixed : Prop :=
  ∀ P : Par, P.OK → ∀ l ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1), j ≠ l →
    star (SS P l) * SS P j = SS P j * star (SS P l)
def NabSS : Prop :=
  ∀ (P : Par), ∀ l ∈ Icc 1 (P.k - 1),
    nabA P * SS P l = SS P l * nabA P - zbA P * ggiA P * SS P l ∧
    nabsA P * SS P l = SS P l * nabsA P - zA P * ggiA P * SS P l
def Curvature : Prop :=
  ∀ P : Par, nabsA P * nabA P - nabA P * nabsA P =
    (kap P fun π => ((2 * aC P π * P.TT : ℝ) : ℂ)) * ggiA P * ggiA P
def QQNormal : Prop :=
  ∀ P : Par, P.OK → ∀ Y : ℂ, (∀ π, xC P π Y ≠ 0) →
    t21 P Y = t22 P Y * lA P Y ∧ t12 P Y = t22 P Y * mA P Y ∧
    ((∀ π, xC P π (Y + 1) ≠ 0) → t11 P Y =
      qC P Y • (ggiA P * kap P fun π => (xC P π (Y + 1))⁻¹) + t22 P Y * mA P Y * lA P Y) ∧
    (star Y = Y → mA P Y = star (lA P (Y - 1)))
def QQHerm : Prop := ∀ P : Par, P.OK → ∀ Y : ℂ, (QQr P Y)ᴴ = QQr P (star Y)
def QQRTTEntries : Prop :=
  ∀ P : Par, P.OK → ∀ (u v : ℂ) (i j k l : Fin 2),
    (u - v) • (QQr P u i j * QQr P v k l - QQr P v k l * QQr P u i j) =
      QQr P u k j * QQr P v i l - QQr P v k j * QQr P u i l
def QQRTT : Prop := ∀ P : Par, P.OK → IsRTT (QQr P)
def QQRTTOfEntries : Prop := QQRTTEntries → QQRTT
def QQDet : Prop := ∀ P : Par, P.OK → IsDet (QQr P) (qC P)
def T21Commute : Prop := ∀ P : Par, P.OK → ∀ u v : ℂ, Commute (t21 P u) (t21 P v)
def QQLeading : Prop :=
  ∀ P : Par, P.OK → ∃ a11 a12 a21 a22 : ℕ → A P, ∀ Y : ℂ,
    t11 P Y = Y ^ (P.k + 1) • (1 : A P) + ∑ i ∈ range (P.k + 1), Y ^ i • a11 i ∧
    t12 P Y = -(Y ^ P.k • zA P) + ∑ i ∈ range P.k, Y ^ i • a12 i ∧
    t21 P Y = -(Y ^ P.k • zbA P) + ∑ i ∈ range P.k, Y ^ i • a21 i ∧
    t22 P Y = Y ^ (P.k - 1) • ggA P + ∑ i ∈ range (P.k - 1), Y ^ i • a22 i
def QQZeta : Prop :=
  ∀ (P : Par) (Y : ℂ), t21 P Y * zA P - zA P * t21 P Y = -t22 P Y ∧
    t11 P Y * zA P - zA P * t11 P Y = -t12 P Y ∧ Commute (t12 P Y) (zA P) ∧ Commute (t22 P Y) (zA P)
def StartIsStart : Prop := ∀ P : Par, P.OK → ∀ l : ℕ, IsStart (startM P l).QQ (startM P l).q
def StartIsStartAssemble : Prop := QQHerm → QQRTT → QQDet → StartIsStart
def StartOK : Prop :=
  ∀ P : Par, P.OK → ∀ (l : ℕ) (L : LevelData (A P) P.r), IsModelLevel P L → IsLevelStart L (startM P l)
def StartAssemble : Prop := StartIsStart → T21Commute → SSScalar → SSShift → RhoUp → StartOK
def SitesOKM : Prop := ∀ (P : Par) (l : ℕ), SitesOK (K := ℂ) (startM P l).QQ (sitesFrom P 0)
def SiteJoint : Prop :=
  ∀ (P : Par) (L : LevelData (A P) P.r), IsModelLevel P L → ∀ (l : Fin P.r) (Y : ℂ),
    L.Tl Y l = Ts (siteA P l) Y ∧ (star Y = Y → L.Tvl Y l = (Ts (siteA P l) Y).map star)
def ChainM : Prop :=
  ∀ (P : Par) (l : ℕ), (∀ Y, QQlev P l P.r Y = (startM P l).QQ Y) ∧
    ∀ (i : Fin P.r) (Y : ℂ), QQlev P l i Y =
      (Ts (siteA P i) (star Y))ᴴ * QQlev P l (i + 1) Y * Ts (siteA P i) Y
def LowerCommutes : Prop :=
  ∀ (P : Par) (l : ℕ) (i : Fin P.r), QQCommutes (K := ℂ) (QQlev P l (i + 1)) (siteA P i)
def LowerStart : Prop := ∀ P : Par, P.OK → ∀ l i : ℕ, i ≤ P.r → IsStart (QQlev P l i) (qC P)
def ModelWords : Prop :=
  ∀ P : Par, P.OK → ∀ (l : ℕ) (S : Type) [Fintype S] [DecidableEq S] (w : List (Letter ℂ S)), Good w →
    (∀ i ≤ P.r, IsModule {Y | Reg w Y} (RRw (QQlev P l i) w) (TTw (QQlev P l i) w) (qw (qC P) w)) ∧
    (∀ i : Fin P.r, star (bT (siteA P i) w) * RRw (QQlev P l (i + 1)) w * bT (siteA P i) w =
      RRw (QQlev P l i) w) ∧
    ∀ Y, Reg w Y → star Y = Y → ∀ z : Ix S,
      (∑ z', Cw (startM P l).QQ (sitesFrom P 0) w Y z z' * uw (sitesFrom P 0) w z') =
        uw (sitesFrom P 0) w z * C0 (startM P l).QQ (sitesFrom P 0) Y
def ModelWordsAssemble : Prop :=
  WordsAll → LowerStart → SitesOKM → ChainM → LowerCommutes → ModelWords
def CutAdm : Prop :=
  I.InterlaceSign → I.QPositive → QPositiveShift → TyInterlaces → RealPoints →
  ∀ P : Par, P.OK → ∀ l, 1 ≤ l → l ≤ P.k → ∀ (S : Type) [Fintype S] [DecidableEq S]
    (w : List (Letter ℂ S)), CutWord P l w → admitted (startM P l) w
def CutAdmBase : Prop :=
  I.InterlaceSign → InterlaceSignTwo → I.QPositive → QPositiveShift → TyInterlaces → RealPoints →
  ∀ P : Par, P.OK → ∀ l, 1 ≤ l → l ≤ P.k → ∀ (S : Type) [Fintype S] [DecidableEq S]
    (w : List (Letter ℂ S)), CutWordBase P l w → AdmBase (startM P l) w
def FrameConcl (P : Par) (l : ℕ) (L : LevelData (A P) P.r) {S : Type} [Fintype S] [DecidableEq S]
    (w : List (Letter ℂ S)) : Prop :=
  IsFrame L (ofWord L (startM P l) w) ∧
  RRw (startM P l).QQ w = star (ofWord L (startM P l) w).F *
    (wt L ^ w.length * (ofWord L (startM P l) w).c) * (ofWord L (startM P l) w).F ∧
  (∀ Y, Reg w Y → (ofWord L (startM P l) w).F * TTw (startM P l).QQ w Y 1 1 =
    io L.GG * (ofWord L (startM P l) w).x Y * (ofWord L (startM P l) w).F) ∧
  (∀ Y ∈ (ofWord L (startM P l) w).inv, Y + 1 ∈ (ofWord L (startM P l) w).inv →
    (ofWord L (startM P l) w).F * TTw (startM P l).QQ w Y 1 0 =
      io L.GG * (ofWord L (startM P l) w).x Y * (io (L.l0 Y) + kapL L * (ofWord L (startM P l) w).ee Y) *
        (ofWord L (startM P l) w).F) ∧
  (ofWord L (startM P l) w).c = (Matrix.diagonal fun e => kap P fun π => cs (x0 P l π) (qC P) w e) ∧
  ∀ (e : Ix S) (π : Ty P), Pos (cs (x0 P l π) (qC P) w e)
def ModelFrame : Prop :=
  ∀ P : Par, P.OK → ∀ l, 1 ≤ l → l ≤ P.k →
    ∃ L : LevelData (A P) P.r, IsModelLevel P L ∧ IsStarLevel L ∧ IsLevelStart L (startM P l) ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Letter ℂ S)), CutWord P l w → FrameConcl P l L w
def ModelFrameBase : Prop :=
  ∀ P : Par, P.OK → ∀ l, 1 ≤ l → l ≤ P.k →
    ∃ L : LevelData (A P) P.r, IsModelLevel P L ∧ IsStarLevel L ∧ IsLevelStart L (startM P l) ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Letter ℂ S)), CutWordBase P l w → FrameConcl P l L w
def ModelAssemble : Prop :=
  I.InterlaceSign → I.QPositive → QPositiveShift → CPos → CPosCut → FrameAll → FrameWord → CDiag →
  LevelExists → LevelStar → StartOK → TyInterlaces → RealPoints → CutAdm → ModelFrame
def ModelAssembleBase : Prop :=
  I.InterlaceSign → InterlaceSignTwo → I.QPositive → QPositiveShift → CPosBase → CPosCutBase → FrameAllRec →
  AdmRecOfBase → WordJoint → CDiag → LevelExists → LevelStar → StartOK → TyInterlaces → RealPoints → CutAdmBase →
  ModelFrameBase
end Formalism.FourierDecayAlt.M


