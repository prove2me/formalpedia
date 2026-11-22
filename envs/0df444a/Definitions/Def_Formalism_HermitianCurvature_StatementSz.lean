-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementSz
-- name    : Formalism_HermitianCurvature_StatementSz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:05:02.092541+00:00
-- url     : https://prove2.me/theorems/1c967242-5e92-48e9-82b0-dcc4a507f5ee
-- title:
--   Statement Sz
-- statement:
--   Definitions and structural lemmas for Statement Sz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementSz.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.Sz
open Finset
noncomputable def Vand (p : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∏ i ∈ Icc 1 p, ∏ j ∈ Ioc i p, (x i - x j)
def sfac (p : ℕ) : ℕ := ∏ i ∈ range p, i.factorial
noncomputable def TcritPow (k m : ℕ) (ka rd g VV Vu : ℝ) : ℝ :=
  (ka ^ ((m - 1) * k + m * (m - 1) / 2))⁻¹ * rd ^ (-(((m : ℝ) - 1) / 2)) *
    g ^ (k * m + m * (m - 1) / 2) * VV / Vu
noncomputable def Tcrit (k m : ℕ) (ka rd g VV Vu : ℝ) : ℝ :=
  (TcritPow k m ka rd g VV Vu) ^ ((1 : ℝ) / (k : ℝ))
noncomputable def glCard (p : ℕ) (q : ℝ) : ℝ := ∏ j ∈ range p, (q ^ p - q ^ j)
def dimN (k r : ℕ) : ℕ := r * (2 * k + 2 * r + 1)
noncomputable def rowIdx (k r : ℕ) (q : ℝ) : ℝ :=
  glCard (k + 2 * r + 1) q / (q ^ dimN k r * q ^ (k * (k - 1) / 2))
noncomputable def colIdx (k : ℕ) (q : ℝ) : ℝ := glCard k q / q ^ (k * (k - 1) / 2)
structure SizeData (ι : Type) [Fintype ι] where

  k : ℕ

  r : ℕ

  v : ℝ

  dF : ℝ

  Lv : ℕ → ℝ

  vol : ℕ → ℝ

  g1 : ℕ
  g2 : ℕ

  T : ℕ

  dsig : ι → ℝ

  Vu : ι → ℝ

  du : ℝ
namespace SizeData
variable {ι : Type} [Fintype ι] (S : SizeData ι)
def f (_S : SizeData ι) : ℕ := Fintype.card ι
def m : ℕ := 2 * S.r + 2
def n : ℕ := S.k + S.m - 1
noncomputable def ka : ℝ := Real.pi / S.v
noncomputable def rd : ℝ := 2 * S.v
noncomputable def g : ℝ := (S.g1 : ℝ) * (S.g2 : ℝ)
noncomputable def VV (w : ι) : ℝ := S.dsig w * (sfac S.n : ℝ)
noncomputable def dimPi (w : ι) : ℝ := S.Vu w / (sfac S.k : ℝ)
noncomputable def TcritPow (w : ι) : ℝ :=
  Sz.TcritPow S.k S.m S.ka S.rd S.g (S.VV w) (S.Vu w)
noncomputable def Tcrit (w : ι) : ℝ :=
  Sz.Tcrit S.k S.m S.ka S.rd S.g (S.VV w) (S.Vu w)
noncomputable def idxRow : ℝ :=
  (rowIdx S.k S.r (S.g1 : ℝ)) ^ S.f * (rowIdx S.k S.r (S.g2 : ℝ)) ^ S.f
noncomputable def idxCol : ℝ := (colIdx S.k (S.g1 : ℝ)) ^ S.f * (colIdx S.k (S.g2 : ℝ)) ^ S.f
noncomputable def Dstar : ℝ := S.vol S.n * S.idxRow * ∏ w, S.dsig w
noncomputable def Ea : ℝ :=
  (∏ M ∈ Ioc S.k S.n, S.Lv M) *
    ((∏ j ∈ Ioc S.k S.n, (1 - ((S.g1 : ℝ) ^ j)⁻¹)) ^ S.f *
      (∏ j ∈ Ioc S.k S.n, (1 - ((S.g2 : ℝ) ^ j)⁻¹)) ^ S.f) *
    ((1 - ((S.T : ℝ) ^ S.k)⁻¹) ^ S.f)⁻¹
def MassRatios : Prop :=
  ∀ M : ℕ, S.k < M → M ≤ S.n →
    S.vol M = (((M - 1).factorial : ℝ) * (S.v / Real.pi) ^ M) ^ S.f *
      S.dF ^ (-(1 / 2 : ℝ)) * S.Lv M * S.vol (M - 1)
def LBound : Prop :=
  ∀ M : ℕ, S.k < M → M ≤ S.n →
    0 < S.Lv M ∧
      |Real.log (S.Lv M)| ≤ (S.f : ℝ) * Real.log (∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ M)
def ColumnCount : Prop :=
  S.du = S.vol S.k * S.idxCol * (∏ w, S.dimPi w) * ((S.T : ℝ) ^ S.k - 1) ^ S.f
def ChoiceOfT (C0 Gam : ℝ) : Prop :=
  (Gam ^ 2)⁻¹ * S.Dstar * C0⁻¹ ≤ S.du ∧ S.du ≤ (Gam ^ 2)⁻¹ * S.Dstar * C0
structure Ok : Prop where
  hk : 1 ≤ S.k
  hv : 0 < S.v
  hdF : S.dF = (2 * S.v) ^ S.f
  hg1 : 2 ≤ S.g1
  hg2 : 2 ≤ S.g2
  hT : 2 ≤ S.T
  hvol : 0 < S.vol S.k
  hVu : ∀ w, 0 < S.Vu w
end SizeData
def SumRanks : Prop :=
  ∀ k r m n : ℕ, m = 2 * r + 2 → n = k + m - 1 →
    ∑ M ∈ Ioc k n, M = (m - 1) * k + m * (m - 1) / 2 ∧ (Ioc k n).card = m - 1 ∧
      2 * (m * (m - 1) / 2) = m * (m - 1)
def LevelExponent : Prop :=
  ∀ k r m n : ℕ, m = 2 * r + 2 → n = k + m - 1 →
    2 * dimN k r + (k + 1) ^ 2 + 2 * r = n ^ 2 ∧
      k ^ 2 + dimN k r + (k * m + m * (m - 1) / 2) = n ^ 2
def IndexRatio : Prop :=
  ∀ (k r m n : ℕ) (q : ℝ), m = 2 * r + 2 → n = k + m - 1 → 1 < q →
    rowIdx k r q / colIdx k q =
      q ^ (k * m + m * (m - 1) / 2) * ∏ j ∈ Ioc k n, (1 - (q ^ j)⁻¹)
def FactorialCancel : Prop :=
  ∀ k n : ℕ, k ≤ n → (∏ i ∈ Ico k n, i.factorial) * sfac k = sfac n
def VolumeChain : Prop :=
  ∀ (ι : Type) [Fintype ι] (S : SizeData ι), S.Ok → S.MassRatios →
    S.vol S.n =
      ((S.ka ^ ((S.m - 1) * S.k + S.m * (S.m - 1) / 2))⁻¹ * S.rd ^ (-(((S.m : ℝ) - 1) / 2)) *
          ((∏ i ∈ Ico S.k S.n, i.factorial : ℕ) : ℝ)) ^ S.f *
        (∏ M ∈ Ioc S.k S.n, S.Lv M) * S.vol S.k
def PropA : Prop :=
  ∀ (ι : Type) [Fintype ι] (S : SizeData ι), S.Ok → S.MassRatios → S.ColumnCount →
    S.Dstar / S.du = S.Ea * ∏ w, (S.TcritPow w / (S.T : ℝ) ^ S.k)
def ZetaTail : Prop :=
  ∀ M : ℕ, 3 ≤ M → Real.log (∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ M) ≤ 2 / 2 ^ M
def EaSize : Prop :=
  ∀ (ι : Type) [Fintype ι] (S : SizeData ι), S.Ok → S.LBound → 2 ≤ S.k → 4 ≤ S.g1 → 4 ≤ S.g2 →
    0 < S.Ea ∧ |Real.log S.Ea| ≤ (S.f : ℝ) * (8 / 2 ^ S.k)
def CorA : Prop :=
  ∀ (ι : Type) [Fintype ι] (S : SizeData ι) (C0 CG C' L : ℝ),
    S.Ok → S.MassRatios → S.LBound → S.ColumnCount →
    (∀ w, 0 < S.dsig w) → 2 ≤ S.k → 4 ≤ S.g1 → 4 ≤ S.g2 →
    1 ≤ C0 → 0 ≤ CG → 0 ≤ L → 8 * CG ≤ C' →
    C' * (S.m : ℝ) ^ 5 * S.f * L ≤ S.k →
    (S.f : ℝ) * (8 / 2 ^ S.k) ≤ Real.log 2 →
    S.ChoiceOfT C0 (Real.exp (CG * (S.m : ℝ) ^ 5 * S.f * L)) →
    (2 * C0) ^ (-(1 / (S.k : ℝ))) ≤ ∏ w, (S.Tcrit w / S.T) ∧
      ∏ w, (S.Tcrit w / S.T) ≤ (2 * C0) ^ (1 / (S.k : ℝ)) * Real.exp (1 / 4) ∧
      (2 * C0) ^ (1 / (S.k : ℝ)) * Real.exp (1 / 4) ≤ 2 * C0 * Real.exp (1 / 4)
def BracketBound : Prop :=
  ∀ (k r m : ℕ) (ka rd g VV Vu : ℝ), m = 2 * r + 2 → 1 ≤ k → 1 ≤ rd → ka = 2 * Real.pi / rd →
    2 * Real.pi ≤ g → 0 < VV → 0 < Vu →
    let om : ℝ := ((ka ^ (m * (m - 1) / 2))⁻¹ * rd ^ (-(((m : ℝ) - 1) / 2)) *
      g ^ (m * (m - 1) / 2)) ^ ((1 : ℝ) / (k : ℝ))
    1 ≤ om ∧ om ≤ Real.exp ((m : ℝ) ^ 2 * (Real.log g + Real.log rd) / (2 * k)) ∧
      Tcrit k m ka rd g VV Vu = (ka ^ (m - 1))⁻¹ * g ^ m * om * (VV / Vu) ^ ((1 : ℝ) / (k : ℝ))
structure Cfg where
  k : ℕ
  m : ℕ

  Del : ℝ

  vlast : ℝ

  b : ℕ → ℝ

  a : ℝ

  top : Bool

  bp : ℝ
namespace Cfg
variable (c : Cfg)
noncomputable def v (i : ℕ) : ℝ := c.vlast + 4 * c.Del * ((c.k : ℝ) - 1 - (i : ℝ))
noncomputable def lam (s : ℕ) : ℝ := if s < c.k then c.v s else -c.b (s + 1 - c.k)
noncomputable def ulast : ℝ := if c.top then -c.bp else c.vlast - 1 / 2
noncomputable def u (de : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 1 then c.a else if i = c.k then c.ulast else c.v (i - 1) - 1 / 2 - de (i - 1) * c.Del
noncomputable def aeff : ℝ := if c.top then c.a * c.bp / (c.k * c.Del) else c.a - c.v 1
noncomputable def vth : ℝ := 4 * c.m * c.k * c.Del / c.b 1
noncomputable def vthp : ℝ := if c.top then 4 * c.k * c.Del / c.bp else 0
noncomputable def prodb : ℝ := ∏ j ∈ Icc 1 c.m, c.b j
noncomputable def P (Y : ℝ) : ℝ := ∏ s ∈ Icc 1 (c.k + c.m - 1), (Y + c.lam s)
noncomputable def q (de de' : ℕ → ℝ) (T T' Y : ℝ) : ℝ :=
  -(T * T') * ∏ i ∈ Icc 1 c.k, ((Y + 1 / 2 + c.u de i) * (Y + 1 / 2 + c.u de' i))
noncomputable def core (de de' : ℕ → ℝ) (T T' Y : ℝ) : ℝ :=
  Real.sqrt |c.P Y * c.P (Y + 1) / c.q de de' T T' Y|
noncomputable def be (ka : ℝ) (de de' : ℕ → ℝ) (T T' Y : ℝ) : ℝ :=
  (ka ^ (c.m - 1))⁻¹ * c.core de de' T T' Y
def cutI (l : ℕ) : Set ℝ := {Y | 5 / 2 ≤ c.v l + Y ∧ c.v l + Y ≤ c.Del / 2}
def cutIntervalLong (l : ℕ) (N : ℝ) : Set ℝ := {Y | 5 / 2 ≤ c.v l + Y ∧ c.v l + Y ≤ N ^ 3}
noncomputable def Nd (y : ℝ) : ℝ :=
  ∏ j ∈ Icc 1 c.m, Real.sqrt ((c.b j + y) * (c.b j + y - 1))
noncomputable def U1 (y : ℝ) : ℝ := 1 / (c.a + 1 / 2 - y)
noncomputable def rho (de de' : ℕ → ℝ) (y : ℝ) (i : ℕ) : ℝ :=
  if c.top = true ∧ i + 1 = c.k then
    Real.sqrt |(c.v i - y) * (c.v i + 1 - y)| / (c.bp + y - 1 / 2)
  else
    Real.sqrt |(c.v i - y) * (c.v i + 1 - y)| /
      Real.sqrt |(c.v i - de i * c.Del - y) * (c.v i - de' i * c.Del - y)|
structure Ok : Prop where
  hk : 4 ≤ c.k
  hm : 2 ≤ c.m
  hDel : 1 ≤ c.Del
  hv0 : 0 ≤ c.vlast
  hv1 : c.v 1 ≤ 4 * c.k * c.Del
  hb1 : 1 ≤ c.b 1
  hgap : ∀ j : ℕ, 1 ≤ j → j < c.m → c.b j + 1 ≤ c.b (j + 1)
  ha : 4 * c.k * c.Del ≤ c.a - c.v 1
  htop : c.top = true → c.b 1 / 2 ≤ c.bp ∧ c.bp ≤ c.b 1 - 3
structure Small (bb : ℝ) : Prop where
  hbb : 1 ≤ bb
  hvth : c.vth ≤ 1 / 10
  hbj : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → c.b j ≤ bb ^ 2
  hmu : 2 * c.m * Real.log bb / c.k ≤ 1 / 10
end Cfg
def IsWord (k : ℕ) (de : ℕ → ℝ) : Prop := (∀ i, de i = 0 ∨ de i = 1) ∧ de (k - 1) = 0
def FormalDegreeLower (c : Cfg) (ep0 VV : ℝ) : Prop :=
  (1 - ep0) * Vand (c.k + c.m - 1) c.lam ≤ VV
def Interlacing : Prop :=
  ∀ (c : Cfg) (de : ℕ → ℝ), c.Ok → IsWord c.k de →
    (∀ i : ℕ, 1 ≤ i → i < c.k → c.lam i < c.u de i ∧ c.u de (i + 1) < c.lam i) ∧
      c.lam c.k < c.u de c.k
def LamAnti : Prop :=
  ∀ c : Cfg, c.Ok → ∀ s t : ℕ, 1 ≤ s → s < t → t ≤ c.k + c.m - 1 → c.lam t < c.lam s
noncomputable def Rde (J : ℕ) (de : ℕ → ℝ) : ℝ :=
  ∏ i ∈ Icc 1 J, ∏ i' ∈ Ioc i J, (1 + (de i' - de i) / (4 * ((i' : ℝ) - (i : ℝ))))
def HarmonicVand : Prop :=
  ∀ (J : ℕ) (de : ℕ → ℝ), 1 ≤ J → (∀ i, de i = 0 ∨ de i = 1) →
    0 < Rde J de ∧
    |Real.log (Rde J de) -
        (1 / 4) * ∑ i ∈ Icc 1 J, de i * (((harmonic (i - 1) : ℚ) : ℝ) - ((harmonic (J - i) : ℚ) : ℝ))|
      ≤ Real.pi ^ 2 / 144 * J ∧
    |Real.log (Rde J de)| ≤ ((J : ℝ) + 1) / 4
def PositionDiff : Prop :=
  ∀ (c : Cfg) (de : ℕ → ℝ), c.Ok → IsWord c.k de → ∀ i i' : ℕ, 1 ≤ i → i < i' → i' + 1 ≤ c.k →
    (i' + 2 ≤ c.k ∨ c.top = false) →
    c.u de (i + 1) - c.u de (i' + 1) = c.Del * (4 * ((i' : ℝ) - (i : ℝ)) + de i' - de i)
def VandNonTop : Prop :=
  ∀ (c : Cfg) (de : ℕ → ℝ), c.Ok → IsWord c.k de → c.top = false →
    0 < Vand (c.k - 1) c.v ∧
    Vand (c.k - 1) (fun i => c.u de (i + 1)) = Rde (c.k - 1) de * Vand (c.k - 1) c.v ∧
    Real.exp (-((c.k : ℝ) / 4)) ≤ Rde (c.k - 1) de ∧ Rde (c.k - 1) de ≤ Real.exp ((c.k : ℝ) / 4)
def VandTop : Prop :=
  ∀ (c : Cfg) (de : ℕ → ℝ), c.Ok → IsWord c.k de →
    0 < Vand (c.k - 2) c.v ∧
    Vand (c.k - 2) (fun i => c.u de (i + 1)) = Rde (c.k - 2) de * Vand (c.k - 2) c.v ∧
    Real.exp (-(((c.k : ℝ) - 1) / 4)) ≤ Rde (c.k - 2) de ∧
    Rde (c.k - 2) de ≤ Real.exp (((c.k : ℝ) - 1) / 4) ∧
    Vand (c.k - 1) c.v = Vand (c.k - 2) c.v * (4 * c.Del) ^ (c.k - 2) * ((c.k - 2).factorial : ℝ)
def EdgeFactors : Prop :=
  ∀ (c : Cfg) (de : ℕ → ℝ), c.Ok → IsWord c.k de →
    (∀ i : ℕ, 2 ≤ i → i ≤ c.k → (i < c.k ∨ c.top = false) →
      c.a - c.v 1 ≤ c.a - c.u de i ∧ c.a - c.u de i ≤ 2 * (c.a - c.v 1)) ∧
    (c.top = false →
      (c.a - c.v 1) ^ (c.k - 1) ≤ ∏ i ∈ Icc 2 c.k, (c.a - c.u de i) ∧
        ∏ i ∈ Icc 2 c.k, (c.a - c.u de i) ≤ (2 * (c.a - c.v 1)) ^ (c.k - 1))
def EdgeRatios : Prop :=
  ∀ (c : Cfg) (de de' : ℕ → ℝ), c.Ok → c.vth ≤ 1 / 10 → IsWord c.k de → IsWord c.k de' →
    (Real.exp (-(1 / 3)) ≤ ∏ i ∈ Icc 2 (c.k - 1), ((c.a - c.u de i) / (c.a - c.u de' i)) ∧
      ∏ i ∈ Icc 2 (c.k - 1), ((c.a - c.u de i) / (c.a - c.u de' i)) ≤ Real.exp (1 / 3)) ∧
    (c.top = true →
      Real.exp (-(c.vthp / 3)) ≤ ∏ i ∈ Icc 2 (c.k - 1), ((c.u de i + c.bp) / (c.u de' i + c.bp)) ∧
        ∏ i ∈ Icc 2 (c.k - 1), ((c.u de i + c.bp) / (c.u de' i + c.bp)) ≤ Real.exp (c.vthp / 3))
def VandWords : Prop :=
  ∀ (c : Cfg) (de de' : ℕ → ℝ), c.Ok → c.vth ≤ 1 / 10 → IsWord c.k de → IsWord c.k de' →
    0 < Vand c.k (c.u de) ∧ 0 < Vand c.k (c.u de') ∧
      |Real.log (Vand c.k (c.u de') / Vand c.k (c.u de))| ≤ (c.k : ℝ) / 2 + 1
def TcritWords : Prop :=
  ∀ (c : Cfg) (de de' : ℕ → ℝ) (ka rd g VV : ℝ), c.Ok → c.vth ≤ 1 / 10 →
    IsWord c.k de → IsWord c.k de' → 0 < ka → 0 < rd → 0 < g → 0 < VV →
    Tcrit c.k c.m ka rd g VV (Vand c.k (c.u de)) / Tcrit c.k c.m ka rd g VV (Vand c.k (c.u de')) =
        (Vand c.k (c.u de') / Vand c.k (c.u de)) ^ ((1 : ℝ) / (c.k : ℝ)) ∧
      Real.exp (-(3 / 4)) ≤ (Vand c.k (c.u de') / Vand c.k (c.u de)) ^ ((1 : ℝ) / (c.k : ℝ)) ∧
      (Vand c.k (c.u de') / Vand c.k (c.u de)) ^ ((1 : ℝ) / (c.k : ℝ)) ≤ Real.exp (3 / 4)
def VandLamLower : Prop :=
  ∀ c : Cfg, c.Ok →
    Vand (c.k + c.m - 1) c.lam =
        Vand (c.k - 1) c.v * (∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)) *
          Vand c.m (fun j => -c.b j) ∧
      Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1) ≤ Vand (c.k + c.m - 1) c.lam
noncomputable def cOne (c : Cfg) (bb : ℝ) : ℝ :=
  0.38 * Real.exp (-(2 * c.m * Real.log bb / c.k)) / (1 + c.vthp)
def TcritLower : Prop :=
  ∀ (c : Cfg) (r : ℕ) (bb : ℝ) (de : ℕ → ℝ) (ka rd g VV : ℝ), c.Ok → c.m = 2 * r + 2 →
    c.Small bb → IsWord c.k de → 1 ≤ rd → ka = 2 * Real.pi / rd → 2 * Real.pi ≤ g →
    FormalDegreeLower c (1 / 2) VV →
    cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff ≤
      Tcrit c.k c.m ka rd g VV (Vand c.k (c.u de))
def Factorisation : Prop :=
  ∀ (c : Cfg) (de de' : ℕ → ℝ) (ka T T' Y : ℝ) (l : ℕ), c.Ok → IsWord c.k de → IsWord c.k de' →
    0 < T → 0 < T' → 1 ≤ l → l + 2 ≤ c.k → de l ≠ de' l → Y ∈ c.cutI l →
    c.q de de' T T' Y ≠ 0 ∧ c.P Y ≠ 0 ∧ c.P (Y + 1) ≠ 0 ∧
    c.be ka de de' T T' Y =
      (ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹ * c.Nd (-Y) * c.U1 (-Y) *
        ∏ i ∈ Icc 1 (c.k - 1), c.rho de de' (-Y) i
def NodeBound : Prop :=
  ∀ (c : Cfg) (Y : ℝ) (l : ℕ), c.Ok → 1 ≤ l → l + 2 ≤ c.k → Y ∈ c.cutI l →
    c.Nd (-Y) ≤ Real.exp c.vth * c.prodb
def FirstBound : Prop :=
  ∀ (c : Cfg) (Y : ℝ) (l : ℕ), c.Ok → 1 ≤ l → l + 2 ≤ c.k → Y ∈ c.cutI l →
    0 < c.U1 (-Y) ∧ c.U1 (-Y) ≤ 1 / (c.a - c.v 1) ∧ 1 / (c.a - c.v 1) ≤ 2 / c.a
def PositionBefore : Prop :=
  ∀ (c : Cfg) (de de' : ℕ → ℝ) (Y : ℝ) (l i : ℕ), c.Ok → IsWord c.k de → IsWord c.k de' →
    1 ≤ i → i < l → l + 2 ≤ c.k → Y ∈ c.cutI l →
    c.rho de de' (-Y) i ≤ 1 + 2 / (4 * ((l : ℝ) - (i : ℝ)) - 1)
def PositionAfter : Prop :=
  ∀ (c : Cfg) (de de' : ℕ → ℝ) (Y : ℝ) (l i : ℕ), c.Ok → IsWord c.k de → IsWord c.k de' →
    1 ≤ l → l < i → i + 1 ≤ c.k → (i + 2 ≤ c.k ∨ c.top = false) → Y ∈ c.cutI l →
    c.rho de de' (-Y) i ≤ 1
def PositionAt : Prop :=
  ∀ (c : Cfg) (de de' : ℕ → ℝ) (Y : ℝ) (l : ℕ), c.Ok → IsWord c.k de → IsWord c.k de' →
    1 ≤ l → l + 2 ≤ c.k → de l ≠ de' l → Y ∈ c.cutI l →
    c.rho de de' (-Y) l = Real.sqrt ((c.v l + Y + 1) / (c.Del - (c.v l + Y))) ∧
      c.rho de de' (-Y) l ≤ Real.sqrt (14 * (c.v l + Y) / (5 * c.Del))
def PositionTop : Prop :=
  ∀ (c : Cfg) (de de' : ℕ → ℝ) (Y : ℝ) (l : ℕ), c.Ok → c.top = true →
    1 ≤ l → l + 2 ≤ c.k → Y ∈ c.cutI l →
    c.rho de de' (-Y) (c.k - 1) ≤ 4 * c.k * c.Del / c.bp
def ProdOneAddTwoDivLeSqrt : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∏ j ∈ Icc 1 p, (1 + 2 / (4 * (j : ℝ) - 1)) ≤ 3.3 * Real.sqrt p
def PositionsBefore : Prop :=
  ∀ (c : Cfg) (de de' : ℕ → ℝ) (Y : ℝ) (l : ℕ), c.Ok → IsWord c.k de → IsWord c.k de' →
    1 ≤ l → l + 2 ≤ c.k → Y ∈ c.cutI l →
    ∏ i ∈ Ico 1 l, c.rho de de' (-Y) i ≤ 3.3 * Real.sqrt c.k
noncomputable def AZero (c : Cfg) (bb : ℝ) : ℝ :=
  8 * 3.3 * Real.sqrt (14 / 5) * Real.exp c.vth / cOne c bb
def AZeroBound : Prop :=
  ∀ (c : Cfg) (bb : ℝ), c.Ok → c.Small bb → 0 < AZero c bb ∧ AZero c bb ≤ 160
noncomputable def tv (c : Cfg) (de de' : ℕ → ℝ) (ka rd g VV T T' : ℝ) : ℝ :=
  Real.sqrt (Tcrit c.k c.m ka rd g VV (Vand c.k (c.u de)) *
    Tcrit c.k c.m ka rd g VV (Vand c.k (c.u de')) / (T * T'))
def BetaOnCut : Prop :=
  ∀ (c : Cfg) (r : ℕ) (bb : ℝ) (de de' : ℕ → ℝ) (ka rd g VV T T' Y : ℝ) (l : ℕ),
    c.Ok → c.m = 2 * r + 2 → c.Small bb → IsWord c.k de → IsWord c.k de' →
    1 ≤ rd → ka = 2 * Real.pi / rd → 2 * Real.pi ≤ g → FormalDegreeLower c (1 / 2) VV →
    0 < T → 0 < T' → 1 ≤ l → l + 2 ≤ c.k → de l ≠ de' l → Y ∈ c.cutI l →
    g ^ c.m * c.be ka de de' T T' Y ≤
      AZero c bb * tv c de de' ka rd g VV T T' * Real.sqrt c.k *
        Real.sqrt ((c.v l + Y) / c.Del)
def DualLattice : Prop :=
  ∀ (E A : Type) [Field E] [One A] (ψ : E → A) (O La : Set E) (g : E), g ≠ 0 →
    {y : E | ∀ x ∈ O, ψ (g ^ 2 * x * y / g) = 1} = {y : E | ∀ x ∈ O, ψ (x * (g * y)) = 1} ∧
    ((∀ x ∈ O, g ^ 2 * x ∈ La) →
      {y : E | ∀ x ∈ La, ψ (x * y / g) = 1} ⊆ {y : E | ∀ x ∈ O, ψ (x * (g * y)) = 1})
noncomputable def xThreshold (m i : ℕ) (C ka N I A : ℝ) : ℝ :=
  C * ((ka ^ (m - 1))⁻¹ * A) * (C * ka * N / I) ^ (2 * i - 2)
noncomputable def lamThreshold (m i s : ℕ) (C ka N I A : ℝ) : ℝ :=
  C * ((ka ^ (m - 1))⁻¹ * A) * (C * ka * N / I) ^ (2 * (i - 1) + s - 1)
noncomputable def lamPrimeSq (m i : ℕ) (C ka N I A TT : ℝ) : ℝ :=
  C * ((ka ^ (m - 1))⁻¹ * A) * ka ^ (2 * i - 1) * (Real.sqrt TT)⁻¹ * (C * N / I) ^ (2 * (i - 1))
def GPowers : Prop :=
  ∀ (m i s : ℕ) (C ka N I A TT g : ℝ), 1 ≤ m → 1 ≤ i → 1 ≤ s → 0 < ka → 0 < g →
    ((ka / g) ^ (m - 1))⁻¹ * A = g ^ (m - 1) * ((ka ^ (m - 1))⁻¹ * A) ∧
    g * xThreshold m i C (ka / g) N I A = g ^ m * xThreshold m i C ka N I A / g ^ (2 * (i - 1)) ∧
    g * lamThreshold m i s C (ka / g) N I A = g ^ m * lamThreshold m i s C ka N I A / g ^ (2 * (i - 1) + s - 1) ∧
    g ^ 2 * lamPrimeSq m i C (ka / g) N I A TT =
      g ^ m * lamPrimeSq m i C ka N I A TT / g ^ (2 * (i - 1))
noncomputable def xHat (i : ℕ) (C ka N I g B : ℝ) : ℝ := C * B * (C * ka * N / (g * I)) ^ (2 * i - 2)
noncomputable def lamHat (i s : ℕ) (C ka N I g B : ℝ) : ℝ :=
  C * B * (C * ka * N / (g * I)) ^ (2 * (i - 1) + s - 1)
noncomputable def lamPrimeHat (i : ℕ) (C ka N I g B TT : ℝ) : ℝ :=
  Real.sqrt (C * B * (g ^ (2 * i - 2))⁻¹ * ka * (C * ka * N / I) ^ (2 * (i - 1)) * (Real.sqrt TT)⁻¹)
def NormalisedForms : Prop :=
  ∀ (m i s : ℕ) (C ka N I A TT g : ℝ), 1 ≤ m → 1 ≤ i → 1 ≤ s → 0 < ka → 0 < g → 0 ≤ C → 0 ≤ A →
    0 < I → 0 ≤ N → 0 < TT →
    g * xThreshold m i C (ka / g) N I A = xHat i C ka N I g (g ^ m * ((ka ^ (m - 1))⁻¹ * A)) ∧
    g * lamThreshold m i s C (ka / g) N I A = lamHat i s C ka N I g (g ^ m * ((ka ^ (m - 1))⁻¹ * A)) ∧
    g * Real.sqrt (lamPrimeSq m i C (ka / g) N I A TT) =
      lamPrimeHat i C ka N I g (g ^ m * ((ka ^ (m - 1))⁻¹ * A)) TT
def Placement : Prop :=
  ∀ (k r m : ℕ) (N Del : ℝ), m = 2 * r + 2 → N = 10 * (m : ℝ) → m ≤ k → 4 ≤ k →
    2000 * (k : ℝ) ^ 4 ≤ Del →
    N ^ 3 ≤ Del / 2 ∧
    (∀ j : ℕ, (j : ℝ) ≤ N - 1 → 5 / 2 + (j : ℝ) * N ^ 2 + 1 ≤ N ^ 3) ∧
    N ^ 3 / 2 ≤ N ^ 3 - 5 / 2 ∧
    Del / 4 ≤ Del / 2 - 5 / 2 ∧
    (k : ℝ) * N * ((r : ℝ) + 1) ^ 2 + N ^ 2 * ((r : ℝ) + 1) ^ 2 + N ^ 3 ≤ 1200 * (k : ℝ) ^ 4
def ThresholdProducts : Prop :=
  ∀ (ι : Type) [Fintype ι] (t B1 B : ι → ℝ) (k : ℕ) (C A0 Ct ka N I g Del TT : ℝ) (i s : ℕ),
    1 ≤ C → 0 < A0 → 0 < Ct → 0 < ka → ka ≤ Real.pi → 0 < N → 0 < I → 1 ≤ g → 0 < Del → 0 < TT →
    C * Real.pi * N / I ≤ 1 →
    (∀ w, 0 ≤ t w) → ∏ w, t w ≤ Ct →
    (∀ w, 0 ≤ B1 w ∧ B1 w ≤ A0 * t w * Real.sqrt k * Real.sqrt (N ^ 3 / Del)) →
    (∀ w, 0 ≤ B w ∧ B w ≤ A0 * t w * Real.sqrt k) →
    1 ≤ i →
    ∏ w, xHat 1 C ka N I g (B1 w) ≤
        Ct * (C * A0) ^ Fintype.card ι * (Real.sqrt (k * N ^ 3 / Del)) ^ Fintype.card ι ∧
    (2 ≤ i → ∏ w, xHat i C ka N I g (B w) ≤
        Ct * (C * A0 * Real.sqrt k) ^ Fintype.card ι * (C * Real.pi * N / I) ^ (2 * Fintype.card ι)) ∧
    (2 ≤ s → ∏ w, lamHat i s C ka N I g (B w) ≤
        Ct * (C * A0 * Real.sqrt k) ^ Fintype.card ι * (C * Real.pi * N / I) ^ Fintype.card ι) ∧
    ∏ w, lamPrimeHat i C ka N I g (B w) TT ≤
        Real.sqrt Ct *
          (Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT)) ^ Fintype.card ι
def ThetaLower : Prop :=
  ∀ (f k : ℕ) (C A0 Ct N I Del TT Th : ℝ),
    1 ≤ f → 1 ≤ k → 1 ≤ C → 0 < A0 → 1 ≤ Ct → 0 < N → 0 < I → 0 < Del → 0 < TT → 0 < Th →
    C * Real.pi * N / I ≤ 1 →
    ((Th ^ f)⁻¹ ≤ Ct * (C * A0) ^ f * (Real.sqrt (k * N ^ 3 / Del)) ^ f ∨
      (Th ^ f)⁻¹ ≤ Ct * (C * A0 * Real.sqrt k) ^ f * (C * Real.pi * N / I) ^ (2 * f) ∨
      (Th ^ f)⁻¹ ≤ Ct * (C * A0 * Real.sqrt k) ^ f * (C * Real.pi * N / I) ^ f ∨
      (Th ^ f)⁻¹ ≤ Real.sqrt Ct * (Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT)) ^ f) →
    min (min (Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0))
        (I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N)))
      (Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k))) ≤ Th
noncomputable def cExp (CDel cT Cb : ℝ) : ℝ := (1 / 2) * min ((CDel - 4) / 2) ((cT * Cb - 1) / 4)
def ThetaPower : Prop :=
  ∀ (C A0 Ct CDel cT Cb : ℝ), 1 ≤ C → 0 < A0 → 1 ≤ Ct → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ (k m f : ℕ) (bb N I Del TT : ℝ), k0 ≤ k → 2 ≤ m → m ≤ f → f ≤ k →
      N = 10 * (m : ℝ) → I = Del / 2 - 5 / 2 → (k : ℝ) ^ (Cb / 2) ≤ bb →
      ((k : ℝ) * f * Real.log bb) ^ CDel ≤ Del → (bb ^ (cT * m)) ^ 2 ≤ TT →
      C * Real.pi * N / I ≤ 1 ∧
      (k : ℝ) ^ cExp CDel cT Cb ≤
        min (min (Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0))
            (I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N)))
          (Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k)))
def FinalSmall : Prop :=
  ∀ (C c : ℝ), 1 ≤ C → 0 < c →
    ∃ k0 : ℕ, ∀ (k r f : ℕ) (bb Cf Th : ℝ), k0 ≤ k → 2 * r + 2 ≤ f → 1 ≤ bb →
      16 ≤ c * Cf → Cf * Real.log bb ≤ f * Real.log k → (k : ℝ) ^ c ≤ Th →
      (r : ℝ) * (C / Th) ^ f ≤ 1 ∧ C * ((r : ℝ) + 1) * (C / Th) ^ f ≤ (bb ^ 7)⁻¹
structure Glob (ι : Type) [Fintype ι] where
  k : ℕ
  r : ℕ
  Del : ℝ
  vlast : ι → ℝ
  b : ι → ℕ → ℝ
  a : ι → ℝ
  top : ι → Bool
  bp : ι → ℝ
  v : ℝ
  dF : ℝ
  Lv : ℕ → ℝ
  vol : ℕ → ℝ
  g1 : ℕ
  g2 : ℕ
  dsig : ι → ℝ
namespace Glob
variable {ι : Type} [Fintype ι] (G : Glob ι)
def place (w : ι) : Cfg :=
  { k := G.k, m := 2 * G.r + 2, Del := G.Del, vlast := G.vlast w, b := G.b w, a := G.a w,
    top := G.top w, bp := G.bp w }
noncomputable def size (de : ℕ → ℝ) (T : ℕ) (du : ℝ) : SizeData ι :=
  { k := G.k, r := G.r, v := G.v, dF := G.dF, Lv := G.Lv, vol := G.vol, g1 := G.g1, g2 := G.g2,
    T := T, dsig := G.dsig, Vu := fun w => Vand G.k ((G.place w).u de), du := du }
def m : ℕ := 2 * G.r + 2
def f (_G : Glob ι) : ℕ := Fintype.card ι
noncomputable def ka : ℝ := Real.pi / G.v
noncomputable def g : ℝ := (G.g1 : ℝ) * (G.g2 : ℝ)
noncomputable def N : ℝ := 4 * 5 * ((G.r : ℝ) + 1)
noncomputable def lenI : ℝ := G.Del / 2 - 5 / 2
noncomputable def supI (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) (w : ι) : ℝ :=
  sSup ((fun Y => G.g ^ G.m * (G.place w).be G.ka de de' T T' Y) '' (G.place w).cutI l)
noncomputable def cutSupLong (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) (w : ι) : ℝ :=
  sSup ((fun Y => G.g ^ G.m * (G.place w).be G.ka de de' T T' Y) '' (G.place w).cutIntervalLong l G.N)
def thrSet (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) : Set ℝ :=
  {x | ∃ i : ℕ, 1 ≤ i ∧ i ≤ G.r + 1 ∧
    ((i = 1 ∧ x = ∏ w, xHat 1 C G.ka G.N G.lenI G.g (G.cutSupLong de de' T T' l w)) ∨
     (2 ≤ i ∧ x = ∏ w, xHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w)) ∨
     (∃ s : ℕ, 2 ≤ s ∧ s + i ≤ G.r + 2 ∧
        x = ∏ w, lamHat i s C G.ka G.N G.lenI G.g (G.supI de de' T T' l w)) ∨
     x = ∏ w, lamPrimeHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T'))}
structure Hyp (bb CDel Cb : ℝ) : Prop where
  hplace : ∀ w, (G.place w).Ok
  hsmall : ∀ w, (G.place w).Small bb
  hbb : 1 < bb
  hmf : G.m ≤ G.f
  hfk : G.f ≤ G.k
  hv : 1 ≤ G.v
  hdF : G.dF = (2 * G.v) ^ G.f
  hg1 : ((G.k : ℝ) * bb) ^ 8 ≤ G.g1
  hg2 : ((G.k : ℝ) * bb) ^ 8 ≤ G.g2
  hnode : ∀ w, ∀ j : ℕ, 1 ≤ j → j ≤ G.m → (G.k : ℝ) ^ Cb ≤ G.b w j
  hDel : ((G.k : ℝ) * G.f * Real.log bb) ^ CDel ≤ G.Del
  hvol : 0 < G.vol G.k
end Glob
def TWords : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : Glob ι) (bb CDel Cb C0 Gam : ℝ) (de de' : ℕ → ℝ) (T T' : ℕ)
    (du du' : ℝ),
    G.Hyp bb CDel Cb → IsWord G.k de → IsWord G.k de' → 2 ≤ T → 2 ≤ T' →
    (G.size de T du).MassRatios → (G.size de T du).LBound →
    (G.size de T du).ColumnCount → (G.size de' T' du').ColumnCount →
    (∀ w, 0 < G.dsig w) → 1 ≤ C0 → 0 < Gam →
    (G.size de T du).ChoiceOfT C0 Gam → (G.size de' T' du').ChoiceOfT C0 Gam →
    (G.f : ℝ) * (8 / 2 ^ G.k) ≤ Real.log 2 →
    (2 * C0) ^ (4 / ((G.k : ℝ) * G.f)) ≤ Real.exp (1 / 4) →
    Real.exp (-1) ≤ (T : ℝ) / T' ∧ (T : ℝ) / T' ≤ Real.exp 1
def SizesMain : Prop :=
  ∀ (CA C0 CG CDel cT Cb : ℝ), 1 ≤ CA → 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb →
    1 < cT * Cb →
    ∃ k0 : ℕ, ∀ (ι : Type) [Fintype ι] (G : Glob ι) (bb C' Cf Th : ℝ) (de de' : ℕ → ℝ) (T T' : ℕ)
      (du du' : ℝ) (l : ℕ),
      k0 ≤ G.k → G.Hyp bb CDel Cb →
      IsWord G.k de → IsWord G.k de' → 1 ≤ l → l + 2 ≤ G.k → de l ≠ de' l →
      bb ^ (cT * G.m) ≤ T → bb ^ (cT * G.m) ≤ T' →
      8 * CG ≤ C' → C' * (G.m : ℝ) ^ 5 * G.f * Real.log bb ≤ G.k →
      (G.size de T du).MassRatios → (G.size de T du).LBound →
      (G.size de T du).ColumnCount → (G.size de' T' du').ColumnCount →
      (G.size de T du).ChoiceOfT C0 (Real.exp (CG * (G.m : ℝ) ^ 5 * G.f * Real.log bb)) →
      (G.size de' T' du').ChoiceOfT C0 (Real.exp (CG * (G.m : ℝ) ^ 5 * G.f * Real.log bb)) →
      (∀ w, FormalDegreeLower (G.place w) (1 / 2) ((G.size de T du).VV w)) →
      0 < Th → IsGreatest (G.thrSet CA de de' T T' l) ((Th ^ G.f)⁻¹) →
      (G.k : ℝ) ^ cExp CDel cT Cb ≤ Th ∧
        (16 ≤ cExp CDel cT Cb * Cf → Cf * Real.log bb ≤ G.f * Real.log G.k →
          (G.r : ℝ) * (CA / Th) ^ G.f ≤ 1 ∧
            CA * ((G.r : ℝ) + 1) * (CA / Th) ^ G.f ≤ (bb ^ 7)⁻¹)
end Formalism.FourierDecayAlt.Sz


