-- Prove2me | Definitions.Def_Formalism_FrobeniusBaseCase_Statement
-- name    : Formalism_FrobeniusBaseCase_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:50.288927+00:00
-- url     : https://prove2.me/theorems/8795c772-b207-439b-b02f-135c4607d9d5
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
namespace Formalism.BaseCaseIdentities
noncomputable section
open Classical
def Lnum (l i : ℕ) : ℝ := (l : ℝ) ^ i
def qnum (l : ℕ) : ℝ := (l : ℝ) ^ 2
def rho (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 1)
def gam (l : ℕ) : ℝ := (l : ℝ) * rho l
def sg (l i : ℕ) : ℝ := 3 / (8 * (l : ℝ) ^ i)
def del (l i : ℕ) : ℝ := 1 / (8 * (l : ℝ) ^ i)
def Enum (l i : ℕ) : ℝ := 1 + ((l : ℝ) ^ i - (l : ℝ)) * rho l
def r1 (l i : ℕ) : ℝ := rho l + 1 / (2 * (l : ℝ) ^ i)
def r2 (l : ℕ) : ℝ := rho l + 1 / 2
def Kn (i : ℕ) : ℕ := (i + 1) / 2
def s0 (i : ℕ) : ℕ := (i - 1) / 2
def eNum (l s : ℕ) : ℕ := ((l ^ 2) ^ s - 1) / (l ^ 2 - 1)
def Id20 : Prop := ∀ l i : ℕ, 2 ≤ l →
  rho l + gam l = 1 / ((l : ℝ) - 1) ∧ r1 l i - del l i = rho l + sg l i
def SlopeSumIdentity : Prop := ∀ l i : ℕ, 2 ≤ l →
  Lnum l i * r1 l i + r2 l = Enum l i + 1 / ((l : ℝ) - 1)
def GeomSlopeIdentity : Prop := ∀ l i : ℕ, 2 ≤ l → Odd i →
  1 + (l : ℝ) * (qnum l ^ s0 i - 1) / (qnum l - 1) = Enum l i
def SqMulIdentity : Prop := ∀ l : ℕ, 2 ≤ l → qnum l * rho l - 1 = rho l
def PowMulThreeEighthsIdentity : Prop := ∀ l i : ℕ, 2 ≤ l → Odd i → qnum l ^ Kn i * sg l i = 3 * (l : ℝ) / 8
def IdE : Prop := ∀ l s : ℕ, 2 ≤ l →
  eNum l 0 = 0 ∧ eNum l (s + 1) = 1 + l ^ 2 * eNum l s ∧ eNum l s * (l ^ 2 - 1) + 1 = (l ^ 2) ^ s
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}
def HasWt (v : AddValuation k (WithTop ℝ)) (r w : ℝ) (f : MvPowerSeries Z k) : Prop :=
  ∀ A : Z →₀ ℕ, (w : WithTop ℝ) ≤ v (coeff A f) + (((A.degree : ℕ) : ℝ) * r : ℝ)
def OrdGE (n : ℕ) (f : MvPowerSeries Z k) : Prop :=
  ∀ A : Z →₀ ℕ, A.degree < n → coeff A f = 0
def NoConst (t : C → MvPowerSeries Z k) : Prop := ∀ c, OrdGE 1 (t c)
def frob (N : ℕ) (f : MvPowerSeries Z k) : MvPowerSeries Z k :=
  fun B => if ∀ d, N ∣ B d then (coeff (B.mapRange (· / N) (Nat.zero_div N)) f) ^ N else 0
def FrobSpec (k : Type*) [Field k] (Z : Type*) : Prop := ∀ (N : ℕ) (f : MvPowerSeries Z k), 1 ≤ N →
  (∀ A : Z →₀ ℕ, coeff (N • A) (frob N f) = (coeff A f) ^ N) ∧
  (∀ B : Z →₀ ℕ, (¬ ∃ A : Z →₀ ℕ, B = N • A) → coeff B (frob N f) = 0)
structure Data (k : Type*) [Field k] (Z : Type*) (C : Type*) where

  v : AddValuation k (WithTop ℝ)

  l : ℕ
  l_prime : l.Prime
  l_ge : 3 ≤ l
  v_l : v (l : k) = 1

  i : ℕ
  i_odd : Odd i

  good : C → Prop

  lev : C → ℕ
  pure_good : ∀ c, lev c < Kn i → good c

  ι : Z → C
  ι_inj : Function.Injective ι
  ι_lev : ∀ d, lev (ι d) = 0

  al : C → ℕ → C → k

  g : C → C → k

  lam : C → C → k
  al_all : ∀ (c : C) (j : ℕ) (b : C), ((-(j : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c j b)
  al_good : ∀ c, good c → ∀ (j : ℕ) (b : C), 1 ≤ j → ((-((j : ℝ) - 1) : ℝ) : WithTop ℝ) ≤ v (al c j b)
  al_one : ∀ c, good c → ∀ b, al c 1 b = 0
  al_two : ∀ c, lev c < Kn i → ∀ b, al c 2 b = (l : k)⁻¹ * (g c b + (l : k) * lam c b)
  g_int : ∀ c b, 0 ≤ v (g c b)
  lam_int : ∀ c b, 0 ≤ v (lam c b)

  g_supp : ∀ c, lev c + 1 < Kn i → ∀ b, lev b ≠ lev c + 1 → g c b = 0
namespace Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
def K : ℕ := Kn D.i
def q : ℕ := D.l ^ 2
def rad : ℝ := rho D.l + sg D.l D.i
def top : ℝ := 1 + rho D.l
def Wt (w : ℝ) (f : MvPowerSeries Z k) : Prop := HasWt D.v D.rad w f
def zvec : C → MvPowerSeries Z k := fun b => ∑ d, if D.ι d = b then X d else 0
def m : ℕ → C → MvPowerSeries Z k
  | 0 => D.zvec
  | s + 1 => fun b => MvPowerSeries.C (-(D.l : k)⁻¹) *
      ∑ c, frob D.q (m s c) * MvPowerSeries.C (D.g c b)
def PsiPartial (N : ℕ) (t : C → MvPowerSeries Z k) : C → MvPowerSeries Z k := fun b =>
  D.zvec b - ∑ c, ∑ j ∈ Finset.Icc 1 N, MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j)
def Psi (t : C → MvPowerSeries Z k) : C → MvPowerSeries Z k := fun b A =>
  coeff A (D.zvec b) -
    ∑ c, ∑ j ∈ Finset.Icc 1 A.degree, D.al c j b * coeff A (t c ^ (D.l ^ j))
def InWTo (J : ℕ) (t : C → MvPowerSeries Z k) : Prop :=
  (∀ c, D.lev c < J → D.Wt D.top (t c - D.m (D.lev c) c)) ∧
  (∀ c, J ≤ D.lev c → D.Wt D.top (t c))
def InW (t : C → MvPowerSeries Z k) : Prop := D.InWTo D.K t
def start : C → MvPowerSeries Z k := fun c => if D.lev c < D.K then D.m (D.lev c) c else 0
def PsiIsLimit : Prop := ∀ t : C → MvPowerSeries Z k, NoConst t →
  ∀ (b : C) (A : Z →₀ ℕ) (N : ℕ), A.degree ≤ N →
    coeff A (D.Psi t b) = coeff A (D.PsiPartial N t b)
def ChainI : Prop := ∀ s, s < D.K →
  (∃ P : C → Z → k, (∀ c d, 0 ≤ D.v (P c d)) ∧ (∀ c, D.lev c ≠ s → ∀ d, P c d = 0) ∧
    ∀ c, D.m s c = MvPowerSeries.C ((-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹) *
      ∑ d, MvPowerSeries.C (P c d) * X d ^ (D.q ^ s)) ∧
  ∀ c, D.Wt (rho D.l + qnum D.l ^ s * sg D.l D.i) (D.m s c)
def Contraction : Prop := ∀ (t t' : C → MvPowerSeries Z k) (n : ℕ), NoConst t → NoConst t' →
  (∀ c, OrdGE (n + 1) (t c - t' c)) → ∀ b, OrdGE (n + D.l) (D.Psi t b - D.Psi t' b)
def FixedPoint : Prop :=
  (∃! t : C → MvPowerSeries Z k, NoConst t ∧ D.Psi t = t) ∧
  ∀ t0 t : C → MvPowerSeries Z k, NoConst t0 → NoConst t → D.Psi t = t →
    ∀ (n : ℕ) (A : Z →₀ ℕ), A.degree ≤ n → ∀ c, coeff A ((D.Psi)^[n] t0 c) = coeff A (t c)
def StartInW : Prop := NoConst D.start ∧ D.InW D.start
def PsiW : Prop := ∀ t : C → MvPowerSeries Z k, NoConst t → D.InW t →
  NoConst (D.Psi t) ∧ D.InW (D.Psi t)
def ChainII : Prop := ∀ t : C → MvPowerSeries Z k, NoConst t → D.Psi t = t → D.InW t
def SecondWay : Prop :=
  D.InWTo 1 D.zvec ∧
  (∀ (J : ℕ) (t : C → MvPowerSeries Z k), 1 ≤ J → J ≤ D.K → NoConst t → D.InWTo J t →
    D.InWTo (min (J + 1) D.K) (D.Psi t)) ∧
  ∀ n, D.K - 1 ≤ n → D.InW ((D.Psi)^[n] D.zvec)
def FrobeniusBaseCaseIdentity : Prop := D.i = 1 → D.InW D.zvec
end Data
def BaseCaseFalse : Prop := ∀ l i : ℕ, l.Prime → 3 ≤ l → Odd i → 3 ≤ i →
  ∃ D : Data ℚ Unit (Fin 2), D.l = l ∧ D.i = i ∧ ¬ D.InW D.zvec
end
end Formalism.BaseCaseIdentities


