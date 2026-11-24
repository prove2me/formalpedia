-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
-- name    : Formalism_HermitianCurvature_OperatorsCommuteTranslations
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T14:26:08.20115+00:00
-- url     : https://prove2.me/theorems/d56f771b-97e3-400b-b2ee-f2ed8e60b96a
-- title:
--   Operators Commute Translations
-- statement:
--   Definitions and structural lemmas for Operators Commute Translations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/OperatorsCommuteTranslations.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace Formalism.FourierDecayAlt.C3
open Formalism.REAL Formalism.QuantumDeterminants
def InNp (k r : ℕ) (p q : Fin (2 * r + k + 1)) : Prop :=
  p.val < q.val ∧ ¬ (r ≤ p.val ∧ p.val ≤ r + k ∧ r ≤ q.val ∧ q.val ≤ r + k)
def dpsiP (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) : ℂ :=
  if p.val < r ∧ q.val < r then (if q.val = p.val + 1 then 1 else 0)
  else if p.val < r ∧ r ≤ q.val ∧ q.val ≤ r + k then (if p.val + 1 = r then z' q else 0)
  else if r ≤ p.val ∧ p.val ≤ r + k ∧ r + k < q.val then
    (if q.val = r + k + 1 then herm (Hpk k r) (bvec p) z' else 0)
  else if r + k < p.val ∧ r + k < q.val then (if q.val = p.val + 1 then 1 else 0)
  else 0
def rgen {A : Type*} [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) : Set A :=
  {x | ∃ p q, InNp k r p q ∧ x = E p q - algebraMap ℂ A (dpsiP k r z' p q)}
def RightRuleFn {A M : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (z' : Fin (2 * r + k + 1) → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M) : Prop :=
  ∀ (x : A) (p q : Fin (2 * r + k + 1)), InNp k r p q → La (x * E p q) = dpsiP k r z' p q • La x
def xR (k r m : ℕ) (h : m ≤ r) (l : Fin m) : Fin (2 * r + k + 1) := eI k r (Fin.castLE h l)
def sR (k r m : ℕ) (h : m ≤ r) (l : Fin m) : Fin (2 * r + k + 1) := esI k r (Fin.castLE h l)
def PeelingOmittedColumn : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (m : ℕ) (hm : m + 1 ≤ r) (i : Fin (m + 1)) (u : ℂ),
    qminor E (xR k r m (by omega)) (fun l : Fin m => xR k r (m + 1) hm (i.succAbove l)) u -
      qminor E (xR k r i.val (by have := i.isLt; omega)) (xR k r i.val (by have := i.isLt; omega)) u ∈
      Ideal.span (rgen k r z' E)
def PeelingCovector : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k m : ℕ) (z' yb : Fin (2 * (m + 1) + k + 1) → ℂ)
    (E : Fin (2 * (m + 1) + k + 1) → Fin (2 * (m + 1) + k + 1) → A) (i : Fin (m + 1)) (u : ℂ),
    inWb k (m + 1) z' →
    (∑ w : Fin (k + 1), herm (Hpk k (m + 1)) (bvec (wI k (m + 1) w)) yb •
        qminor E (xR k (m + 1) (m + 1) le_rfl)
          (Fin.snoc (α := fun _ => Fin (2 * (m + 1) + k + 1))
            (fun l : Fin m => xR k (m + 1) (m + 1) le_rfl (i.succAbove l)) (wI k (m + 1) w)) u) -
      herm (Hpk k (m + 1)) z' yb •
        qminor E (xR k (m + 1) i.val (by have := i.isLt; omega)) (xR k (m + 1) i.val (by have := i.isLt; omega)) u ∈
      Ideal.span (rgen k (m + 1) z' E)
def PeelingDualColumn : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A), GlRel E →
    ∀ (m : ℕ) (hm : m + 1 ≤ r) (i : Fin (m + 1)) (ell : ℂ),
    qminor E (fun l : Fin m => sR k r (m + 1) hm (i.succAbove l)) (sR k r m (by omega)) (ell + (m : ℂ) - 1) -
      qminor E (sR k r i.val (by have := i.isLt; omega)) (sR k r i.val (by have := i.isLt; omega))
        (ell + ((i.val : ℕ) : ℂ) - 1) ∈
      Ideal.span (rgen k r z' E)
def PeelingDualCovector : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k m : ℕ) (z' yb : Fin (2 * (m + 1) + k + 1) → ℂ)
    (E : Fin (2 * (m + 1) + k + 1) → Fin (2 * (m + 1) + k + 1) → A), GlRel E →
    ∀ (i : Fin (m + 1)) (ell : ℂ), inWb k (m + 1) z' → inWb k (m + 1) yb →
    (∑ w : Fin (k + 1), yb (wI k (m + 1) w) •
        qminor E
          (Fin.snoc (α := fun _ => Fin (2 * (m + 1) + k + 1))
            (fun l : Fin m => sR k (m + 1) (m + 1) le_rfl (i.succAbove l)) (wI k (m + 1) w))
          (sR k (m + 1) (m + 1) le_rfl) (ell + (m : ℂ))) -
      herm (Hpk k (m + 1)) yb z' •
        qminor E (sR k (m + 1) i.val (by have := i.isLt; omega)) (sR k (m + 1) i.val (by have := i.isLt; omega))
          (ell + ((i.val : ℕ) : ℂ) - 1) ∈
      Ideal.span (rgen k (m + 1) z' E)
def Zb (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (a b : ℕ) : ℂ :=
  if ha : a < i0 then (if hb : b < i0 then h ⟨a, ha⟩ ⟨b, hb⟩ else 0)
  else if i0 ≤ b ∧ a < i0 + s ∧ b < i0 + s ∧ (a - i0) + (b - i0) + 1 = s then t else 0
def Dlead (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (n : ℕ) : ℂ :=
  (Matrix.of fun a b : Fin n => Zb i0 s h t a.val b.val).det
def sgnW (m : ℕ) : ℂ := (-1) ^ (m * (m - 1) / 2)
def AntiDiagDet : Prop :=
  ∀ m : ℕ, (Matrix.of fun a b : Fin m => if a.val + b.val + 1 = m then (1 : ℂ) else 0).det = sgnW m
def DleadZb : Prop :=
  ∀ (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ),
    Dlead i0 s h t i0 = h.det ∧ Dlead i0 s h t (i0 + s) = h.det * t ^ s * sgnW s
def MinorsFirstCase : Prop :=
  ∀ (i0 s' : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (c : Fin (i0 + s' + 1)),
    (Matrix.of fun a l : Fin (i0 + s') => Zb i0 (s' + 1) h t a.val (c.succAbove l).val).det =
      if c.val = i0 then h.det * t ^ s' * sgnW s' else 0
def MinorsThirdCase : Prop :=
  ∀ (i0 s'' : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ),
    (Matrix.of fun a b : Fin (i0 + s'') =>
        Zb i0 (s'' + 2) h t ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove a).val
          ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove b).val).det =
      h.det * t ^ s'' * sgnW s''
def SignE : Prop :=
  ∀ s : ℕ, sgnW s * sgnW (s + 1) = (-1) ^ s ∧ sgnW s * sgnW (s + 2) = -1
def keyS (k r : ℕ) (p : Fin (2 * r + k + 1)) : ℕ := if r + k < p.val then 2 * r + k - p.val else p.val + r
open scoped Classical in

def AAx {A : Type*} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r) (u : ℂ) : A :=
  ∑ c : Fin m → Fin (2 * r + k + 1),
    if StrictMono c then (Matrix.of fun a l : Fin m => xi (Fin.castLE hm a) (c l)).det • qminor E (xR k r m hm) c u
    else 0
open scoped Classical in

def AAv {A : Type*} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r) (ell : ℂ) : A :=
  ∑ B : Fin m → Fin (2 * r + k + 1),
    if StrictMono (fun l => keyS k r (B l)) then
      (Matrix.of fun a l : Fin m => y (Fin.castLE hm a) (B l)).det • qminor E B (sR k r m hm) (ell + (m : ℂ) - 1)
    else 0
def ExpansionOmittedColumn : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (z' : Fin (2 * r + k + 1) → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t u : ℂ)
    (hs : 1 ≤ s) (hj : i0 + s ≤ r),
    RightRuleFn k r z' E La → h.det ≠ 0 → t ≠ 0 →
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      xi a p = if p.val < i0 + s then Zb i0 s h t a.val p.val else 0) →
    (Dlead i0 s h t (i0 + s))⁻¹ • La (AAx k r E xi (i0 + s - 1) (by omega) u) =
      ((-1 : ℂ) ^ (s - 1) * t⁻¹) • ((Dlead i0 s h t i0)⁻¹ • La (AAx k r E xi i0 (by omega) u))
def ExpansionDualColumn : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (z' : Fin (2 * r + k + 1) → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t ell : ℂ)
    (hs : 1 ≤ s) (hj : i0 + s ≤ r),
    GlRel E → RightRuleFn k r z' E La → h.det ≠ 0 → t ≠ 0 →
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      y a p = if r + k < p.val ∧ 2 * r + k - p.val < i0 + s then star (Zb i0 s h t a.val (2 * r + k - p.val))
        else 0) →
    (star (Dlead i0 s h t (i0 + s)))⁻¹ • La (AAv k r E y (i0 + s - 1) (by omega) ell) =
      ((-1 : ℂ) ^ (s - 1) * (star t)⁻¹) • ((star (Dlead i0 s h t i0))⁻¹ • La (AAv k r E y i0 (by omega) ell))
def ExpansionCovector : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (z' yb : Fin (2 * r + k + 1) → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t u : ℂ)
    (hs : 2 ≤ s) (hj : i0 + s = r + 1),
    RightRuleFn k r z' E La → h.det ≠ 0 → t ≠ 0 → inWb k r z' → inWb k r yb → herm (Hpk k r) z' yb = t →
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val ≠ i0 →
      xi a p = if p.val < r ∧ p.val ≠ i0 then Zb i0 s h t a.val p.val else 0) →
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val = i0 → xi a p = herm (Hpk k r) (bvec p) yb) →
    (Dlead i0 s h t (r + 1))⁻¹ • La (AAx k r E xi r le_rfl u) =
      ((-1 : ℂ) ^ (s - 1) * t⁻¹) • ((Dlead i0 s h t i0)⁻¹ • La (AAx k r E xi i0 (by omega) u))
def ExpansionDualCovector : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (z' yb : Fin (2 * r + k + 1) → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t ell : ℂ)
    (hs : 2 ≤ s) (hj : i0 + s = r + 1),
    GlRel E → RightRuleFn k r z' E La → h.det ≠ 0 → t ≠ 0 → inWb k r z' → inWb k r yb →
    herm (Hpk k r) z' yb = t →
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val ≠ i0 →
      y a p = if r + k < p.val ∧ 2 * r + k - p.val ≠ i0 then star (Zb i0 s h t a.val (2 * r + k - p.val))
        else 0) →
    (∀ (a : Fin r), a.val = i0 → y a = yb) →
    (star (Dlead i0 s h t (r + 1)))⁻¹ • La (AAv k r E y r le_rfl ell) =
      ((-1 : ℂ) ^ (s - 1) * (star t)⁻¹) • ((star (Dlead i0 s h t i0))⁻¹ • La (AAv k r E y i0 (by omega) ell))
def ExpansionFirstCaseFromComponents : Prop := PeelingOmittedColumn → MinorsFirstCase → DleadZb → SignE → ExpansionOmittedColumn
def ExpansionSecondCaseFromComponents : Prop := Formalism.FourierDecayAlt.Q.RowForm → PeelingDualColumn → MinorsFirstCase → DleadZb → SignE → ExpansionDualColumn
def ExpansionThirdCaseFromComponents : Prop := PeelingOmittedColumn → PeelingCovector → MinorsThirdCase → DleadZb → SignE → ExpansionCovector
def ExpansionFourthCaseFromComponents : Prop := PeelingDualColumn → PeelingDualCovector → MinorsThirdCase → DleadZb → SignE → ExpansionDualCovector
def PeelOfParts : Prop := Formalism.FourierDecayAlt.Q.RowForm → PeelingOmittedColumn ∧ PeelingCovector ∧ PeelingDualColumn ∧ PeelingDualCovector
def LeftRuleBig {A M : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] (k r : ℕ) (c : Fin r → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M) : Prop :=
  ∀ (x : A) (a b : Fin r), b.val < a.val →
    La (E (eI k r a) (eI k r b) * x) = (if a.val = b.val + 1 then c a / c b else 0) • La x
def LastColumnChain : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (La : A →ₗ[ℂ] M), GlRel E → (∀ l, c l ≠ 0) → RightRuleFn k r z' E La → LeftRuleBig k r c E La →
    ∀ (m : ℕ) (hm : m + 2 ≤ r) (u : ℂ),
      La (qminor E (xR k r (m + 2) hm) (xR k r (m + 2) hm) u) =
        La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
            Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) -
          (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u)
def LastColumnChainFromComponents : Prop := Formalism.FourierDecayAlt.Q.ExpLastCol → Formalism.FourierDecayAlt.Q.RowForm → LastColumnChain
def RuleRightDpsi : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (l : Fin r) (j : Fin (Formalism.FourierDecayAlt.Q.mdim k r l.succ)), inWb k r z' →
    InNp k r (eI k r l) (Formalism.FourierDecayAlt.Q.posL k r l.succ j) ∧
    Formalism.FourierDecayAlt.Q.xv k r z' l.succ j = dpsiP k r z' (eI k r l) (Formalism.FourierDecayAlt.Q.posL k r l.succ j) ∧
    InNp k r (Formalism.FourierDecayAlt.Q.posL k r l.succ j) (esI k r l) ∧
    Formalism.FourierDecayAlt.Q.xbv k r z' l.succ j = dpsiP k r z' (Formalism.FourierDecayAlt.Q.posL k r l.succ j) (esI k r l)
def dEll (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hr : 1 ≤ r) : ℂ :=
  (∑ a : Fin r, if h : a.val + 1 < r then X (eI k r a) (eI k r ⟨a.val + 1, h⟩) else 0) +
    (X *ᵥ z') (eI k r ⟨r - 1, by omega⟩)
def DpsiDerivation : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hr : 1 ≤ r), inWb k r z' → Xᴴ * Hpk k r + Hpk k r * X = 0 → (∀ p q, ¬ InNp k r p q → X p q = 0) →
    ∑ p, ∑ q, X p q * dpsiP k r z' p q = dEll k r z' X hr - star (dEll k r z' X hr)
def LeadAA : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r), ∃ B : Fin m → A, ∀ u : ℂ,
      AAx k r E xi m hm u =
        algebraMap ℂ A (u ^ m * (Matrix.of fun a b : Fin m => xi (Fin.castLE hm a) (xR k r m hm b)).det) +
          ∑ l : Fin m, algebraMap ℂ A (u ^ (l : ℕ)) * B l
def LeadAAv : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r), ∃ B : Fin m → A, ∀ ell : ℂ,
      AAv k r E y m hm ell =
        algebraMap ℂ A (ell ^ m * (Matrix.of fun a b : Fin m => y (Fin.castLE hm a) (sR k r m hm b)).det) +
          ∑ l : Fin m, algebraMap ℂ A (ell ^ (l : ℕ)) * B l
def XiYZhat : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (a b : Fin r), g ∈ UH (Hpk k r) →
    herm (Hpk k r) (g *ᵥ bvec (eI k r b)) (bvec (eI k r a)) = Zhat k r z z' g a.castSucc b.castSucc ∧
    (g⁻¹ *ᵥ bvec (eI k r a)) (esI k r b) = star (Zhat k r z z' g a.castSucc b.castSucc)
open scoped Classical in

def AAop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r m : ℕ) (hm : m ≤ r) (u : ℂ)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E := fun g =>
  ∑ c : Fin m → Fin (2 * r + k + 1),
    if StrictMono c then
      (Matrix.of fun a l : Fin m => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))).det •
        qminorOp (EabH (Hpk k r)) (xR k r m hm) c u f g
    else 0
open scoped Classical in

def AAvop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r m : ℕ) (hm : m ≤ r) (ell : ℂ)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E := fun g =>
  ∑ B : Fin m → Fin (2 * r + k + 1),
    if StrictMono (fun l => keyS k r (B l)) then
      (Matrix.of fun a l : Fin m => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (B l)).det •
        qminorOp (EabH (Hpk k r)) B (sR k r m hm) (ell + (m : ℂ) - 1) f g
    else 0
def OperatorsCommuteTranslations : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (m : ℕ)
    (hm : m ≤ r) (u ell : ℂ) (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E),
    inWb k r z → inWb k r z' → SmoothOnH (Hpk k r) f →
    ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', ∀ g, inUH (Hpk k r) g →
      AAop k r m hm u (fun x => f (s * x * s')) g = AAop k r m hm u f (s * g * s') ∧
      AAvop k r m hm ell (fun x => f (s * x * s')) g = AAvop k r m hm ell f (s * g * s')
def N0set (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧ (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a)) ∧ g *ᵥ z' = z' ∧
    (∀ p q : Fin (2 * r + k + 1), r ≤ q.val → q.val ≤ r + k → r ≤ p.val → g p q = if p = q then 1 else 0) ∧
    (∀ p q : Fin (2 * r + k + 1), r + k < q.val → r + k < p.val → g p q = if p = q then 1 else 0)}
def IsotropicNormalFormPartial : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ),
    inWb k r z' →
    (∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0) →
    (Matrix.of fun a b : Fin j => y a (sR k r j hj b)).det ≠ 0 →
    (∀ a, herm (Hpk k r) z' (y a) = 0) →
    (∀ a a', herm (Hpk k r) (y a) (y a') = 0) →
    ∃ n0 ∈ N0set k r z', ∃ y' : Fin j → Fin (2 * r + k + 1) → ℂ, ∀ a,
      n0 *ᵥ y' a = y a ∧ (∀ p : Fin (2 * r + k + 1), p.val ≤ r + k → y' a p = 0) ∧
      (∀ p : Fin (2 * r + k + 1), r + k < p.val → y' a p = y a p)
def IsotropicNormalFormFull : Prop :=
  ∀ (k m : ℕ) (z' : Fin (2 * (m + 1) + k + 1) → ℂ) (i : Fin (m + 1)) (y : Fin (m + 1) → Fin (2 * (m + 1) + k + 1) → ℂ)
    (t : ℂ), inWb k (m + 1) z' → herm (Hpk k (m + 1)) z' z' ≠ 0 → t ≠ 0 →
    (∀ a, a ≠ i → y a (esI k (m + 1) i) = 0) →
    (∀ p : Fin (2 * (m + 1) + k + 1), m + 1 + k < p.val → y i p = 0) →
    (Matrix.of fun a b : Fin m => y (i.succAbove a) (esI k (m + 1) (i.succAbove b))).det ≠ 0 →
    (∀ a, a ≠ i → herm (Hpk k (m + 1)) z' (y a) = 0) → herm (Hpk k (m + 1)) z' (y i) = t →
    (∀ a a', herm (Hpk k (m + 1)) (y a) (y a') = 0) →
    ∃ n0 ∈ N0set k (m + 1) z', ∃ y' : Fin (m + 1) → Fin (2 * (m + 1) + k + 1) → ℂ, ∀ a,
      n0 *ᵥ y' a = y a ∧
      (a ≠ i → (∀ p : Fin (2 * (m + 1) + k + 1), p.val ≤ m + 1 + k → y' a p = 0) ∧
        (∀ p : Fin (2 * (m + 1) + k + 1), m + 1 + k < p.val → y' a p = y a p)) ∧
      (a = i → inWb k (m + 1) (y' a) ∧ herm (Hpk k (m + 1)) z' (y' a) = t)
end Formalism.FourierDecayAlt.C3


