-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:48:13.447982+00:00
-- url     : https://prove2.me/theorems/0f56bfa3-4f85-4990-9448-22462520fce4
-- title:
--   Coef Left AAv
-- statement:
--   Definitions and structural lemmas for Coef Left AAv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CoefLeftAAv.lean

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def LeftAA : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (m : ℕ)
    (hm : m ≤ r) (u ell : ℂ) (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E)
    (s g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    s ∈ Sset k r z → inUH (Hpk k r) g →
      AAop k r m hm u (fun x => F (s * x)) g = AAop k r m hm u F (s * g) ∧
      AAvop k r m hm ell (fun x => F (s * x)) g = AAvop k r m hm ell F (s * g)
def RightAA : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (m : ℕ)
    (hm : m ≤ r) (u ell : ℂ) (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E)
    (s' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    SmoothOnH (Hpk k r) f → s' ∈ Sset k r z' → inUH (Hpk k r) g →
      AAop k r m hm u (fun x => f (x * s')) g = AAop k r m hm u f (g * s') ∧
      AAvop k r m hm ell (fun x => f (x * s')) g = AAvop k r m hm ell f (g * s')
def SsetUH : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    s ∈ Sset k r z → inUH (Hpk k r) s
def SsetInvCol : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    s ∈ Sset k r z → ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), (∀ b : Fin r, b.val < a.val → i ≠ eI k r b) →
      s⁻¹ i (eI k r a) = if i = eI k r a then 1 else 0
def SsetRowStar : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    s ∈ Sset k r z → ∀ (a : Fin r) (j : Fin (2 * r + k + 1)), (∀ b : Fin r, b.val < a.val → j ≠ esI k r b) →
      s (esI k r a) j = if j = esI k r a then 1 else 0
def CoefLeftAA : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r)
    (s g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : Fin m → Fin (2 * r + k + 1)),
    s ∈ Sset k r z →
      (Matrix.of fun a l : Fin m => herm (Hpk k r) ((s * g) *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))).det =
      (Matrix.of fun a l : Fin m => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))).det
def CoefLeftAAv : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r)
    (s g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (B : Fin m → Fin (2 * r + k + 1)),
    s ∈ Sset k r z → inUH (Hpk k r) g →
      (Matrix.of fun a l : Fin m => ((s * g)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (B l)).det =
      (Matrix.of fun a l : Fin m => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (B l)).det
def HInvol {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Prop := Hᴴ = H ∧ H * H = 1
def HpkInvol : Prop := ∀ k r : ℕ, HInvol (Hpk k r)
def RdExtH : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f F : Matrix (Fin n) (Fin n) ℂ → E) (U : Set (Matrix (Fin n) (Fin n) ℂ)) (g X : Matrix (Fin n) (Fin n) ℂ),
    HInvol H → IsOpen U → g ∈ U → inUH H g → ContDiffOn ℝ ∞ F U → (∀ h ∈ U, inUH H h → f h = F h) →
    Xᴴ * H + H * X = 0 → RdV X f g = fderiv ℝ F g (g * X)
def SmoothLin : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f f' : Matrix (Fin n) (Fin n) ℂ → E) (c : ℂ),
    SmoothOnH H f → SmoothOnH H f' → SmoothOnH H (fun x => f x + c • f' x)
def SmoothLocal : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f f' : Matrix (Fin n) (Fin n) ℂ → E),
    (∀ x, inUH H x → f x = f' x) → SmoothOnH H f → SmoothOnH H f'
def SmoothRight : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E) (s : Matrix (Fin n) (Fin n) ℂ),
    HInvol H → inUH H s → SmoothOnH H f → SmoothOnH H (fun x => f (x * s))
def EabHSmooth : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin n),
    HInvol H → SmoothOnH H f → SmoothOnH H (EabH H a b f)
def EabHLin : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f f' : Matrix (Fin n) (Fin n) ℂ → E) (c : ℂ) (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ),
    HInvol H → SmoothOnH H f → SmoothOnH H f' → inUH H g →
      EabH H a b (fun x => f x + c • f' x) g = EabH H a b f g + c • EabH H a b f' g
def EabHLocal : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f f' : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ),
    HInvol H → (∀ x, inUH H x → f x = f' x) → inUH H g → EabH H a b f g = EabH H a b f' g
def EabHGl : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E) (a b c d : Fin n) (g : Matrix (Fin n) (Fin n) ℂ),
    HInvol H → SmoothOnH H f → inUH H g →
      EabH H a b (EabH H c d f) g - EabH H c d (EabH H a b f) g =
        (if b = c then EabH H a d f g else 0) - (if d = a then EabH H c b f g else 0)
def EabHRight : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin n) (s g : Matrix (Fin n) (Fin n) ℂ),
    HInvol H → SmoothOnH H f → inUH H s → inUH H g →
      EabH H a b (fun x => f (x * s)) g = ∑ c, ∑ d, (s⁻¹ c a * s b d) • EabH H c d f (g * s)
def QExpand : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin t → Fin n) (u : ℂ), Q * P = 1 →
      qminor (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) a b u =
        ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n,
          ((∏ j, P (c j) (a j)) * ∏ j, Q (b j) (d j)) • qminor E c d u
open scoped Classical in

def AlgAA : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r m : ℕ) (hm : m ≤ r)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (xi : Fin m → Fin (2 * r + k + 1) → ℂ) (u : ℂ),
    GlRel E → Q * P = 1 →
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), (∀ b : Fin r, b.val < a.val → i ≠ eI k r b) →
      P i (eI k r a) = if i = eI k r a then 1 else 0) →
    (∑ D : Fin m → Fin (2 * r + k + 1),
      if StrictMono D then (Matrix.of fun a l : Fin m => xi a (D l)).det •
        qminor (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) (xR k r m hm) D u else 0) =
    ∑ C : Fin m → Fin (2 * r + k + 1),
      if StrictMono C then (Matrix.of fun a l : Fin m => ∑ d, Q d (C l) * xi a d).det •
        qminor E (xR k r m hm) C u else 0
open scoped Classical in

def AlgAAv : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r m : ℕ) (hm : m ≤ r)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (eta : Fin m → Fin (2 * r + k + 1) → ℂ) (v : ℂ),
    GlRel E → Q * P = 1 →
    (∀ (a : Fin r) (j : Fin (2 * r + k + 1)), (∀ b : Fin r, b.val < a.val → j ≠ esI k r b) →
      Q (esI k r a) j = if j = esI k r a then 1 else 0) →
    (∑ B : Fin m → Fin (2 * r + k + 1),
      if StrictMono (fun l => keyS k r (B l)) then (Matrix.of fun a l : Fin m => eta a (B l)).det •
        qminor (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) B (sR k r m hm) v else 0) =
    ∑ C : Fin m → Fin (2 * r + k + 1),
      if StrictMono (fun l => keyS k r (C l)) then (Matrix.of fun a l : Fin m => ∑ d, P (C l) d * eta a d).det •
        qminor E C (sR k r m hm) v else 0
end AAInvW


