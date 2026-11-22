-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
-- name    : Formalism_RealPlaceAnalysis_SmoothOnG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:47:45.351012+00:00
-- url     : https://prove2.me/theorems/534be425-7712-4761-9283-f5ae3aae7bde
-- title:
--   Smooth On G
-- statement:
--   Definitions and structural lemmas for Smooth On G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/SmoothOnG.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
namespace Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def cpart1 {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε)
def cpart2 {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I)) • (Z + Jm ε * Zᴴ * Jm ε)
def SmoothOnG {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ g₀, inUJ ε g₀ → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, inUJ ε g → f g = F g
def Rd {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0
def Ec {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => Rd (cpart1 ε Z) f g + Complex.I * Rd (cpart2 ε Z) f g
def Eab {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  Ec ε (Matrix.single a b 1) f
def CpartMem : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ),
    inG ε (cpart1 ε Z) ∧ inG ε (cpart2 ε Z) ∧ Z = cpart1 ε Z + Complex.I • cpart2 ε Z ∧
    (inG ε Z → cpart1 ε Z = Z ∧ cpart2 ε Z = 0)
def RdExt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (f F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (U : Set (Matrix (Fin n) (Fin n) ℂ)) (g X : Matrix (Fin n) (Fin n) ℂ),
    IsOpen U → g ∈ U → inUJ ε g → ContDiffOn ℝ ∞ F U → (∀ h ∈ U, inUJ ε h → f h = F h) →
    inG ε X → Rd X f g = fderiv ℝ F g (g * X)
def RdSmooth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ),
    SmoothOnG ε f → inG ε X → SmoothOnG ε (Rd X f)
def RdLin : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ) (X Y : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) (c : ℂ) (g : Matrix (Fin n) (Fin n) ℂ),
    SmoothOnG ε f → SmoothOnG ε f' → inG ε X → inG ε Y → inUJ ε g →
    Rd (X + Y) f g = Rd X f g + Rd Y f g ∧ Rd ((r : ℂ) • X) f g = (r : ℂ) * Rd X f g ∧
    Rd X (fun h => f h + c * f' h) g = Rd X f g + c * Rd X f' g
def RdBracket : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X Y g : Matrix (Fin n) (Fin n) ℂ),
    SmoothOnG ε f → inG ε X → inG ε Y → inUJ ε g →
    Rd X (Rd Y f) g - Rd Y (Rd X f) g = Rd (X * Y - Y * X) f g
def EabGl : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (a b c d : Fin n)
    (g : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → inUJ ε g →
    Eab ε a b (Eab ε c d f) g - Eab ε c d (Eab ε a b f) g =
      (if b = c then Eab ε a d f g else 0) - (if d = a then Eab ε c b f g else 0)
def RdLeft : Prop :=
  ∀ (n : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X h g : Matrix (Fin n) (Fin n) ℂ),
    Rd X (fun x => f (h * x)) g = Rd X f (h * g)
end Formalism.REAL


