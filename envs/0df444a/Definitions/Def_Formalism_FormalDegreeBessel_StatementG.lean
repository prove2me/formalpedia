-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_StatementG
-- name    : Formalism_FormalDegreeBessel_StatementG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:45:53.503797+00:00
-- url     : https://prove2.me/theorems/46e54ded-69c4-4048-b3a8-2ad0b1121138
-- title:
--   Statement G
-- statement:
--   Definitions and structural lemmas for Statement G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/StatementG.lean

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
noncomputable section
namespace Formalism.QuantumDeterminants
def herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)
def UH {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {g | gᴴ * H * g = H}
def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩
def wI (k r : ℕ) (j : Fin (k + 1)) : Fin (2 * r + k + 1) := ⟨r + j.val, by omega⟩
def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩
def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if i.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1)
  else 0
def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1
def inWb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → v i = 0
def Tz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ := -(herm (Hpk k r) z z).re
def Nset (k r : ℕ) : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (eI k r a) = if i = eI k r a then 1 else 0) ∧
    (∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      g i j = if i = j then 1 else 0)}
def UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ z = z}
def Sset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {s | ∃ h ∈ UWset k r z, ∃ m ∈ Nset k r, s = h * m}
def ell (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  ∑ a : Fin r, if h : a.val + 1 < r then g (eI k r a) (eI k r ⟨a.val + 1, h⟩)
    else (g *ᵥ z) (eI k r a)
def psi (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  Complex.exp (Complex.I * ((c * ell k r z g).re : ℂ))
def cStd : ℂ := -2 * Complex.I
def fvec (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if h : a.val < r then bvec (eI k r ⟨a.val, h⟩) else z
def Zhat (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun a b => herm (Hpk k r) (g *ᵥ fvec k r z' b) (fvec k r z a)
def Dmin (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (l : Fin (r + 2)) : ℂ :=
  ((Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
    (Fin.castLE (Nat.le_of_lt_succ l.isLt))).det
def cmin (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) : ℂ :=
  Dmin k r z z' g ⟨a.val + 1, by omega⟩ / Dmin k r z z' g ⟨a.val, by omega⟩
def zeta (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  Dmin k r z z' g (Fin.last (r + 1)) / Dmin k r z z' g ⟨r, by omega⟩
def GGf (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℝ :=
  Complex.normSq (zeta k r z z' g) - Tz k r z * Tz k r z'
def Gf (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℝ :=
  Complex.normSq (Dmin k r z z' g (Fin.last (r + 1))) -
    Tz k r z * Tz k r z' * Complex.normSq (Dmin k r z z' g ⟨r, by omega⟩)
def gramVec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Fin (r + 1) ⊕ Fin (r + 1) → Fin (2 * r + k + 1) → ℂ
  | Sum.inl a => fvec k r z a
  | Sum.inr b => g *ᵥ fvec k r z' b
def gramM (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  fun i j => herm (Hpk k r) (gramVec k r z z' g j) (gramVec k r z z' g i)
def UHGroup : Prop :=
  ∀ (m : ℕ) (H : Matrix (Fin m) (Fin m) ℂ), IsUnit H.det →
    (1 : Matrix (Fin m) (Fin m) ℂ) ∈ UH H ∧
    (∀ g ∈ UH H, ∀ h ∈ UH H, g * h ∈ UH H) ∧
    (∀ g ∈ UH H, IsUnit g.det ∧ g⁻¹ ∈ UH H)
def UHConj : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (H P : Matrix (Fin m) (Fin m) ℂ), IsUnit P.det →
    Pᴴ * Formalism.REAL.Jm ε * P = H →
    ∀ g : Matrix (Fin m) (Fin m) ℂ, g ∈ UH H ↔ Formalism.REAL.inUJ ε (P * g * P⁻¹)
def HpkFacts : Prop :=
  ∀ k r : ℕ,
    (Hpk k r)ᴴ = Hpk k r ∧ Hpk k r * Hpk k r = 1 ∧
    (∀ a b : Fin r, herm (Hpk k r) (bvec (eI k r a)) (bvec (esI k r b)) = if a = b then 1 else 0) ∧
    ∃ ε : Fin (2 * r + k + 1) → Bool, (Finset.univ.filter fun i => ε i = true).card = k + r ∧
      ∃ P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, IsUnit P.det ∧
        Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r
def NSubgroup : Prop :=
  ∀ k r : ℕ, (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Nset k r ∧
    (∀ g ∈ Nset k r, ∀ h ∈ Nset k r, g * h ∈ Nset k r) ∧
    (∀ g ∈ Nset k r, g⁻¹ ∈ Nset k r)
def EllAdd : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z →
    ∀ g ∈ Nset k r, ∀ h ∈ Nset k r, ell k r z (g * h) = ell k r z g + ell k r z h
def PsiChar : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ), inWb k r z →
    ∀ g ∈ Nset k r, (∀ h ∈ Nset k r, psi k r z c (g * h) = psi k r z c g * psi k r z c h) ∧
      ‖psi k r z c g‖ = 1
def UWNormal : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z →
    ∀ h ∈ UWset k r z, ∀ g ∈ Nset k r,
      h * g * h⁻¹ ∈ Nset k r ∧ ell k r z (h * g * h⁻¹) = ell k r z g
def SGroup : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z →
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Sset k r z ∧
    (∀ s ∈ Sset k r z, ∀ t ∈ Sset k r z, s * t ∈ Sset k r z) ∧
    (∀ s ∈ Sset k r z, s⁻¹ ∈ Sset k r z)
def DInv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' →
    ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      (l : Fin (r + 2)), Dmin k r z z' (s * g * s') l = Dmin k r z z' g l
def GInv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' →
    ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Gf k r z z' (s * g * s') = Gf k r z z' g
def GFactor : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    Dmin k r z z' g ⟨r, by omega⟩ ≠ 0 →
      Gf k r z z' g = Complex.normSq (Dmin k r z z' g ⟨r, by omega⟩) * GGf k r z z' g
def RevCS : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' →
    (herm (Hpk k r) z z).re < 0 → (herm (Hpk k r) z' z').re < 0 →
      Tz k r z * Tz k r z' ≤ Complex.normSq (herm (Hpk k r) z' z)
def GGram : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' →
    ∀ g ∈ UH (Hpk k r),
      ((Gf k r z z' g : ℝ) : ℂ) = (-1) ^ (r + 1) * (gramM k r z z' g).det
def GNonneg : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' →
    0 < Tz k r z → 0 < Tz k r z' → ∀ g ∈ UH (Hpk k r), 0 ≤ Gf k r z z' g
end Formalism.QuantumDeterminants


