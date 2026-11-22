-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_SegRing
-- name    : Formalism_SharpRestriction_GrowthBounds_SegRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:33.94184+00:00
-- url     : https://prove2.me/theorems/bf84c837-4037-4b9f-9b7a-b1106457892a
-- title:
--   Seg Ring
-- statement:
--   Definitions and structural lemmas for Seg Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/SegRing.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace Formalism.MainNotions.G
def posOf (n' : ℕ) [NeZero n'] (x : ℤ) : Fin n' :=
  ⟨(x % (n' : ℤ)).toNat % n', Nat.mod_lt _ (NeZero.pos n')⟩
structure Frames (n' r : ℕ) where
  TT : Finset (Fin n')
  J : ℕ
  fr : ℤ → ℕ → ℤ
namespace Frames
variable {n' r : ℕ} [NeZero n'] (F : Frames n' r)
open Classical in

def letters (j : ℤ) : Finset ℤ :=
  (Finset.Icc (F.fr (j - 1) 0) (F.fr j (r - 1))).filter fun x => posOf n' x ∈ F.TT
def IsW (j x : ℤ) : Prop := x ≤ F.fr (j - 1) (r - 1)
open Classical in

def LLset (j : ℤ) : Finset ℤ :=
  (Finset.Ioo (F.fr (j - 1) (r - 1)) (F.fr j 0)).filter fun x => posOf n' x ∈ F.TT
def dist (j x : ℤ) : ℕ := (F.fr j (r - 1) - x).toNat
def GapGt (L : ℕ) (j x : ℤ) : Prop :=
  ∀ y ∈ F.letters j, y < x → (∀ z ∈ F.letters j, z < x → z ≤ y) → (L : ℤ) < x - y
open Classical in

def oldest (j x : ℤ) : ℤ :=
  let l := ((F.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·)
  l.getD (l.length - r) 0
open Classical in

def Valid (L₁ N₁ : ℕ) : Prop :=
  1 ≤ F.J ∧
  (∀ j : ℤ, ∀ i, F.fr (j + F.J) i = F.fr j i + n') ∧
  (∀ j : ℤ, ∀ i, i + 1 < r → F.fr j i < F.fr j (i + 1)) ∧
  (∀ j : ℤ, F.fr j (r - 1) < F.fr (j + 1) 0) ∧
  (∀ j : ℤ, ∀ i, i < r → posOf n' (F.fr j i) ∈ F.TT ∧ Even (F.fr j i)) ∧
  (∀ j : ℤ, ∀ i, ∀ x : ℤ, i + 1 < r → F.fr j i < x → x < F.fr j (i + 1) → posOf n' x ∉ F.TT) ∧
  (∀ j : ℤ, r ≤ (F.LLset j).card ∧
    (∀ x ∈ F.LLset j, (((F.LLset j).filter (· ≤ x)).card ≤ r ∨
        (F.LLset j).card < ((F.LLset j).filter (· ≤ x)).card + r) → Even x ∧ F.GapGt L₁ j x) ∧
    F.GapGt L₁ j (F.fr j 0)) ∧
  (∀ j : ℤ, (F.letters j).card ≤ N₁) ∧
  (∀ j : ℤ, ∀ x ∈ F.letters j, ¬ F.IsW j x → (L₁ : ℤ) < x - F.oldest j x)
end Frames
def LZ : Letters ℤ := ⟨fun x => decide (Even x)⟩
abbrev SegRing (O : Type*) [CommRing O] (r K : ℕ) := MvPolynomial (ℤ × Fin (r + K)) O
abbrev RRing (O : Type*) [CommRing O] (n' k : ℕ) := MvPolynomial (Fin n' × Fin k) O
def plEmb (O : Type*) [CommRing O] (r K : ℕ) : MvPolynomial (ℤ × Fin r) O →ₐ[O] SegRing O r K :=
  rename fun v => (v.1, Fin.castAdd K v.2)
def nmEmb (O : Type*) [CommRing O] (r K : ℕ) : MvPolynomial (ℤ × Fin K) O →ₐ[O] SegRing O r K :=
  rename fun v => (v.1, Fin.natAdd r v.2)
def geR (v : WithTop ℤ) (t : ℝ) : Prop := ∀ z : ℤ, v = (z : WithTop ℤ) → t ≤ (z : ℝ)
def ordDeg {r K : ℕ} (m : ℤ × Fin (r + K) →₀ ℕ) (x : ℤ) : ℕ :=
  if Even x then ∑ c : Fin K, m (x, Fin.natAdd r c) else ∑ c : Fin r, m (x, Fin.castAdd K c)
def XX' (O : Type*) [CommRing O] (r K : ℕ) [NeZero r] [NeZero K] {n' : ℕ} [NeZero n'] (F : Frames n' r)
    (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ) : Submodule O (SegRing O r K) :=
  Submodule.span O {P | ∃ (A : MvPolynomial (ℤ × Fin r) O) (G : MvPolynomial (ℤ × Fin K) O) (M : ℤ → ℤ),
      A ∈ supported O {v : ℤ × Fin r | v.1 ∈ F.letters j} ∧
      G ∈ supported O {v : ℤ × Fin K | v.1 ∈ F.letters j ∧ ¬ F.IsW j v.1} ∧
      (∀ x ∈ F.letters j, ¬ F.IsW j x →
        (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
        (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
        geR (valS LZ {y | y < x} A) (th x)) ∧
      P = plEmb O r K A * nmEmb O r K G} ⊓
  restrictSupport O {mm | ∀ x ∈ F.letters j, ¬ F.IsW j x → (ordDeg mm x : ℝ) ≤ o x}
def phSeg (O : Type*) [CommRing O] (K p : ℕ) {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ) :
    SegRing O r K →ₐ[O] RRing O n' (r + K) :=
  aeval fun v => X (posOf n' v.1, v.2) ^ (p ^ F.dist j v.1)
def IsLabel {n' r K : ℕ} [NeZero n'] (p : ℕ) (F : Frames n' r) (m : Fin n' × Fin (r + K) →₀ ℕ) : Prop :=
  ∀ j : ℤ, ∀ x ∈ F.letters j, ¬ F.IsW j x → ∀ c, m (posOf n' x, c) < p ^ F.dist j x
def RRdeg (O : Type*) [CommRing O] (n' k : ℕ) (d : Fin n' → ℕ) : Submodule O (RRing O n' k) :=
  restrictSupport O {m | ∀ t, ∑ c : Fin k, m (t, c) = d t}
def Gen (O : Type*) [CommRing O] (p K : ℕ) {n' r : ℕ} [NeZero n'] (F : Frames n' r)
    (XXs : ℤ → Submodule O (SegRing O r K)) (d : Fin n' → ℕ) : Set (RRing O n' (r + K)) :=
  {P | ∃ x : ℤ → SegRing O r K, (∀ j, x j ∈ XXs j) ∧ ∃ l : Fin n' × Fin (r + K) →₀ ℕ, IsLabel p F l ∧
      P = (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (x j)) * monomial l 1 ∧ P ∈ RRdeg O n' (r + K) d}
def vsDeg {n' r K : ℕ} (m : Fin n' × Fin (r + K) →₀ ℕ) : ℕ :=
  ∑ t : Fin n', if Even t.val then ∑ c : Fin K, m (t, Fin.natAdd r c) else ∑ c : Fin r, m (t, Fin.castAdd K c)
def nPl (FF : Type*) [Field FF] (k r : ℕ) : ℕ :=
  Nat.card {V : Submodule FF (Fin k → FF) // Module.finrank FF V = r}
end Formalism.MainNotions.G


