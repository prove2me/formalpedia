-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_StandardBasisDerivatives_ArchimedeanBasisDerivatives_StBasDeriv
-- name    : Development_WeilBound_RepresentationTheoryGL_StandardBasisDerivatives_ArchimedeanBasisDerivatives_StBasDeriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:01.396815+00:00
-- url     : https://prove2.me/theorems/1a68d60e-015b-4441-967e-689225cfc617
-- title:
--   St Bas Deriv
-- statement:
--   Definitions and structural lemmas for St Bas Deriv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/StandardBasisDerivatives/ArchimedeanBasisDerivatives/StBasDeriv.lean

import Mathlib
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
open scoped ContDiff
namespace PositivityTheory.Rg.Pc1
variable {n : ℕ}
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Poly (n : ℕ) := MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ
def ev (g : Mat n) : Poly n →+* ℂ :=
  MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2)))
abbrev Mode (ε : Fin n → Bool) := {x : Fin n × Fin n // ε x.1 = true ∧ ε x.2 = false}
def nMode (ε : Fin n → Bool) : ℕ := Fintype.card (Mode ε)
def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1
def barM (ε : Fin n → Bool) (Z : Mat n) : Mat n := fun a b => -(sg ε a * sg ε b * Z b a)
def LieU (ε : Fin n → Bool) (Z : Mat n) : Prop := ∀ a b, star (Z a b) = barM ε Z a b
def dZ (ε : Fin n → Bool) (Z : Mat n) : Derivation ℂ (Poly n) (Poly n) :=
  MvPolynomial.mkDerivation ℂ (Sum.elim
    (fun x => ∑ c, (X (Sum.inl (x.1, c)) * C (Z c x.2) - C (Z x.1 c) * X (Sum.inl (c, x.2))))
    (fun x => ∑ c, (X (Sum.inr (x.1, c)) * C (barM ε Z c x.2) - C (barM ε Z x.1 c) * X (Sum.inr (c, x.2)))))
def dM (ε : Fin n → Bool) (x : Mode ε) : Derivation ℂ (Poly n) (Poly n) := dZ ε (Matrix.single x.1.2 x.1.1 1)
def rP (ε : Fin n → Bool) : Poly n := ∑ x : Mode ε, X (Sum.inl x.1) * X (Sum.inr x.1)
def rM (ε : Fin n → Bool) (g : Mat n) : ℝ := ∑ x : Mode ε, ‖g x.1.1 x.1.2‖ ^ 2
def OmP (ε : Fin n → Bool) : Matrix (Mode ε) (Mode ε) (Poly n) := fun x y => dM ε x (X (Sum.inr y.1))
def detbP (n : ℕ) : Poly n := (Matrix.of fun a b : Fin n => (X (Sum.inr (a, b)) : Poly n)).det
def blockAlg (ε : Fin n → Bool) : Subalgebra ℂ (Poly n) :=
  Algebra.adjoin ℂ {P | ∃ a b, ε a = ε b ∧ P = X (Sum.inl (a, b))}
def topP (ε : Fin n → Bool) (M : ℕ) (P : Poly n) : Poly n := detbP n ^ M * P * (OmP ε).det
def prev (q : ℕ → Poly n) : ℕ → Poly n
  | 0 => 0
  | k + 1 => q k
def IsKoszul (ε : Fin n → Bool) (p : ℕ → Poly n) (q : Mode ε → ℕ → Poly n) : Prop :=
  (∀ k : ℕ, ((k : Poly n) + 1) * p (k + 1) + rP ε * p k = ∑ x, (dM ε x (q x k) + dM ε x (rP ε) * prev (q x) k)) ∧
    (∀ k, nMode ε < k → p k = 0) ∧ ∀ x k, nMode ε ≤ k → q x k = 0
def IsCutFn (H : ℝ → ℝ) : Prop := ContDiff ℝ ∞ H ∧ ∃ R : ℝ, ∀ x, R ≤ x → H x = 0
def IsProfile (N : ℕ) (G : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ G ∧ (∀ x, 1 ≤ x → G x = 0) ∧ (∀ x, 0 ≤ (-1) ^ N * iteratedDeriv N G x) ∧ iteratedDeriv N G 0 ≠ 0
def bas (ε : Fin n → Bool) (H : ℝ → ℝ) (P : Poly n) (g : Mat n) : ℂ := (H (rM ε g) : ℂ) * ev g P
def adBas (ε : Fin n → Bool) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n) (g : Mat n) : ℂ :=
  bas ε (deriv H) (dZ ε Z (rP ε) * P) g + bas ε H (dZ ε Z P) g
def ShapeM (ε : Fin n → Bool) (d : ℕ) : Submodule ℂ (Mat n → ℂ) :=
  Submodule.span ℂ {φ | ∃ H P, IsCutFn H ∧ P.totalDegree ≤ d ∧ φ = bas ε H P}
def AdSpanM (ε : Fin n → Bool) : Submodule ℂ (Mat n → ℂ) :=
  Submodule.span ℂ {φ | ∃ Z H P, LieU ε Z ∧ IsCutFn H ∧ φ = adBas ε Z H P}
def famF (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → Poly n) (t : ℝ) (g : Mat n) : ℂ :=
  ∑ k ∈ Finset.range (nMode ε + 1), bas ε (iteratedDeriv k fun x => G (t * x)) (p k) g
def dMode (ε : Fin n → Bool) (θ : Fin n → ℝ) : ℝ :=
  ∏ x : Mode ε, ‖Complex.exp (θ x.1.1 * Complex.I) - Complex.exp (θ x.1.2 * Complex.I)‖ ^ 2
def StAlg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (M : ℕ) (P : Poly n), P ∈ blockAlg ε →
    ∃ p q, IsKoszul ε p q ∧ p (nMode ε) = topP ε M P
def StProfile : Prop := ∀ N : ℕ, ∃ G, IsProfile N G
def StFam : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → Poly n), IsProfile (nMode ε) G →
    ∃ d, (∀ k ≤ nMode ε, (p k).totalDegree ≤ d) ∧
      ∀ t : ℝ, 0 < t → famF ε G p t ∈ ShapeM ε d ∧ ∀ g, 1 < t * rM ε g → famF ε G p t g = 0
def StHomot : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → Poly n) (q : Mode ε → ℕ → Poly n),
    IsProfile (nMode ε) G → IsKoszul ε p q → ∀ t : ℝ, 1 ≤ t → famF ε G p 1 - famF ε G p t ∈ AdSpanM ε
def StBasDeriv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n), LieU ε Z → IsCutFn H →
    adBas ε Z H P ∈ ShapeM ε (P.totalDegree + 2) ∧ ∀ (g : Mat n) (s : ℝ),
      HasDerivAt (fun u : ℝ => bas ε H P (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)))
        (adBas ε Z H P (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) s
end PositivityTheory.Rg.Pc1


