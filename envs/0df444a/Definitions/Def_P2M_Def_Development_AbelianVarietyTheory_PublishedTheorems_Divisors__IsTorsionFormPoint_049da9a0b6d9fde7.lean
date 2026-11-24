-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsTorsionFormPoint_049da9a0b6d9fde7
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsTorsionFormPoint_049da9a0b6d9fde7
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:56.850384+00:00
-- url     : https://prove2.me/theorems/b4102032-6467-4f6e-9f9a-e6ce0a299506
-- title:
--   Is Torsion Form Point
-- statement:
--   Definitions and structural lemmas for Is Torsion Form Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsTorsionFormPoint.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SiegelReframe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
namespace GlobalTheory.TorsionForm
abbrev Ext (m : ℕ) : Type := Finset (Fin m) → ℂ
def sgn {m : ℕ} (i : Fin m) (S : Finset (Fin m)) : ℂ := (-1) ^ (S.filter (· < i)).card
def wedge {m : ℕ} (i : Fin m) (w : Ext m) : Ext m :=
  fun S => if i ∈ S then sgn i S * w (S.erase i) else 0
def contr {m : ℕ} (i : Fin m) (w : Ext m) : Ext m :=
  fun S => if i ∈ S then 0 else sgn i S * w (insert i S)
def dt {n : ℕ} (g : ℕ) (i : Fin n) : Fin (n + n + g) := (i.castAdd n).castAdd g
def dtb {n : ℕ} (g : ℕ) (i : Fin n) : Fin (n + n + g) := (i.natAdd n).castAdd g
def dzb (n : ℕ) {g : ℕ} (a : Fin g) : Fin (n + n + g) := a.natAdd (n + n)
def join {m g : ℕ} (S : Finset (Fin m)) (I : Finset (Fin g)) : Finset (Fin (m + g)) :=
  S.map (Fin.castAddEmb g) ∪ I.map (Fin.natAddEmb m)
def strN {m g : ℕ} (K : Ext (m + g) →L[ℂ] Ext (m + g)) : Ext m := fun S =>
  ∑ I : Finset (Fin g), (-1) ^ I.card * (I.card : ℂ) * K (Pi.single (join ∅ I) 1) (join S I)
def phi {m : ℕ} (w : Ext m) : Ext m := fun S => ((2 * π * Complex.I)⁻¹ : ℂ) ^ (S.card / 2) * w S
def IsMellinDeriv (F : ℝ → ℂ) (T : ℂ) : Prop :=
  ∃ C₁ C₀ : ℂ, IntegrableOn (fun u : ℝ => (F u - C₁ / u - C₀) / u) (Ioc 0 1) ∧
    IntegrableOn (fun u : ℝ => F u / u) (Ioi 1) ∧
    T = -(∫ u in Ioc (0 : ℝ) 1, (F u - C₁ / u - C₀) / u) - (∫ u in Ioi (1 : ℝ), F u / u) + C₁ -
      Real.eulerMascheroniConstant * C₀
section Deriv
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [SMul ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [SMul ℂ W]
def d10 (f : V → W) (P v : V) : W :=
  (1 / 2 : ℂ) • (fderiv ℝ f P v - Complex.I • fderiv ℝ f P (Complex.I • v))
def d01 (f : V → W) (P v : V) : W :=
  (1 / 2 : ℂ) • (fderiv ℝ f P v + Complex.I • fderiv ℝ f P (Complex.I • v))
end Deriv
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
  (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
  (h : Pt E g → ℝ) (β : Fin n → E)
def hor (P : Pt E g) (v : E) : Pt E g := (v, fderiv ℂ (fun b => per (τ b) (flat τ P)) P.1 v)
def vert (E : Type) [Zero E] (a : Fin g) : Pt E g := (0, Pi.single a 1)
def imPart (b : E) : Matrix (Fin g) (Fin g) ℂ := (τ b).map fun t => (t.im : ℂ)
def pointDifference (s : Pt E g → Ext (n + n + g)) (P v : Pt E g) : Ext (n + n + g) :=
  d10 s P v + d10 (fun Q => (Real.log (h Q) : ℂ)) P v • s P
def connForm (b v : E) (w : Ext (n + n + g)) : Ext (n + n + g) :=
  ∑ a, ∑ c, ((Matrix.of fun a e => d01 (fun b' => imPart τ b' a e) b v) * (imPart τ b)⁻¹) a c •
    wedge (dzb n c) (contr (dzb n a) w)
def nablaE (s : Pt E g → Ext (n + n + g)) (P : Pt E g) : Ext (n + n + g) :=
  ∑ i, (wedge (dt g i) (pointDifference h s P (hor τ P (β i))) +
    wedge (dtb g i) (d01 s P (hor τ P (β i)) + connForm τ P.1 (β i) (s P)))
def dbarV (s : Pt E g → Ext (n + n + g)) (P : Pt E g) : Ext (n + n + g) :=
  ∑ a, wedge (dzb n a) (d01 s P (vert E a))
def dbarAdj (s : Pt E g → Ext (n + n + g)) (P : Pt E g) : Ext (n + n + g) :=
  -∑ a, ∑ c, (2 * imPart τ P.1 a c) • contr (dzb n c) (pointDifference h s P (vert E a))
def superconn (u : ℝ) (s : Pt E g → Ext (n + n + g)) (P : Pt E g) : Ext (n + n + g) :=
  nablaE τ h β s P + (Real.sqrt u : ℂ) • (dbarV s P + dbarAdj τ h s P)
def curv (b : E) (u : ℝ) (f : (Fin g → ℂ) → Ext (n + n + g)) (z : Fin g → ℂ) : Ext (n + n + g) :=
  superconn τ h β u (superconn τ h β u fun P => f P.2) (b, z)
def IsSec {m : ℕ} (b : E) (f : (Fin g → ℂ) → Ext m) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ l ∈ M, ∀ z, f (z + per (τ b) l) = j l (b, z) • f z
def IsHeatKernel (b : E) (u : ℝ) (D : Set (Fl g))
    (K : ℝ → (Fin g → ℂ) → (Fin g → ℂ) → Ext (n + n + g) →L[ℂ] Ext (n + n + g)) : Prop :=
  ContDiffOn ℝ ∞ (fun a : ℝ × (Fin g → ℂ) × (Fin g → ℂ) => K a.1 a.2.1 a.2.2) (Ioi 0 ×ˢ univ) ∧
  (∀ t > 0, ∀ l ∈ M, ∀ z z', K t (z + per (τ b) l) z' = j l (b, z) • K t z z' ∧
    j l (b, z') • K t z (z' + per (τ b) l) = K t z z') ∧
  (∀ t > 0, ∀ z z' w, HasDerivAt (fun t' => K t' z z' w)
    (-curv τ h β b u (fun y => K t y z' w) z) t) ∧
  ∀ f, IsSec τ M j b f → TendstoLocallyUniformly
    (fun t z => ∫ x in D, K t z (per (τ b) x) (f (per (τ b) x))) f (𝓝[>] 0)
def IsHeatTrace (b : E) (F : ℝ → Ext (n + n)) : Prop :=
  ∃ D : Set (Fl g), IsAddFundamentalDomain M D volume ∧ ∀ u > 0, ∃ K,
    IsHeatKernel τ M j h β b u D K ∧
      F u = phi (∫ x in D, strN (K 1 (per (τ b) x) (per (τ b) x)))
def IsAcyclicAt (b : E) : Prop :=
  ∀ f : (Fin g → ℂ) → Ext (0 + 0 + g), IsSec τ M j b f →
    (∀ z, dbarV (fun P : Pt E g => f P.2) (b, z) + dbarAdj τ h (fun P => f P.2) (b, z) = 0) →
    ∀ z, ∀ I ≠ ∅, f z I = 0
def IsTorsionForm (b : E) (T : Ext (n + n)) : Prop :=
  ∃ F, IsHeatTrace τ M j h β b F ∧ ∀ S, IsMellinDeriv (fun u => F u S) (T S)
example : wedge (0 : Fin 2) (wedge 1 (Pi.single ∅ 1)) Finset.univ = 1 ∧
    wedge (1 : Fin 2) (wedge 0 (Pi.single ∅ 1)) Finset.univ = -1 := by
  have e₁ : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have e₂ : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  have e₃ : ((Finset.univ : Finset (Fin 2)).filter (· = 0)).card = 1 := by decide
  have e₄ : (({1} : Finset (Fin 2)).filter (· = 0)).card = 0 := by decide
  simp [wedge, sgn, e₁, e₂, e₃, e₄]
end GlobalTheory.TorsionForm


