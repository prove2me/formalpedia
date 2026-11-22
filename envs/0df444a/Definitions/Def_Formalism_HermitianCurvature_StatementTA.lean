-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementTA
-- name    : Formalism_HermitianCurvature_StatementTA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:16:01.258267+00:00
-- url     : https://prove2.me/theorems/bd7a0bec-39fd-426c-a902-287bc142c25b
-- title:
--   Statement TA
-- statement:
--   Definitions and structural lemmas for Statement TA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementTA.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.TA
open Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
abbrev Pt (E : Type) := List (ℕ × E)
def lvl {E : Type} (p : Pt E) : ℕ := (p.map Prod.fst).sum
def IsPt {E : Type} [Zero E] (i : ℕ) (p : Pt E) : Prop :=
  lvl p = i ∧ ∀ b ∈ p, 1 ≤ b.1 ∧ b.2 ≠ 0
def ext {E : Type} (h : Pt E) (s : ℕ) (t : E) : Pt E := h ++ [(s, t)]
def PT {E : Type} [DecidableEq E] (Sg : ℕ → ℕ → Finset E) : ℕ → Finset (Pt E)
  | 0 => {[]}
  | n + 1 => (range (n + 1)).attach.biUnion fun m =>
      (PT Sg m.1).biUnion fun h => (Sg (n + 1) (n + 1 - m.1)).image fun t => ext h (n + 1 - m.1) t
termination_by n => n
decreasing_by all_goals (have := mem_range.mp m.2; omega)
def NZSg {E : Type} [Zero E] (Sg : ℕ → ℕ → Finset E) : Prop := ∀ i s, ∀ t ∈ Sg i s, t ≠ 0
def PSDOn {α : Type} (P : Finset α) (k : α → α → ℂ) : Prop :=
  (∀ x ∈ P, ∀ y ∈ P, k y x = conj (k x y)) ∧
  ∀ a : α → ℂ, 0 ≤ (∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y).re
section forms
variable {E : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
noncomputable def gram (k : Pt E → Pt E → ℂ) (V : Pt E → H) (P : Finset (Pt E)) : ℂ :=
  ∑ p ∈ P, ∑ p' ∈ P, k p p' * ⟪V p, V p'⟫_ℂ
noncomputable def Nst (V : Pt E → H) (Hd : Finset (Pt E)) (kap : Pt E → Pt E → ℂ) (s : ℕ) (t t' : E) : ℂ :=
  ∑ h ∈ Hd, ∑ h' ∈ Hd, kap h h' * ⟪V (ext h s t), V (ext h' s t')⟫_ℂ
def offK (k : Pt E → Pt E → ℂ) (s : ℕ) (t t' : E) : Pt E → Pt E → ℂ :=
  fun h h' => k (ext h s t) (ext h' s t')
end forms
def IsProb {W : Type} [Fintype W] (len : W → ℕ) (B : ℕ) (th : W → ℝ) : Prop :=
  (∀ w, 0 ≤ th w) ∧ ∑ w, th w = 1 ∧ ∀ w, th w ≠ 0 → len w ≤ B
def IsProb2 {W : Type} [Fintype W] (len : W → ℕ) (B : ℕ) (th : W × W → ℝ) : Prop :=
  (∀ x, 0 ≤ th x) ∧ ∑ x, th x = 1 ∧ ∀ x, th x ≠ 0 → len x.1 ≤ B ∧ len x.2 ≤ B
noncomputable def wsup {W : Type} (len : W → ℕ) (B : ℕ) (g : W → ℝ) : ℝ :=
  ⨆ w : {w // len w ≤ B}, g w.1
def LatSum {E : Type} [AddCommGroup E] (L : AddSubgroup E) (c : E → ℝ) (ep : ℝ) : Prop :=
  (∀ x, 0 ≤ c x) ∧ ∀ S : Finset E, (∀ x ∈ S, x ∈ L ∧ x ≠ 0) → ∑ x ∈ S, c x ≤ ep
structure Data (E : Type) [Field E] where
  r : ℕ
  K : ℕ → Pt E → Pt E → ℂ
  Th : ℕ → ℕ → E → Pt E → Pt E → ℂ
  e : ℕ → ℝ
  La : ℕ → ℕ → AddSubgroup E
  Lf : ℕ → ℕ → AddSubgroup E
  Lv : ℕ → AddSubgroup E
section axioms
variable {E : Type} [Field E] [DecidableEq E]
def AxK (D : Data E) : Prop :=
  D.K 0 [] [] = 1 ∧ ∀ i ≤ D.r + 1, ∀ P : Finset (Pt E), (∀ p ∈ P, IsPt i p) → PSDOn P (D.K i)
def KernelSupport (D : Data E) : Prop :=
  ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ (h h' : Pt E) (t t' : E),
    IsPt (i - s) h → IsPt (i - s) h' → t ≠ 0 → t' ≠ 0 →
    (1 / t - 1 / t' ∉ D.Lf i s ∨ (i = D.r + 1 ∧ s = 1 ∧ t ≠ t')) →
    D.K i (ext h s t) (ext h' s t') = 0
def ThetaDomination (D : Data E) : Prop :=
  ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 →
    (∀ (t : E) (Hd : Finset (Pt E)), (∀ h ∈ Hd, IsPt (i - s) h) → PSDOn Hd (D.Th i s t)) ∧
    (∀ t l : E, l ∈ D.La i s → D.Th i s (t + l) = D.Th i s t) ∧
    (∀ (t : E) (Hd : Finset (Pt E)), t ≠ 0 → (∀ h ∈ Hd, IsPt (i - s) h) →
      PSDOn Hd (fun h h' => D.Th i s t h h' - D.K i (ext h s t) (ext h' s t))) ∧
    (∀ (R : Finset E) (Hd : Finset (Pt E)), (∀ x ∈ R, ∀ y ∈ R, x - y ∈ D.La i s → x = y) →
      (∀ h ∈ Hd, IsPt (i - s) h) →
      PSDOn Hd (fun h h' => ((1 + D.e i : ℝ) : ℂ) * D.K (i - s) h h' - ∑ t ∈ R, D.Th i s t h h'))
def AxE (D : Data E) : Prop := ∀ i, 1 ≤ i → i ≤ D.r + 1 → 0 ≤ D.e i ∧ D.e i ≤ 1
end axioms
section estimates
variable {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {W : Type} [Fintype W]
def Poisson (D : Data E) (Φ : W → Pt E → H)
    (tr : W → Finset (Pt E) → (Pt E → Pt E → ℂ) → E → ℂ) (i : ℕ) : Prop :=
  ∀ (w : W) (Hd : Finset (Pt E)) (kap : Pt E → Pt E → ℂ), (∀ h ∈ Hd, IsPt (i - 1) h) →
    PSDOn Hd kap → ∀ (t0 : E) (T : Finset E), (∀ t ∈ T, t ≠ 0 ∧ t - t0 ∈ D.La i 1) →
    ∀ B : ℝ, (∀ L : Finset E, (∀ l ∈ L, l ∈ D.Lv i ∧ l ≠ 0) → ∑ l ∈ L, ‖tr w Hd kap l‖ ≤ B) →
      ∑ t ∈ T, (Nst (Φ w) Hd kap 1 t t).re ≤ ‖tr w Hd kap 0‖ + B
def WaveEstimate (D : Data E) (len : W → ℕ) (Kl Nw : ℕ) (Φ : W → Pt E → H)
    (tr : W → Finset (Pt E) → (Pt E → Pt E → ℂ) → E → ℂ) {Pat1 : Type} (pat1 : E → Pat1)
    (c1 : E → ℝ) (i : ℕ) : Prop :=
  ∀ w : W, len w + Kl ≤ Nw → ∃ th : Pat1 → W → ℝ, (∀ π, IsProb len (len w + Kl) (th π)) ∧
    ∀ (Hd : Finset (Pt E)) (kap : Pt E → Pt E → ℂ), (∀ h ∈ Hd, IsPt (i - 1) h) → PSDOn Hd kap →
      tr w Hd kap 0 = gram kap (Φ w) Hd ∧
      ∀ l ∈ D.Lv i, l ≠ 0 →
        ‖tr w Hd kap l‖ ≤ c1 l * ∑ w', th (pat1 l) w' * (gram kap (Φ w') Hd).re
def LiftEstimate (len : W → ℕ) (Kl Nw : ℕ) (Φ : W → Pt E → H) {Pat3 : Type}
    (pat3 : E → E → Pat3) (c3 : E → ℝ) (i s : ℕ) : Prop :=
  ∀ w : W, len w + Kl ≤ Nw → ∃ th : Pat3 → W × W → ℝ, (∀ π, IsProb2 len (len w + Kl) (th π)) ∧
    ∀ (Hd : Finset (Pt E)) (kp : Pt E → Pt E → ℂ) (T : Finset E),
      (∀ h ∈ Hd, IsPt (i - s) h) → (∀ t ∈ T, t ≠ 0) →
      PSDOn ((Hd ×ˢ T).image fun x => ext x.1 s x.2) kp →
      ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
        ‖Nst (Φ w) Hd (offK kp s t t') s t t'‖ ≤
          c3 (1 / t - 1 / t') * ∑ x, th (pat3 t t') x *
            (((Nst (Φ x.1) Hd (offK kp s t t) s t t).re +
              (Nst (Φ x.2) Hd (offK kp s t' t') s t' t').re) / 2)
def BlockEstimate (D : Data E) (len : W → ℕ) (Kl Nw : ℕ) (Φ : W → Pt E → H) (bd4 : ℝ) (i s : ℕ) : Prop :=
  ∀ w : W, len w + (s + 1) * Kl ≤ Nw → ∃ th : W → ℝ, IsProb len (len w + (s + 1) * Kl) th ∧
    ∀ (Hd : Finset (Pt E)) (kap : Pt E → Pt E → ℂ), (∀ h ∈ Hd, IsPt (i - s) h) → PSDOn Hd kap →
      ∀ (t0 : E) (T : Finset E), (∀ t ∈ T, t ≠ 0 ∧ t - t0 ∈ D.La i s) →
        ∑ t ∈ T, (Nst (Φ w) Hd kap s t t).re ≤ bd4 * ∑ w', th w' * (gram kap (Φ w') Hd).re
end estimates
section levels
variable {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {W : Type} [Fintype W]
noncomputable def Slev (D : Data E) (Sg : ℕ → ℕ → Finset E) (Φ : W → Pt E → H) (w : W) (i : ℕ) : ℝ :=
  (gram (D.K i) (Φ w) (PT Sg i)).re
noncomputable def Ssplit (D : Data E) (Sg : ℕ → ℕ → Finset E) (Φ : W → Pt E → H) (w : W)
    (i s : ℕ) : ℝ :=
  (∑ t ∈ Sg i s, ∑ t' ∈ Sg i s, Nst (Φ w) (PT Sg (i - s)) (offK (D.K i) s t t') s t t').re
noncomputable def Diag (D : Data E) (Sg : ℕ → ℕ → Finset E) (Φ : W → Pt E → H) (w : W)
    (i s : ℕ) : ℝ :=
  ∑ t ∈ Sg i s, (Nst (Φ w) (PT Sg (i - s)) (offK (D.K i) s t t) s t t).re
open Classical in

noncomputable def Cosets (D : Data E) (Sg : ℕ → ℕ → Finset E) (Φ : W → Pt E → H) (w : W)
    (i s : ℕ) (R : Finset E) : ℝ :=
  ∑ t0 ∈ R, ∑ t ∈ (Sg i s).filter (fun t => t - t0 ∈ D.La i s),
    (Nst (Φ w) (PT Sg (i - s)) (D.Th i s t0) s t t).re
noncomputable def lsup (D : Data E) (len : W → ℕ) (Kl : ℕ) (Sg : ℕ → ℕ → Finset E)
    (Φ : W → Pt E → H) (i : ℕ) : ℝ :=
  wsup len (4 * Kl * (D.r + 1 - i)) fun w => Slev D Sg Φ w i
end levels
def SplitLast : Prop :=
  ∀ (E : Type) [Field E] [DecidableEq E] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (W : Type) (D : Data E) (Sg : ℕ → ℕ → Finset E) (Φ : W → Pt E → H) (w : W) (i : ℕ),
    NZSg Sg → 1 ≤ i → PSDOn (PT Sg i) (D.K i) →
      √(Slev D Sg Φ w i) ≤ ∑ s ∈ Icc 1 i, √(Ssplit D Sg Φ w i s)
def OffDiagSchur : Prop :=
  ∀ (E : Type) [Field E] [DecidableEq E] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (W : Type) [Fintype W] (len : W → ℕ) (Kl Nw : ℕ) (D : Data E) (Sg : ℕ → ℕ → Finset E)
    (Φ : W → Pt E → H) (Pat3 : Type) [Fintype Pat3] (pat3 : E → E → Pat3) (c3 : E → ℝ)
    (ep3 : ℝ) (i s : ℕ) (w : W),
    NZSg Sg → 1 ≤ s → s ≤ i → i ≤ D.r + 1 → AxK D → KernelSupport D →
    LiftEstimate len Kl Nw Φ pat3 c3 i s → LatSum (D.Lf i s) c3 ep3 → len w + Kl ≤ Nw →
      Ssplit D Sg Φ w i s ≤
        Diag D Sg Φ w i s + Fintype.card Pat3 * ep3 * wsup len (len w + Kl) (fun w' => Diag D Sg Φ w' i s)
def DiagTop : Prop :=
  ∀ (E : Type) [Field E] [DecidableEq E] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (W : Type) (D : Data E) (Sg : ℕ → ℕ → Finset E) (Φ : W → Pt E → H) (w : W),
    NZSg Sg → KernelSupport D → Ssplit D Sg Φ w (D.r + 1) 1 = Diag D Sg Φ w (D.r + 1) 1
def DiagCosets : Prop :=
  ∀ (E : Type) [Field E] [DecidableEq E] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (W : Type) (D : Data E) (Sg : ℕ → ℕ → Finset E) (Φ : W → Pt E → H) (w : W) (i s : ℕ)
    (R : Finset E),
    NZSg Sg → 1 ≤ s → s ≤ i → i ≤ D.r + 1 → ThetaDomination D →
    (∀ t ∈ Sg i s, ∃ t0 ∈ R, t - t0 ∈ D.La i s) → (∀ x ∈ R, ∀ y ∈ R, x - y ∈ D.La i s → x = y) →
      Diag D Sg Φ w i s ≤ Cosets D Sg Φ w i s R
def CosetsOne : Prop :=
  ∀ (E : Type) [Field E] [DecidableEq E] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (W : Type) [Fintype W] (len : W → ℕ) (Kl Nw : ℕ) (D : Data E) (Sg : ℕ → ℕ → Finset E)
    (Φ : W → Pt E → H) (tr : W → Finset (Pt E) → (Pt E → Pt E → ℂ) → E → ℂ) (Pat1 : Type)
    (pat1 : E → Pat1) (c1 : E → ℝ) (ep1 : ℝ) (i : ℕ) (w : W) (R : Finset E),
    NZSg Sg → 1 ≤ i → i ≤ D.r + 1 → AxK D → ThetaDomination D → AxE D →
    Poisson D Φ tr i → WaveEstimate D len Kl Nw Φ tr pat1 c1 i → LatSum (D.Lv i) c1 ep1 → len w + Kl ≤ Nw →
    (∀ x ∈ R, ∀ y ∈ R, x - y ∈ D.La i 1 → x = y) →
      Cosets D Sg Φ w i 1 R ≤
        (1 + D.e i) * (Slev D Sg Φ w (i - 1) +
          ep1 * wsup len (len w + Kl) (fun w' => Slev D Sg Φ w' (i - 1)))
def CosetsS : Prop :=
  ∀ (E : Type) [Field E] [DecidableEq E] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (W : Type) [Fintype W] (len : W → ℕ) (Kl Nw : ℕ) (D : Data E) (Sg : ℕ → ℕ → Finset E)
    (Φ : W → Pt E → H) (bd4 : ℝ) (i s : ℕ) (w : W) (R : Finset E),
    NZSg Sg → 2 ≤ s → s ≤ i → i ≤ D.r + 1 → AxK D → ThetaDomination D → AxE D → 0 ≤ bd4 →
    BlockEstimate D len Kl Nw Φ bd4 i s → len w + (s + 1) * Kl ≤ Nw →
    (∀ x ∈ R, ∀ y ∈ R, x - y ∈ D.La i s → x = y) →
      Cosets D Sg Φ w i s R ≤
        (1 + D.e i) * bd4 * wsup len (len w + (s + 1) * Kl) (fun w' => Slev D Sg Φ w' (i - s))
def LevelEst {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {W : Type} [Fintype W] (len : W → ℕ) (Kl : ℕ) (D : Data E)
    (Φ : W → Pt E → H) (tr : W → Finset (Pt E) → (Pt E → Pt E → ℂ) → E → ℂ) {Pat1 Pat3 : Type}
    (pat1 : E → Pat1) (pat3 : ℕ → E → E → Pat3) (c1 : E → ℝ) (c3 : ℕ → E → ℝ) (bd4 : ℕ → ℝ)
    (i : ℕ) : Prop :=
  Poisson D Φ tr i ∧ WaveEstimate D len Kl (4 * Kl * (D.r + 1)) Φ tr pat1 c1 i ∧
  (∀ s ∈ Icc 1 i, ¬ (i = D.r + 1 ∧ s = 1) →
    LiftEstimate len Kl (4 * Kl * (D.r + 1)) Φ (pat3 s) (c3 s) i s) ∧
  (∀ s ∈ Icc 2 i, BlockEstimate D len Kl (4 * Kl * (D.r + 1)) Φ (bd4 s) i s)
def LevelSizes {E : Type} [Field E] (D : Data E) (Pat3 : Type) [Fintype Pat3] (c1 : E → ℝ)
    (c3 : ℕ → E → ℝ) (ep1 : ℝ) (ep3 bd4 : ℕ → ℝ) (ep a : ℝ) (i : ℕ) : Prop :=
  LatSum (D.Lv i) c1 ep1 ∧
  (∀ s ∈ Icc 1 i, ¬ (i = D.r + 1 ∧ s = 1) → LatSum (D.Lf i s) (c3 s) (ep3 s)) ∧
  0 ≤ ep3 1 ∧
  (1 + Fintype.card Pat3 * ep3 1) * (1 + ep1) ≤ (1 + ep) ^ 2 ∧
  (∀ s ∈ Icc 2 i, 0 ≤ bd4 s ∧ (1 + Fintype.card Pat3 * ep3 s) * (1 + D.e i) * bd4 s ≤ a ^ (2 * (s - 1)))
def OneLevel : Prop :=
  ∀ (E : Type) [Field E] [DecidableEq E] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (W : Type) [Fintype W] (len : W → ℕ) (Kl : ℕ) (D : Data E) (Sg : ℕ → ℕ → Finset E)
    (Φ : W → Pt E → H) (tr : W → Finset (Pt E) → (Pt E → Pt E → ℂ) → E → ℂ) (Pat1 Pat3 : Type)
    [Fintype Pat3] (pat1 : E → Pat1) (pat3 : ℕ → E → E → Pat3) (c1 : E → ℝ) (c3 : ℕ → E → ℝ)
    (ep1 : ℝ) (ep3 bd4 : ℕ → ℝ) (ep a : ℝ) (i : ℕ),
    NZSg Sg → 1 ≤ i → i ≤ D.r + 1 → 0 ≤ ep → 0 ≤ a →
    AxK D → KernelSupport D → ThetaDomination D → AxE D →
    LevelEst len Kl D Φ tr pat1 pat3 c1 c3 bd4 i →
    LevelSizes D Pat3 c1 c3 ep1 ep3 bd4 ep a i →
      √(lsup D len Kl Sg Φ i) ≤ (1 + ep) * √(1 + D.e i) * √(lsup D len Kl Sg Φ (i - 1)) +
        ∑ s ∈ Icc 2 i, a ^ (s - 1) * √(lsup D len Kl Sg Φ (i - s))
def EpsLimit : Prop :=
  ∀ (E : Type) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Type) [Fintype W]
    (len : W → ℕ) (k : Pt E → Pt E → ℂ) (P : Finset (Pt E)) (Φ : ℝ → W → Pt E → H)
    (V : Pt E → H) (w0 : W) (B0 : ℕ) (Bc jn : ℝ),
    len w0 ≤ B0 →
    (∀ eps : ℝ, 0 < eps → (gram k (Φ eps w0) P).re ≤ Bc * wsup len B0 (fun w => ‖Φ eps w []‖ ^ 2)) →
    (∀ w, len w ≤ B0 → Tendsto (fun eps => ‖Φ eps w []‖ ^ 2) (𝓝[>] 0) (𝓝 jn)) →
    (∀ p ∈ P, ∀ᶠ eps in 𝓝[>] (0 : ℝ), Φ eps w0 p = V p) →
      (gram k V P).re ≤ Bc * jn
def TopDominationLimit : Prop :=
  ∀ (E : Type) [Field E] [DecidableEq E] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (n : ℕ) (Kn : Pt E → Pt E → ℂ) (V : Pt E → H) (ρ : Type)
    (c : ρ → Pt E → ℂ) (B : ℝ),
    (∀ Sg : ℕ → ℕ → Finset E, NZSg Sg → (gram Kn V (PT Sg n)).re ≤ B) →
    (∀ (P : Finset (Pt E)) (R : Finset ρ), (∀ p ∈ P, IsPt n p) →
      PSDOn P (fun p p' => Kn p p' - ∑ x ∈ R, conj (c x p) * c x p')) →
    (∀ x, Summable (fun p : {p : Pt E // IsPt n p} => ‖c x p.1‖ * ‖V p.1‖)) →
      ∀ R : Finset ρ, ∑ x ∈ R, ‖∑' p : {p : Pt E // IsPt n p}, c x p.1 • V p.1‖ ^ 2 ≤ B
def TheoremAReduction : Prop :=
  ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C' C : ℝ,
    ∀ (E : Type) [Field E] [DecidableEq E] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (W : Type) [Fintype W] (len : W → ℕ) (Kl f : ℕ) (Θ : ℝ) (D : Data E)
      (Pat1 Pat3 : Type) [Fintype Pat3] (pat1 : ℕ → E → Pat1) (pat3 : ℕ → ℕ → E → E → Pat3)
      (c1 : ℕ → E → ℝ) (c3 : ℕ → ℕ → E → ℝ) (ep1 : ℕ → ℝ) (ep3 bd4 : ℕ → ℕ → ℝ)
      (Φ : ℝ → W → Pt E → H) (tr : ℝ → ℕ → W → Finset (Pt E) → (Pt E → Pt E → ℂ) → E → ℂ)
      (w0 : W) (V : Pt E → H) (jn : ℝ) (ρ : Type) (c : ρ → Pt E → ℂ),
      4 ≤ Kl → 1 ≤ f → C' ≤ Θ → (D.r : ℝ) * (C₀ / Θ) ^ f ≤ 1 →
      AxK D → KernelSupport D → ThetaDomination D → AxE D →
      (∀ i ∈ Icc 1 (D.r + 1), LevelSizes D Pat3 (c1 i) (c3 i) (ep1 i) (ep3 i) (bd4 i)
        ((C₀ * Θ ^ (-((Kl : ℝ) - 5 / 2))) ^ f) ((C₀ / Θ) ^ f) i) →
      (∀ eps : ℝ, 0 < eps → ∀ i ∈ Icc 1 (D.r + 1),
        LevelEst len Kl D (Φ eps) (tr eps i) (pat1 i) (pat3 i) (c1 i) (c3 i) (bd4 i) i) →
      (∀ w, len w ≤ 4 * Kl * (D.r + 1) → Tendsto (fun eps => ‖Φ eps w []‖ ^ 2) (𝓝[>] 0) (𝓝 jn)) →
      len w0 = 0 →
      (∀ p, IsPt (D.r + 1) p → ∀ᶠ eps in 𝓝[>] (0 : ℝ), Φ eps w0 p = V p) →
      (∀ (P : Finset (Pt E)) (R : Finset ρ), (∀ p ∈ P, IsPt (D.r + 1) p) →
        PSDOn P (fun p p' => D.K (D.r + 1) p p' - ∑ x ∈ R, conj (c x p) * c x p')) →
      (∀ x, Summable (fun p : {p : Pt E // IsPt (D.r + 1) p} => ‖c x p.1‖ * ‖V p.1‖)) →
        ∀ R : Finset ρ, ∑ x ∈ R, ‖∑' p : {p : Pt E // IsPt (D.r + 1) p}, c x p.1 • V p.1‖ ^ 2 ≤
          (1 + C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * jn
def OneLevelOfSteps : Prop :=
  SplitLast → OffDiagSchur → DiagTop → DiagCosets → CosetsOne → CosetsS → OneLevel
def ReductionOfSteps : Prop :=
  OneLevel → EpsLimit → TopDominationLimit → Formalism.FourierDecayAlt.K.JointTheoremA → TheoremAReduction
end Formalism.FourierDecayAlt.TA


