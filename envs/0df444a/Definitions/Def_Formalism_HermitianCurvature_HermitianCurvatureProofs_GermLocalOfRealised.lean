-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocalOfRealised
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocalOfRealised
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T07:42:14.178797+00:00
-- url     : https://prove2.me/theorems/5c993f5f-5858-57f7-9a7d-0855ce038372
-- title:
--   Germ Local Of Realised
-- statement:
--   Definitions and structural lemmas for Germ Local Of Realised, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfRealised.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocTail
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.GermRealisation
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
section loc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
def gK (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (b s : ℕ) (a : List C.Letter) (p q : C.LPt × ℂ) : ℂ :=
  KB.gN S v ε (b + s - 2) a (p.1 ++ [(s - 1, p.2⁻¹)]) (q.1 ++ [(s - 1, q.2⁻¹)])
def gDens (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (b s : ℕ) (a : List C.Letter) (h h' : C.LPt) (z : ℂ) : ℂ :=
  KB.gN S v ε (b + s - 1) a (h ++ [(s, z)]) (h' ++ [(s, z)])
structure GermReal (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (b s : ℕ) (a : List C.Letter) (Y : Finset C.LPt) where
  H : Type
  [nag : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]
  ut : C.LPt → ℂ → ℂ → H
  bt : C.LPt → ℂ → H
  β : ℂ
  ε' : ℂ
  hβ : β ≠ 0
  hε' : ‖ε'‖ = 1
  hdl : KB.dlB S b s ≠ 0
  hpsi : ∀ σ z : ℂ, G.psi β (σ * z) = KB.psiL S σ z
  memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (ut h x) 2 volume
  gram : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
    gK S v ε b s a (h, x) (h', x') = gramL volume (Uc s ut) (Uc s ut) (h, x) (h', x')
  meas : ∀ h ∈ Y, StronglyMeasurable (bt h)
  loc : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖bz s (bt h) z‖ ^ 2) K
  germ : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
    ∀ᵐ D, D ∈ K → ‖ut h x D - mainD s β ε' (bt h) x D‖ ≤ C * ‖x‖⁻¹
  dens : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ z : ℂ, z ≠ 0 →
    gDens S v ε b s a h h' z = (KB.dlB S b s : ℂ) * ⟪bz s (bt h) z, bz s (bt h') z⟫_ℂ
attribute [instance] GermReal.nag GermReal.ips GermReal.cs
def GermRealised (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s ≤ S.G.r + 2 → ∀ a, D.AdmAt S v a → ∀ Y : Finset C.LPt,
    (∀ h ∈ Y, D.ptSize h = b - 1) → Nonempty (GermReal S v ε b s a Y)
def GermCont (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s ≤ S.G.r + 2 → ∀ a, D.AdmAt S v a → ∀ h h' : C.LPt,
    D.ptSize h = b - 1 → D.ptSize h' = b - 1 → ContinuousOn (gDens S v ε b s a h h') {0}ᶜ
end loc
def GermLocOfRealised : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (v : Fin S.f),
    GermRealised S v → GermCont S v → KB.GermLoc S v
end
end Formalism.FourierDecayAlt.P.GermRealisation


