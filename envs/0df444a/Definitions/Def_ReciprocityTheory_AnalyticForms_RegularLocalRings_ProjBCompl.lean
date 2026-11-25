-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjBCompl
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjBCompl
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T13:41:31.804178+00:00
-- url     : https://prove2.me/theorems/21a0581c-d4f0-5e7f-aaf3-77bb7b1382cd
-- title:
--   Proj BCompl
-- statement:
--   Definitions and structural lemmas for Proj BCompl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjBCompl.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
def projBCompl (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    (projX P hP).Opens :=
  ⟨(projB P D hP : Set (projX P hP))ᶜ, (projB P D hP).isClosed.isOpen_compl⟩
variable (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) in

structure WData where

  W : Scheme.{0}
  π : W ⟶ projX P hP
  lft : LocallyOfFiniteType (π ≫ toSpecC hP)

  J : (projX P hP).IdealSheafData
  blowup : FinalTheorems.Blowup π J
  support_le : (J.support : Set (projX P hP)) ⊆ projB P D hP
  regular : ∀ w : W, IsRegularLocalRing (W.presheaf.stalk w)
  snc : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal
    ⟨π.base ⁻¹' (projB P D hP : Set (projX P hP)),
      IsClosed.preimage π.base.hom.continuous (projB P D hP).2⟩)
  isIso_off : IsIso (π ∣_ projBCompl P D hP)

  m : ((k : K) → ι k) → ℕ

  g : ∀ p, Fin (m p) → Γ(projX P hP, (chartOpen hP p).1)
  span_g : ∀ p, Ideal.span (Set.range (g p)) = J.ideal (chartOpen hP p)

  pres : ∀ p, Fin (m p) → AffPres (π ≫ toSpecC hP)
  le_pres : ∀ p i, (pres p i).V ≤ π ⁻¹ᵁ (chartOpen hP p).1
  iSup_pres : ∀ p, (⨆ i, (pres p i).V) = π ⁻¹ᵁ (chartOpen hP p).1

  t : ∀ p i, Fin (m p) → Γ(W, (pres p i).V)
  t_self : ∀ p i, t p i i = 1
  g_eq : ∀ p i k, π.appLE _ (pres p i).V (le_pres p i) (g p k) =
    t p i k * π.appLE _ (pres p i).V (le_pres p i) (g p i)
  inter : ∀ p i j, (pres p i).V ⊓ (pres p j).V = W.basicOpen (t p i j)
  t_cocycle : ∀ p i j k,
    W.presheaf.map (homOfLE (inf_le_right : (pres p i).V ⊓ (pres p j).V ≤ _)).op (t p j k) *
      W.presheaf.map (homOfLE (inf_le_left : (pres p i).V ⊓ (pres p j).V ≤ _)).op (t p i j) =
    W.presheaf.map (homOfLE (inf_le_left : (pres p i).V ⊓ (pres p j).V ≤ _)).op (t p i k)

  yq : ∀ p i, (Σ k, ι k) → Fin (pres p i).n

  yt : ∀ p i, Fin (m p) → Fin (pres p i).n
  sec_yq : ∀ p i q, (pres p i).secHom (X (yq p i q)) =
    π.appLE _ (pres p i).V (le_pres p i) (chartCoord hP p q)
  sec_yt : ∀ p i k, (pres p i).secHom (X (yt p i k)) = t p i k

  gen : ∀ p i (l : Fin (pres p i).n), ∃ F : MvPolynomial (Fin (pres p i).n) ℂ,
    F.vars ⊆ Finset.univ.image (yq p i) ∪ Finset.univ.image (yt p i) ∧ X l - F ∈ (pres p i).K
end
end ReciprocityTheory.AnForm.R


