-- Prove2me | solution 1 for AutomorphicForm.archCasimirAtComplex_and_archCasimirBarAtComplex_foldr_archDeriv_eq_foldr_archDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/2baf5756-fa54-5b6b-a351-96d912c74f05

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Theorems.Thm_AutomorphicForm_foldr_archDeriv_comm_of_ne_place
import Theorems.Thm_AutomorphicForm_isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archCasimirAtComplex_and_archCasimirBarAtComplex_foldr_archDeriv_eq_foldr_archDeriv

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace CasC

variable {K : Type} [Field K] [NumberField K]

abbrev Dir (K : Type) [Field K] [NumberField K] : Type :=
  (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)

abbrev D1 (d : Dir K) (φ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ) (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d

abbrev Wd (l : List (Dir K)) (b : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ) (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b

abbrev R {w : InfinitePlace K} (hw : w.IsReal) (x : ArchDir) : Dir K := Sum.inl ⟨w, hw, x⟩

abbrev place (d : Dir K) : InfinitePlace K := Sum.elim (fun e => e.1) (fun e => e.1) d

theorem Wd_nil (b : AdelicGL2 (𝓞 K) K → ℂ) : Wd [] b = b := rfl

theorem Wd_cons (d : Dir K) (l : List (Dir K)) (b : AdelicGL2 (𝓞 K) K → ℂ) : Wd (d :: l) b = D1 d (Wd l b) := rfl

theorem Wd_append (l l' : List (Dir K)) (b : AdelicGL2 (𝓞 K) K → ℂ) : Wd (l ++ l') b = Wd l (Wd l' b) :=
  List.foldr_append

theorem IsArchSmoothAtComplex.add' {w : InfinitePlace K} {hw : w.IsComplex} {φ ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) : IsArchSmoothAtComplex hw (φ + ψ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archComplexLiftAt hw e) + ψ (g * archComplexLiftAt hw e)) _
  exact (hφ g).add (hψ g)

theorem IsArchSmoothAtComplex.smul' {w : InfinitePlace K} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (c : ℂ) : IsArchSmoothAtComplex hw (c • φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => c * φ (g * archComplexLiftAt hw e)) _
  exact contDiffOn_const.mul (hφ g)

def SmoothFor (d : Dir K) (φ : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  Sum.elim (fun e => IsArchSmoothAt e.2.1 φ) (fun e => IsArchSmoothAtComplex e.2.1 φ) d

theorem SmoothFor.add {d : Dir K} {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : SmoothFor d φ) (hψ : SmoothFor d ψ) :
    SmoothFor d (φ + ψ) := by
  rcases d with ⟨w, hw, x⟩ | ⟨w, hw, x⟩
  · exact IsArchSmoothAt.add hφ hψ
  · exact IsArchSmoothAtComplex.add' hφ hψ

theorem SmoothFor.smul {d : Dir K} {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : SmoothFor d φ) (c : ℂ) :
    SmoothFor d (c • φ) := by
  rcases d with ⟨w, hw, x⟩ | ⟨w, hw, x⟩
  · exact IsArchSmoothAt.smul hφ c
  · exact IsArchSmoothAtComplex.smul' hφ c

theorem D1_add (d : Dir K) {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : SmoothFor d φ) (hψ : SmoothFor d ψ) :
    D1 d (φ + ψ) = D1 d φ + D1 d ψ := by
  rcases d with ⟨w, hw, x⟩ | ⟨w, hw, x⟩
  · exact archDerivAt_add hφ hψ x
  · exact (AutomorphicForm.isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm K w hw).2.1 φ ψ hφ hψ x

theorem D1_smul (d : Dir K) (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) : D1 d (c • φ) = c • D1 d φ := by
  rcases d with ⟨w, hw, x⟩ | ⟨w, hw, x⟩
  · exact archDerivAt_smul hw x c φ
  · exact (AutomorphicForm.isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm K w hw).2.2.1 c φ x

theorem Wd_smul (l : List (Dir K)) (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) : Wd l (c • φ) = c • Wd l φ := by
  induction l with
  | nil => rfl
  | cons d l ih => rw [Wd_cons, Wd_cons, ih, D1_smul]

theorem D1_lin2 (d : Dir K) {f₁ f₂ : AdelicGL2 (𝓞 K) K → ℂ} (h₁ : SmoothFor d f₁) (h₂ : SmoothFor d f₂) (a b : ℂ) :
    D1 d (a • f₁ + b • f₂) = a • D1 d f₁ + b • D1 d f₂ := by
  rw [D1_add d (h₁.smul a) (h₂.smul b), D1_smul, D1_smul]

theorem D1_lin3 (d : Dir K) {f₁ f₂ f₃ : AdelicGL2 (𝓞 K) K → ℂ} (h₁ : SmoothFor d f₁) (h₂ : SmoothFor d f₂)
    (h₃ : SmoothFor d f₃) (a b c : ℂ) :
    D1 d (a • f₁ + b • f₂ + c • f₃) = a • D1 d f₁ + b • D1 d f₂ + c • D1 d f₃ := by
  rw [D1_add d ((h₁.smul a).add (h₂.smul b)) (h₃.smul c), D1_add d (h₁.smul a) (h₂.smul b),
    D1_smul, D1_smul, D1_smul]

section Generic

def CasA (A : ArchDir → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ)) (ψ : AdelicGL2 (𝓞 K) K → ℂ) :
    AdelicGL2 (𝓞 K) K → ℂ :=
  -((1 / 4 : ℂ) • A .H (A .H ψ) - (1 / 2 : ℂ) • A .H ψ + A .E (A .Fm ψ))

variable (A : ArchDir → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
  {S : (AdelicGL2 (𝓞 K) K → ℂ) → Prop}

theorem casA_lin3 (ψ : AdelicGL2 (𝓞 K) K → ℂ) :
    CasA A ψ = (-(1 / 4 : ℂ)) • A .H (A .H ψ) + (1 / 2 : ℂ) • A .H ψ + (-1 : ℂ) • A .E (A .Fm ψ) := by
  funext g
  simp only [CasA, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem A_sub'
    (hAadd : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, S u → S v → ∀ x, A x (u + v) = A x u + A x v)
    (hAs : ∀ (x : ArchDir) (c : ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ), A x (c • u) = c • A x u)
    (hSs : ∀ {u : AdelicGL2 (𝓞 K) K → ℂ}, S u → ∀ c : ℂ, S (c • u))
    {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : S φ) (hψ : S ψ) (x : ArchDir) :
    A x (φ - ψ) = A x φ - A x ψ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ, hAadd hφ (hSs hψ _) x, hAs, neg_one_smul, ← sub_eq_add_neg]

theorem A_lin3
    (hAadd : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, S u → S v → ∀ x, A x (u + v) = A x u + A x v)
    (hAs : ∀ (x : ArchDir) (c : ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ), A x (c • u) = c • A x u)
    (hSs : ∀ {u : AdelicGL2 (𝓞 K) K → ℂ}, S u → ∀ c : ℂ, S (c • u))
    (hSadd : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, S u → S v → S (u + v))
    (x : ArchDir) {f₁ f₂ f₃ : AdelicGL2 (𝓞 K) K → ℂ} (h₁ : S f₁) (h₂ : S f₂) (h₃ : S f₃) (a b c : ℂ) :
    A x (a • f₁ + b • f₂ + c • f₃) = a • A x f₁ + b • A x f₂ + c • A x f₃ := by
  rw [hAadd (hSadd (hSs h₁ a) (hSs h₂ b)) (hSs h₃ c) x, hAadd (hSs h₁ a) (hSs h₂ b) x, hAs, hAs, hAs]

theorem A_cas
    (hAadd : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, S u → S v → ∀ x, A x (u + v) = A x u + A x v)
    (hAs : ∀ (x : ArchDir) (c : ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ), A x (c • u) = c • A x u)
    (hSs : ∀ {u : AdelicGL2 (𝓞 K) K → ℂ}, S u → ∀ c : ℂ, S (c • u))
    (hSadd : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, S u → S v → S (u + v))
    (x : ArchDir) {ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (h₁ : S (A .H (A .H ψ))) (h₂ : S (A .H ψ)) (h₃ : S (A .E (A .Fm ψ))) :
    A x (CasA A ψ) = (-(1 / 4 : ℂ)) • A x (A .H (A .H ψ)) + (1 / 2 : ℂ) • A x (A .H ψ) +
      (-1 : ℂ) • A x (A .E (A .Fm ψ)) := by
  rw [casA_lin3, A_lin3 A hAadd hAs hSs hSadd x h₁ h₂ h₃]

variable
  (hAadd : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, S u → S v → ∀ x, A x (u + v) = A x u + A x v)
  (hAs : ∀ (x : ArchDir) (c : ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ), A x (c • u) = c • A x u)
  (hSs : ∀ {u : AdelicGL2 (𝓞 K) K → ℂ}, S u → ∀ c : ℂ, S (c • u))
  (hSadd : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, S u → S v → S (u + v))
  (hSA : ∀ (x : ArchDir) {u : AdelicGL2 (𝓞 K) K → ℂ}, S u → S (A x u))
  (hrel : ∀ u : AdelicGL2 (𝓞 K) K → ℂ, S u →
    (A .H (A .E u) - A .E (A .H u) = (2 : ℂ) • A .E u) ∧
    (A .H (A .Fm u) - A .Fm (A .H u) = (-2 : ℂ) • A .Fm u) ∧
    (A .E (A .Fm u) - A .Fm (A .E u) = A .H u))

include hAadd hAs hSs hSadd hSA hrel

theorem gcomm_H {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : S ψ) :
    CasA A (A .H ψ) = A .H (CasA A ψ) := by
  have sF := (hSA .Fm hψ)
  have sH := (hSA .H hψ)
  have k1 : A .H (A .E (A .Fm ψ)) =
      A .E (A .H (A .Fm ψ)) + (2 : ℂ) • A .E (A .Fm ψ) :=
    sub_eq_iff_eq_add'.1 (hrel _ sF).1
  have k2 : A .H (A .Fm ψ) = A .Fm (A .H ψ) + (-2 : ℂ) • A .Fm ψ :=
    sub_eq_iff_eq_add'.1 (hrel _ hψ).2.1
  have k3 : A .E (A .H (A .Fm ψ)) =
      A .E (A .Fm (A .H ψ)) + (-2 : ℂ) • A .E (A .Fm ψ) := by
    rw [k2, hAadd ((hSA .Fm sH)) (hSs sF _), hAs]
  have hD : A .H (CasA A ψ) = (-(1 / 4 : ℂ)) • A .H (A .H (A .H ψ)) +
      (1 / 2 : ℂ) • A .H (A .H ψ) + (-1 : ℂ) • A .H (A .E (A .Fm ψ)) :=
    A_cas A hAadd hAs hSs hSadd .H ((hSA .H sH)) sH ((hSA .E sF))
  rw [hD, casA_lin3 A, k1, k3]
  funext g
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem gcomm_E {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : S ψ) :
    CasA A (A .E ψ) = A .E (CasA A ψ) := by
  have sF := (hSA .Fm hψ)
  have sH := (hSA .H hψ)
  have sE := (hSA .E hψ)
  have e1 : A .H (A .E ψ) = A .E (A .H ψ) + (2 : ℂ) • A .E ψ :=
    sub_eq_iff_eq_add'.1 (hrel _ hψ).1
  have e2 : A .H (A .H (A .E ψ)) =
      A .H (A .E (A .H ψ)) + (2 : ℂ) • A .H (A .E ψ) := by
    conv_lhs => rw [e1]
    rw [hAadd ((hSA .E sH)) (hSs sE _), hAs]
  have e3 : A .H (A .E (A .H ψ)) =
      A .E (A .H (A .H ψ)) + (2 : ℂ) • A .E (A .H ψ) :=
    sub_eq_iff_eq_add'.1 (hrel _ sH).1
  have e4 : A .Fm (A .E ψ) = A .E (A .Fm ψ) - A .H ψ := by
    rw [← (hrel _ hψ).2.2, sub_sub_cancel]
  have e5 : A .E (A .Fm (A .E ψ)) =
      A .E (A .E (A .Fm ψ)) - A .E (A .H ψ) := by
    rw [e4, A_sub' A hAadd hAs hSs ((hSA .E sF)) sH]
  have hD : A .E (CasA A ψ) = (-(1 / 4 : ℂ)) • A .E (A .H (A .H ψ)) +
      (1 / 2 : ℂ) • A .E (A .H ψ) + (-1 : ℂ) • A .E (A .E (A .Fm ψ)) :=
    A_cas A hAadd hAs hSs hSadd .E ((hSA .H sH)) sH ((hSA .E sF))
  rw [hD, casA_lin3 A, e2, e3, e1, e5]
  funext g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem gcomm_Fm {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : S ψ) :
    CasA A (A .Fm ψ) = A .Fm (CasA A ψ) := by
  have sF := (hSA .Fm hψ)
  have sH := (hSA .H hψ)
  have f1 : A .H (A .Fm ψ) = A .Fm (A .H ψ) + (-2 : ℂ) • A .Fm ψ :=
    sub_eq_iff_eq_add'.1 (hrel _ hψ).2.1
  have f2 : A .H (A .H (A .Fm ψ)) =
      A .H (A .Fm (A .H ψ)) + (-2 : ℂ) • A .H (A .Fm ψ) := by
    conv_lhs => rw [f1]
    rw [hAadd ((hSA .Fm sH)) (hSs sF _), hAs]
  have f3 : A .H (A .Fm (A .H ψ)) =
      A .Fm (A .H (A .H ψ)) + (-2 : ℂ) • A .Fm (A .H ψ) :=
    sub_eq_iff_eq_add'.1 (hrel _ sH).2.1
  have f4 : A .E (A .Fm (A .Fm ψ)) =
      A .H (A .Fm ψ) + A .Fm (A .E (A .Fm ψ)) :=
    sub_eq_iff_eq_add.1 (hrel _ sF).2.2
  have hD : A .Fm (CasA A ψ) = (-(1 / 4 : ℂ)) • A .Fm (A .H (A .H ψ)) +
      (1 / 2 : ℂ) • A .Fm (A .H ψ) + (-1 : ℂ) • A .Fm (A .E (A .Fm ψ)) :=
    A_cas A hAadd hAs hSs hSadd .Fm ((hSA .H sH)) sH ((hSA .E sF))
  rw [hD, casA_lin3 A, f2, f3, f4, f1]
  funext g
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem gcomm (x : ArchDir) {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : S ψ) :
    CasA A (A x ψ) = A x (CasA A ψ) := by
  cases x with
  | H => exact gcomm_H A hAadd hAs hSs hSadd hSA hrel hψ
  | E => exact gcomm_E A hAadd hAs hSs hSadd hSA hrel hψ
  | Fm => exact gcomm_Fm A hAadd hAs hSs hSadd hSA hrel hψ

omit hrel in

theorem gcross (B : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hBadd : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, S u → S v → B (u + v) = B u + B v)
    (hBs : ∀ (c : ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ), B (c • u) = c • B u)
    (hSB : ∀ {u : AdelicGL2 (𝓞 K) K → ℂ}, S u → S (B u))
    (hcomm : ∀ {u : AdelicGL2 (𝓞 K) K → ℂ}, S u → ∀ x, B (A x u) = A x (B u))
    {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : S ψ) :
    B (CasA A ψ) = CasA A (B ψ) := by
  have s1 : ∀ x, S (A x ψ) := fun x => hSA x hψ
  rw [casA_lin3, casA_lin3, hBadd (hSadd (hSs (hSA _ (s1 _)) _) (hSs (s1 _) _)) (hSs (hSA _ (s1 _)) _),
    hBadd (hSs (hSA _ (s1 _)) _) (hSs (s1 _) _), hBs, hBs, hBs,
    hcomm (s1 .H) .H, hcomm hψ .H, hcomm (s1 .Fm) .E, hcomm hψ .Fm]

omit hrel in

theorem casA_add {u v : AdelicGL2 (𝓞 K) K → ℂ} (hu : S u) (hv : S v) :
    CasA A (u + v) = CasA A u + CasA A v := by
  rw [casA_lin3, casA_lin3, casA_lin3, hAadd hu hv, hAadd (hSA _ hu) (hSA _ hv), hAadd hu hv, hAadd (hSA _ hu) (hSA _ hv)]
  funext g
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit hAadd hSs hSadd hSA hrel in
theorem casA_smul (c : ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ) : CasA A (c • u) = c • CasA A u := by
  rw [casA_lin3, casA_lin3, hAs, hAs, hAs, hAs]
  funext g
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Generic

def Reg3 (m : ℕ) (b : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∀ l : List (Dir K), l.length ≤ m + 2 →
    Continuous (Wd l b) ∧
    (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (Wd l b)) ∧
    (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (Wd l b))

theorem Reg3.smoothFor {m : ℕ} {b : AdelicGL2 (𝓞 K) K → ℂ} (h : Reg3 m b) (d : Dir K) (l : List (Dir K))
    (hl : l.length ≤ m + 2) : SmoothFor d (Wd l b) := by
  rcases d with ⟨w, hw, x⟩ | ⟨w, hw, x⟩
  · exact (h l hl).2.1 w hw
  · exact (h l hl).2.2 w hw

theorem Reg3.swap {m : ℕ} {b : AdelicGL2 (𝓞 K) K → ℂ} (h : Reg3 m b) (l : List (Dir K))
    (hl : l.length + 2 ≤ m + 2) (d d' : Dir K) (hne : place d ≠ place d') :
    D1 d (D1 d' (Wd l b)) = D1 d' (D1 d (Wd l b)) := by
  have hyp : ∀ l' : List (Dir K), l'.length ≤ 2 →
      Continuous (Wd l' (Wd l b)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (Wd l' (Wd l b))) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (Wd l' (Wd l b))) := by
    intro l' hl'
    rw [← Wd_append]
    exact h (l' ++ l) (by rw [List.length_append]; omega)
  exact AutomorphicForm.foldr_archDeriv_comm_of_ne_place K (Wd l b) hyp d d' hne

section Cplx

variable {w : InfinitePlace K} (hw : w.IsComplex)

theorem Dc_sub {u v : AdelicGL2 (𝓞 K) K → ℂ} (hu : IsArchSmoothAtComplex hw u) (hv : IsArchSmoothAtComplex hw v)
    (X : ArchDirComplex) :
    archDerivAtComplex hw X (u - v) = archDerivAtComplex hw X u - archDerivAtComplex hw X v := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ v, archDerivAtComplex_add hu (hv.smul _), AutomorphicForm.archDerivAtComplex_smul,
    neg_one_smul, ← sub_eq_add_neg]

theorem del_eq_lin2 (e : ArchDir) (v : AdelicGL2 (𝓞 K) K → ℂ) :
    archDelAt hw e v = (1 / 2 : ℂ) • archDerivAtComplex hw e.toComplex v +
      (-(Complex.I / 2)) • archDerivAtComplex hw e.toComplexI v := by
  funext g
  simp only [archDelAt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem delbar_eq_lin2 (e : ArchDir) (v : AdelicGL2 (𝓞 K) K → ℂ) :
    archDelBarAt hw e v = (1 / 2 : ℂ) • archDerivAtComplex hw e.toComplex v +
      (Complex.I / 2) • archDerivAtComplex hw e.toComplexI v := by
  funext g
  simp only [archDelBarAt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem del_add {u v : AdelicGL2 (𝓞 K) K → ℂ} (hu : IsArchSmoothAtComplex hw u) (hv : IsArchSmoothAtComplex hw v)
    (x : ArchDir) : archDelAt hw x (u + v) = archDelAt hw x u + archDelAt hw x v := by
  simp only [del_eq_lin2, archDerivAtComplex_add hu hv]
  funext g
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem del_smul (x : ArchDir) (c : ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ) : archDelAt hw x (c • u) = c • archDelAt hw x u := by
  simp only [del_eq_lin2, AutomorphicForm.archDerivAtComplex_smul]
  funext g
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem delbar_add {u v : AdelicGL2 (𝓞 K) K → ℂ} (hu : IsArchSmoothAtComplex hw u) (hv : IsArchSmoothAtComplex hw v)
    (x : ArchDir) : archDelBarAt hw x (u + v) = archDelBarAt hw x u + archDelBarAt hw x v := by
  simp only [delbar_eq_lin2, archDerivAtComplex_add hu hv]
  funext g
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem delbar_smul (x : ArchDir) (c : ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ) :
    archDelBarAt hw x (c • u) = c • archDelBarAt hw x u := by
  simp only [delbar_eq_lin2, AutomorphicForm.archDerivAtComplex_smul]
  funext g
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem D_del {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : IsArchSmoothAtComplex hw u) (X : ArchDirComplex) (e : ArchDir) :
    archDerivAtComplex hw X (archDelAt hw e u) = (1 / 2 : ℂ) • archDerivAtComplex hw X (archDerivAtComplex hw e.toComplex u) +
      (-(Complex.I / 2)) • archDerivAtComplex hw X (archDerivAtComplex hw e.toComplexI u) := by
  rw [del_eq_lin2, archDerivAtComplex_add ((hu.archDerivAtComplex _).smul _) ((hu.archDerivAtComplex _).smul _),
    AutomorphicForm.archDerivAtComplex_smul, AutomorphicForm.archDerivAtComplex_smul]

theorem D_delbar {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : IsArchSmoothAtComplex hw u) (X : ArchDirComplex) (e : ArchDir) :
    archDerivAtComplex hw X (archDelBarAt hw e u) = (1 / 2 : ℂ) • archDerivAtComplex hw X (archDerivAtComplex hw e.toComplex u) +
      (Complex.I / 2) • archDerivAtComplex hw X (archDerivAtComplex hw e.toComplexI u) := by
  rw [delbar_eq_lin2, archDerivAtComplex_add ((hu.archDerivAtComplex _).smul _) ((hu.archDerivAtComplex _).smul _),
    AutomorphicForm.archDerivAtComplex_smul, AutomorphicForm.archDerivAtComplex_smul]

theorem reorder {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : IsArchSmoothAtComplex hw u) :
    (∀ g, archDerivAtComplex hw .E (archDerivAtComplex hw .H u) g =
      archDerivAtComplex hw .H (archDerivAtComplex hw .E u) g - 2 * archDerivAtComplex hw .E u g) ∧
    (∀ g, archDerivAtComplex hw .Fm (archDerivAtComplex hw .H u) g =
      archDerivAtComplex hw .H (archDerivAtComplex hw .Fm u) g + 2 * archDerivAtComplex hw .Fm u g) ∧
    (∀ g, archDerivAtComplex hw .Fm (archDerivAtComplex hw .E u) g =
      archDerivAtComplex hw .E (archDerivAtComplex hw .Fm u) g - archDerivAtComplex hw .H u g) ∧
    (∀ g, archDerivAtComplex hw .iH (archDerivAtComplex hw .H u) g =
      archDerivAtComplex hw .H (archDerivAtComplex hw .iH u) g) ∧
    (∀ g, archDerivAtComplex hw .iE (archDerivAtComplex hw .H u) g =
      archDerivAtComplex hw .H (archDerivAtComplex hw .iE u) g - 2 * archDerivAtComplex hw .iE u g) ∧
    (∀ g, archDerivAtComplex hw .iFm (archDerivAtComplex hw .H u) g =
      archDerivAtComplex hw .H (archDerivAtComplex hw .iFm u) g + 2 * archDerivAtComplex hw .iFm u g) ∧
    (∀ g, archDerivAtComplex hw .iH (archDerivAtComplex hw .E u) g =
      archDerivAtComplex hw .E (archDerivAtComplex hw .iH u) g + 2 * archDerivAtComplex hw .iE u g) ∧
    (∀ g, archDerivAtComplex hw .iE (archDerivAtComplex hw .E u) g =
      archDerivAtComplex hw .E (archDerivAtComplex hw .iE u) g) ∧
    (∀ g, archDerivAtComplex hw .iFm (archDerivAtComplex hw .E u) g =
      archDerivAtComplex hw .E (archDerivAtComplex hw .iFm u) g - archDerivAtComplex hw .iH u g) ∧
    (∀ g, archDerivAtComplex hw .iH (archDerivAtComplex hw .Fm u) g =
      archDerivAtComplex hw .Fm (archDerivAtComplex hw .iH u) g - 2 * archDerivAtComplex hw .iFm u g) ∧
    (∀ g, archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm u) g =
      archDerivAtComplex hw .Fm (archDerivAtComplex hw .iE u) g + archDerivAtComplex hw .iH u g) ∧
    (∀ g, archDerivAtComplex hw .iFm (archDerivAtComplex hw .Fm u) g =
      archDerivAtComplex hw .Fm (archDerivAtComplex hw .iFm u) g) ∧
    (∀ g, archDerivAtComplex hw .iE (archDerivAtComplex hw .iH u) g =
      archDerivAtComplex hw .iH (archDerivAtComplex hw .iE u) g + 2 * archDerivAtComplex hw .E u g) ∧
    (∀ g, archDerivAtComplex hw .iFm (archDerivAtComplex hw .iH u) g =
      archDerivAtComplex hw .iH (archDerivAtComplex hw .iFm u) g - 2 * archDerivAtComplex hw .Fm u g) ∧
    (∀ g, archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE u) g =
      archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm u) g + archDerivAtComplex hw .H u g) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15⟩ :=
    (AutomorphicForm.isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm K w hw).2.2.2 u hu
  refine ⟨fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_,
    fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_⟩
  · have h := congrFun t1 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t2 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t3 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t4 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t5 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t6 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t7 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t8 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t9 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t10 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t11 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t12 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t13 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t14 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h
  · have h := congrFun t15 g; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at h; linear_combination -h

theorem del_rel (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsArchSmoothAtComplex hw u) :
    (archDelAt hw .H (archDelAt hw .E u) - archDelAt hw .E (archDelAt hw .H u) = (2 : ℂ) • archDelAt hw .E u) ∧
    (archDelAt hw .H (archDelAt hw .Fm u) - archDelAt hw .Fm (archDelAt hw .H u) = (-2 : ℂ) • archDelAt hw .Fm u) ∧
    (archDelAt hw .E (archDelAt hw .Fm u) - archDelAt hw .Fm (archDelAt hw .E u) = archDelAt hw .H u) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩ := reorder hw hu
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [del_eq_lin2 hw _ (archDelAt hw _ u), del_eq_lin2 hw _ (archDelAt hw _ u), D_del hw hu, D_del hw hu, D_del hw hu, D_del hw hu]
    funext g
    simp only [ArchDir.toComplex, ArchDir.toComplexI, del_eq_lin2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15]
    ring_nf
    try simp only [Complex.I_sq]
    try ring

theorem delbar_rel (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsArchSmoothAtComplex hw u) :
    (archDelBarAt hw .H (archDelBarAt hw .E u) - archDelBarAt hw .E (archDelBarAt hw .H u) = (2 : ℂ) • archDelBarAt hw .E u) ∧
    (archDelBarAt hw .H (archDelBarAt hw .Fm u) - archDelBarAt hw .Fm (archDelBarAt hw .H u) = (-2 : ℂ) • archDelBarAt hw .Fm u) ∧
    (archDelBarAt hw .E (archDelBarAt hw .Fm u) - archDelBarAt hw .Fm (archDelBarAt hw .E u) = archDelBarAt hw .H u) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩ := reorder hw hu
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [delbar_eq_lin2 hw _ (archDelBarAt hw _ u), delbar_eq_lin2 hw _ (archDelBarAt hw _ u), D_delbar hw hu, D_delbar hw hu,
      D_delbar hw hu, D_delbar hw hu]
    funext g
    simp only [ArchDir.toComplex, ArchDir.toComplexI, delbar_eq_lin2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15]
    ring_nf
    try simp only [Complex.I_sq]
    try ring

theorem cross_rel {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : IsArchSmoothAtComplex hw u) (x y : ArchDir) :
    archDelBarAt hw y (archDelAt hw x u) = archDelAt hw x (archDelBarAt hw y u) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩ := reorder hw hu
  rw [delbar_eq_lin2 hw _ (archDelAt hw _ u), del_eq_lin2 hw _ (archDelBarAt hw _ u), D_del hw hu, D_del hw hu,
    D_delbar hw hu, D_delbar hw hu]
  funext g
  cases x <;> cases y <;>
  · simp only [ArchDir.toComplex, ArchDir.toComplexI, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15]
    ring_nf
    try simp only [Complex.I_sq]
    try ring

theorem casC_eq (u : AdelicGL2 (𝓞 K) K → ℂ) : archCasimirAtComplex hw u = CasA (archDelAt hw) u := rfl
theorem casBarC_eq (u : AdelicGL2 (𝓞 K) K → ℂ) : archCasimirBarAtComplex hw u = CasA (archDelBarAt hw) u := rfl

theorem D_toComplex_eq (e : ArchDir) (v : AdelicGL2 (𝓞 K) K → ℂ) :
    archDerivAtComplex hw e.toComplex v = archDelAt hw e v + archDelBarAt hw e v := by
  funext g; simp only [archDelAt, archDelBarAt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem D_toComplexI_eq (e : ArchDir) (v : AdelicGL2 (𝓞 K) K → ℂ) :
    archDerivAtComplex hw e.toComplexI v = Complex.I • archDelAt hw e v + (-Complex.I) • archDelBarAt hw e v := by
  funext g
  simp only [archDelAt, archDelBarAt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem same_del (e : ArchDir) {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : IsArchSmoothAtComplex hw u) :
    (archCasimirAtComplex hw (archDelAt hw e u) = archDelAt hw e (archCasimirAtComplex hw u) ∧
     archCasimirAtComplex hw (archDelBarAt hw e u) = archDelBarAt hw e (archCasimirAtComplex hw u)) ∧
    (archCasimirBarAtComplex hw (archDelAt hw e u) = archDelAt hw e (archCasimirBarAtComplex hw u) ∧
     archCasimirBarAtComplex hw (archDelBarAt hw e u) = archDelBarAt hw e (archCasimirBarAtComplex hw u)) := by
  have hA1 : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v →
      ∀ x, archDelAt hw x (u + v) = archDelAt hw x u + archDelAt hw x v := fun hu hv x => del_add hw hu hv x
  have hA2 : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v →
      ∀ x, archDelBarAt hw x (u + v) = archDelBarAt hw x u + archDelBarAt hw x v := fun hu hv x => delbar_add hw hu hv x
  have hSs : ∀ {u : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → ∀ c : ℂ, IsArchSmoothAtComplex hw (c • u) :=
    fun hu c => hu.smul c
  have hSadd : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v →
      IsArchSmoothAtComplex hw (u + v) := fun hu hv => hu.add hv
  have hS1 : ∀ (x : ArchDir) {u : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw (archDelAt hw x u) :=
    fun x _ hu => hu.archDelAt x
  have hS2 : ∀ (x : ArchDir) {u : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw (archDelBarAt hw x u) :=
    fun x _ hu => hu.archDelBarAt x
  simp only [casC_eq, casBarC_eq]
  refine ⟨⟨gcomm (archDelAt hw) hA1 (del_smul hw) hSs hSadd hS1 (del_rel hw) e hu, ?_⟩,
    ⟨?_, gcomm (archDelBarAt hw) hA2 (delbar_smul hw) hSs hSadd hS2 (delbar_rel hw) e hu⟩⟩
  · exact (gcross (archDelAt hw) hA1 (del_smul hw) hSs hSadd hS1 (archDelBarAt hw e) (fun hu hv => delbar_add hw hu hv e)
      (delbar_smul hw e) (fun hu => hu.archDelBarAt e) (fun hu x => cross_rel hw hu x e) hu).symm
  · exact (gcross (archDelBarAt hw) hA2 (delbar_smul hw) hSs hSadd hS2 (archDelAt hw e) (fun hu hv => del_add hw hu hv e)
      (del_smul hw e) (fun hu => hu.archDelAt e) (fun hu x => (cross_rel hw hu e x).symm) hu).symm

theorem same (X : ArchDirComplex) {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : IsArchSmoothAtComplex hw u) :
    archCasimirAtComplex hw (archDerivAtComplex hw X u) = archDerivAtComplex hw X (archCasimirAtComplex hw u) ∧
    archCasimirBarAtComplex hw (archDerivAtComplex hw X u) = archDerivAtComplex hw X (archCasimirBarAtComplex hw u) := by
  have hSs : ∀ {u : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → ∀ c : ℂ, IsArchSmoothAtComplex hw (c • u) :=
    fun hu c => hu.smul c
  have hSadd : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v →
      IsArchSmoothAtComplex hw (u + v) := fun hu hv => hu.add hv
  have hA1 : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v →
      ∀ x, archDelAt hw x (u + v) = archDelAt hw x u + archDelAt hw x v := fun hu hv x => del_add hw hu hv x
  have hA2 : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v →
      ∀ x, archDelBarAt hw x (u + v) = archDelBarAt hw x u + archDelBarAt hw x v := fun hu hv x => delbar_add hw hu hv x
  have hS1 : ∀ (x : ArchDir) {u : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw (archDelAt hw x u) :=
    fun x _ hu => hu.archDelAt x
  have hS2 : ∀ (x : ArchDir) {u : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw (archDelBarAt hw x u) :=
    fun x _ hu => hu.archDelBarAt x
  have add1 : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v →
      archCasimirAtComplex hw (u + v) = archCasimirAtComplex hw u + archCasimirAtComplex hw v :=
    fun hu hv => by simp only [casC_eq]; exact casA_add (archDelAt hw) hA1 (del_smul hw) hSs hSadd hS1 hu hv
  have add2 : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v →
      archCasimirBarAtComplex hw (u + v) = archCasimirBarAtComplex hw u + archCasimirBarAtComplex hw v :=
    fun hu hv => by simp only [casBarC_eq]; exact casA_add (archDelBarAt hw) hA2 (delbar_smul hw) hSs hSadd hS2 hu hv
  have sm1 : ∀ (c : ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ), archCasimirAtComplex hw (c • u) = c • archCasimirAtComplex hw u :=
    fun c u => by simp only [casC_eq]; exact casA_smul (archDelAt hw) (del_smul hw) c u
  have sm2 : ∀ (c : ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ), archCasimirBarAtComplex hw (c • u) = c • archCasimirBarAtComplex hw u :=
    fun c u => by simp only [casBarC_eq]; exact casA_smul (archDelBarAt hw) (delbar_smul hw) c u

  have plain : ∀ e : ArchDir,
      archCasimirAtComplex hw (archDerivAtComplex hw e.toComplex u) = archDerivAtComplex hw e.toComplex (archCasimirAtComplex hw u) ∧
      archCasimirBarAtComplex hw (archDerivAtComplex hw e.toComplex u) = archDerivAtComplex hw e.toComplex (archCasimirBarAtComplex hw u) := by
    intro e
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := same_del hw e hu
    have s1 := hu.archDelAt e
    have s2 := hu.archDelBarAt e
    refine ⟨?_, ?_⟩
    · rw [D_toComplex_eq, D_toComplex_eq, add1 s1 s2, a1, a2]
    · rw [D_toComplex_eq, D_toComplex_eq, add2 s1 s2, b1, b2]
  have twisted : ∀ e : ArchDir,
      archCasimirAtComplex hw (archDerivAtComplex hw e.toComplexI u) = archDerivAtComplex hw e.toComplexI (archCasimirAtComplex hw u) ∧
      archCasimirBarAtComplex hw (archDerivAtComplex hw e.toComplexI u) = archDerivAtComplex hw e.toComplexI (archCasimirBarAtComplex hw u) := by
    intro e
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := same_del hw e hu
    have s1 := hu.archDelAt e
    have s2 := hu.archDelBarAt e
    refine ⟨?_, ?_⟩
    · rw [D_toComplexI_eq, D_toComplexI_eq, add1 (s1.smul _) (s2.smul _), sm1, sm1, a1, a2]
    · rw [D_toComplexI_eq, D_toComplexI_eq, add2 (s1.smul _) (s2.smul _), sm2, sm2, b1, b2]
  cases X with
  | H => exact plain .H
  | E => exact plain .E
  | Fm => exact plain .Fm
  | iH => exact twisted .H
  | iE => exact twisted .E
  | iFm => exact twisted .Fm

end Cplx

section Cross

variable {w : InfinitePlace K} (hw : w.IsComplex) {m : ℕ} {b : AdelicGL2 (𝓞 K) K → ℂ}

abbrev Cx (hw : w.IsComplex) (X : ArchDirComplex) : Dir K := Sum.inr ⟨w, hw, X⟩

theorem D1_Cx (X : ArchDirComplex) (v : AdelicGL2 (𝓞 K) K → ℂ) : D1 (Cx hw X) v = archDerivAtComplex hw X v := rfl

theorem Reg3.smoothC (h : Reg3 m b) (l : List (Dir K)) (hl : l.length ≤ m + 2) :
    IsArchSmoothAtComplex hw (Wd l b) := (h l hl).2.2 w hw

theorem del_word (e : ArchDir) (l : List (Dir K)) :
    archDelAt hw e (Wd l b) = (1 / 2 : ℂ) • Wd (Cx hw e.toComplex :: l) b + (-(Complex.I / 2)) • Wd (Cx hw e.toComplexI :: l) b :=
  del_eq_lin2 hw e (Wd l b)

theorem delbar_word (e : ArchDir) (l : List (Dir K)) :
    archDelBarAt hw e (Wd l b) = (1 / 2 : ℂ) • Wd (Cx hw e.toComplex :: l) b + (Complex.I / 2) • Wd (Cx hw e.toComplexI :: l) b :=
  delbar_eq_lin2 hw e (Wd l b)

theorem smoothFor_del_word (h : Reg3 m b) (d : Dir K) (e : ArchDir) (l : List (Dir K)) (hl : l.length + 1 ≤ m + 2) :
    SmoothFor d (archDelAt hw e (Wd l b)) := by
  rw [del_word]
  exact ((h.smoothFor d _ (by simpa using hl)).smul _).add ((h.smoothFor d _ (by simpa using hl)).smul _)

theorem smoothFor_delbar_word (h : Reg3 m b) (d : Dir K) (e : ArchDir) (l : List (Dir K)) (hl : l.length + 1 ≤ m + 2) :
    SmoothFor d (archDelBarAt hw e (Wd l b)) := by
  rw [delbar_word]
  exact ((h.smoothFor d _ (by simpa using hl)).smul _).add ((h.smoothFor d _ (by simpa using hl)).smul _)

theorem del_del_word (h : Reg3 m b) (e e' : ArchDir) (l : List (Dir K)) (hl : l.length + 1 ≤ m + 2) :
    archDelAt hw e (archDelAt hw e' (Wd l b)) =
      (1 / 2 : ℂ) • archDelAt hw e (Wd (Cx hw e'.toComplex :: l) b) +
        (-(Complex.I / 2)) • archDelAt hw e (Wd (Cx hw e'.toComplexI :: l) b) := by
  rw [del_word hw e' l, del_add hw ((h.smoothC hw _ (by simpa using hl)).smul _) ((h.smoothC hw _ (by simpa using hl)).smul _),
    del_smul, del_smul]

theorem delbar_delbar_word (h : Reg3 m b) (e e' : ArchDir) (l : List (Dir K)) (hl : l.length + 1 ≤ m + 2) :
    archDelBarAt hw e (archDelBarAt hw e' (Wd l b)) =
      (1 / 2 : ℂ) • archDelBarAt hw e (Wd (Cx hw e'.toComplex :: l) b) +
        (Complex.I / 2) • archDelBarAt hw e (Wd (Cx hw e'.toComplexI :: l) b) := by
  rw [delbar_word hw e' l, delbar_add hw ((h.smoothC hw _ (by simpa using hl)).smul _) ((h.smoothC hw _ (by simpa using hl)).smul _),
    delbar_smul, delbar_smul]

theorem smoothFor_del_del_word (h : Reg3 m b) (d : Dir K) (e e' : ArchDir) (l : List (Dir K)) (hl : l.length + 2 ≤ m + 2) :
    SmoothFor d (archDelAt hw e (archDelAt hw e' (Wd l b))) := by
  rw [del_del_word hw h e e' l (by omega)]
  exact ((smoothFor_del_word hw h d e _ (by simpa using hl)).smul _).add
    ((smoothFor_del_word hw h d e _ (by simpa using hl)).smul _)

theorem smoothFor_delbar_delbar_word (h : Reg3 m b) (d : Dir K) (e e' : ArchDir) (l : List (Dir K)) (hl : l.length + 2 ≤ m + 2) :
    SmoothFor d (archDelBarAt hw e (archDelBarAt hw e' (Wd l b))) := by
  rw [delbar_delbar_word hw h e e' l (by omega)]
  exact ((smoothFor_delbar_word hw h d e _ (by simpa using hl)).smul _).add
    ((smoothFor_delbar_word hw h d e _ (by simpa using hl)).smul _)

theorem swap_del (h : Reg3 m b) (d : Dir K) (hne : place d ≠ w) (e : ArchDir) (l : List (Dir K))
    (hl : l.length + 2 ≤ m + 2) :
    D1 d (archDelAt hw e (Wd l b)) = archDelAt hw e (D1 d (Wd l b)) := by
  have hne' : ∀ X, place d ≠ place (Cx hw X) := fun X => hne
  rw [del_word hw e l, D1_lin2 d (h.smoothFor d _ (by simp only [List.length_cons]; omega))
    (h.smoothFor d _ (by simp only [List.length_cons]; omega)), Wd_cons, Wd_cons,
    h.swap l hl d (Cx hw _) (hne' _), h.swap l hl d (Cx hw _) (hne' _), D1_Cx, D1_Cx, ← del_eq_lin2]

theorem swap_delbar (h : Reg3 m b) (d : Dir K) (hne : place d ≠ w) (e : ArchDir) (l : List (Dir K))
    (hl : l.length + 2 ≤ m + 2) :
    D1 d (archDelBarAt hw e (Wd l b)) = archDelBarAt hw e (D1 d (Wd l b)) := by
  have hne' : ∀ X, place d ≠ place (Cx hw X) := fun X => hne
  rw [delbar_word hw e l, D1_lin2 d (h.smoothFor d _ (by simp only [List.length_cons]; omega))
    (h.smoothFor d _ (by simp only [List.length_cons]; omega)), Wd_cons, Wd_cons,
    h.swap l hl d (Cx hw _) (hne' _), h.swap l hl d (Cx hw _) (hne' _), D1_Cx, D1_Cx, ← delbar_eq_lin2]

theorem swap_del_del (h : Reg3 m b) (d : Dir K) (hne : place d ≠ w) (e e' : ArchDir) (l : List (Dir K))
    (hl : l.length + 3 ≤ m + 2) :
    D1 d (archDelAt hw e (archDelAt hw e' (Wd l b))) = archDelAt hw e (archDelAt hw e' (D1 d (Wd l b))) := by
  have hne' : ∀ X, place d ≠ place (Cx hw X) := fun X => hne
  have sV : IsArchSmoothAtComplex hw (D1 d (Wd l b)) := h.smoothC hw (d :: l) (by simp only [List.length_cons]; omega)
  rw [del_del_word hw h e e' l (by omega),
    D1_lin2 d (smoothFor_del_word hw h d e _ (by simp only [List.length_cons]; omega))
      (smoothFor_del_word hw h d e _ (by simp only [List.length_cons]; omega)),
    swap_del hw h d hne e _ (by simp only [List.length_cons]; omega),
    swap_del hw h d hne e _ (by simp only [List.length_cons]; omega),
    Wd_cons, Wd_cons, h.swap l (by omega) d (Cx hw _) (hne' _), h.swap l (by omega) d (Cx hw _) (hne' _), D1_Cx, D1_Cx,
    del_eq_lin2 hw e' (D1 d (Wd l b)), del_add hw ((sV.archDerivAtComplex _).smul _) ((sV.archDerivAtComplex _).smul _),
    del_smul, del_smul]

theorem swap_delbar_delbar (h : Reg3 m b) (d : Dir K) (hne : place d ≠ w) (e e' : ArchDir) (l : List (Dir K))
    (hl : l.length + 3 ≤ m + 2) :
    D1 d (archDelBarAt hw e (archDelBarAt hw e' (Wd l b))) = archDelBarAt hw e (archDelBarAt hw e' (D1 d (Wd l b))) := by
  have hne' : ∀ X, place d ≠ place (Cx hw X) := fun X => hne
  have sV : IsArchSmoothAtComplex hw (D1 d (Wd l b)) := h.smoothC hw (d :: l) (by simp only [List.length_cons]; omega)
  rw [delbar_delbar_word hw h e e' l (by omega),
    D1_lin2 d (smoothFor_delbar_word hw h d e _ (by simp only [List.length_cons]; omega))
      (smoothFor_delbar_word hw h d e _ (by simp only [List.length_cons]; omega)),
    swap_delbar hw h d hne e _ (by simp only [List.length_cons]; omega),
    swap_delbar hw h d hne e _ (by simp only [List.length_cons]; omega),
    Wd_cons, Wd_cons, h.swap l (by omega) d (Cx hw _) (hne' _), h.swap l (by omega) d (Cx hw _) (hne' _), D1_Cx, D1_Cx,
    delbar_eq_lin2 hw e' (D1 d (Wd l b)), delbar_add hw ((sV.archDerivAtComplex _).smul _) ((sV.archDerivAtComplex _).smul _),
    delbar_smul, delbar_smul]

theorem comm_cross (h : Reg3 m b) (l : List (Dir K)) (hl : l.length + 1 ≤ m) (d : Dir K) (hne : place d ≠ w) :
    archCasimirAtComplex hw (D1 d (Wd l b)) = D1 d (archCasimirAtComplex hw (Wd l b)) ∧
    archCasimirBarAtComplex hw (D1 d (Wd l b)) = D1 d (archCasimirBarAtComplex hw (Wd l b)) := by
  constructor
  · rw [casC_eq, casC_eq, casA_lin3, casA_lin3,
      D1_lin3 d (smoothFor_del_del_word hw h d .H .H l (by omega)) (smoothFor_del_word hw h d .H l (by omega))
        (smoothFor_del_del_word hw h d .E .Fm l (by omega)),
      swap_del_del hw h d hne .H .H l (by omega), swap_del hw h d hne .H l (by omega), swap_del_del hw h d hne .E .Fm l (by omega)]
  · rw [casBarC_eq, casBarC_eq, casA_lin3, casA_lin3,
      D1_lin3 d (smoothFor_delbar_delbar_word hw h d .H .H l (by omega)) (smoothFor_delbar_word hw h d .H l (by omega))
        (smoothFor_delbar_delbar_word hw h d .E .Fm l (by omega)),
      swap_delbar_delbar hw h d hne .H .H l (by omega), swap_delbar hw h d hne .H l (by omega),
      swap_delbar_delbar hw h d hne .E .Fm l (by omega)]

theorem main (h : Reg3 m b) :
    ∀ l : List (Dir K), l.length ≤ m →
      archCasimirAtComplex hw (Wd l b) = Wd l (archCasimirAtComplex hw b) ∧
      archCasimirBarAtComplex hw (Wd l b) = Wd l (archCasimirBarAtComplex hw b)
  | [], _ => ⟨rfl, rfl⟩
  | d :: l, hl => by
    rw [List.length_cons] at hl
    obtain ⟨ih1, ih2⟩ := main h l (by omega)
    rw [Wd_cons, Wd_cons, Wd_cons, ← ih1, ← ih2]
    by_cases hd : place d = w
    · rcases d with ⟨w', hw', x⟩ | ⟨w', hw', x⟩
      · change w' = w at hd
        subst hd
        exact absurd hw' (NumberField.InfinitePlace.not_isReal_iff_isComplex.2 hw)
      · change w' = w at hd
        subst hd
        exact same hw x (h.smoothC hw l (by omega))
    · exact comm_cross hw h l (by omega) d hd

end Cross

end CasC

theorem solution
    (K : Type) [Field K] [NumberField K] (m : ℕ)
    (b : AdelicGL2 (𝓞 K) K → ℂ) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    (∀ l, l.length ≤ m + 2 →
      Continuous (W l b) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b))) →
    ∀ (w : InfinitePlace K) (hw : w.IsComplex)
      (l : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
        (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex))), l.length ≤ m →
      archCasimirAtComplex hw (W l b) = W l (archCasimirAtComplex hw b) ∧
        archCasimirBarAtComplex hw (W l b) = W l (archCasimirBarAtComplex hw b) := by
  intro W hreg w hw l hl
  have hreg' : CasC.Reg3 m b := hreg
  exact CasC.main hw hreg' l hl

end

end S_AutomorphicForm_archCasimirAtComplex_and_archCasimirBarAtComplex_foldr_archDeriv_eq_foldr_archDeriv
end P2MW
export P2MW.S_AutomorphicForm_archCasimirAtComplex_and_archCasimirBarAtComplex_foldr_archDeriv_eq_foldr_archDeriv (solution)
