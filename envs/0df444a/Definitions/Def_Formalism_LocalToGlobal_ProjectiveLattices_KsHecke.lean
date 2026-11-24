-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_KsHecke
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_KsHecke
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:15.691455+00:00
-- url     : https://prove2.me/theorems/2bf4a879-bdec-492e-82d0-b40614cdfa66
-- title:
--   Ks Hecke
-- statement:
--   Definitions and structural lemmas for Ks Hecke, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/KsHecke.lean

import Mathlib
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
namespace Formalism.L2.Pj
namespace KsHecke
open Polynomial
section Gen
variable {L : Type*} [Field L] {WL : Type*} [AddCommGroup WL] [Module L WL]
  {XS : Type*} [AddCommGroup XS] [Module L XS] {G : Type*}
def IsHL (act : G → WL →ₗ[L] WL) (th : XS → WL) (TV : XS →ₗ[L] XS) (T : WL →ₗ[L] WL) : Prop :=
  (∀ g, T ∘ₗ act g = act g ∘ₗ T) ∧ ∀ x, T (th x) = th (TV x)
open Classical in

def hLby (act : G → WL →ₗ[L] WL) (th : XS → WL) (TV : XS →ₗ[L] XS) : WL →ₗ[L] WL :=
  if h : ∃! T, IsHL act th TV T then h.choose else 0
variable {act : G → WL →ₗ[L] WL} {th : XS → WL} {TV : XS →ₗ[L] XS}
def ThSpan (th : XS → WL) : Prop := Submodule.span L (Set.range th) = ⊤
def KerStab (Th : XS →ₗ[L] WL) (TV : XS →ₗ[L] XS) : Prop := ∀ x, Th x = 0 → Th (TV x) = 0
def ActTie (act : G → WL →ₗ[L] WL) (Th : XS →ₗ[L] WL) (TV : XS →ₗ[L] XS) (actX : G → XS →ₗ[L] XS) : Prop :=
  ∀ g x, act g (Th x) = Th (actX g x) ∧ act g (Th (TV x)) = Th (TV (actX g x))
def eqvTh (Th : XS →ₗ[L] WL) (hs : LinearMap.range Th = ⊤) : (XS ⧸ LinearMap.ker Th) ≃ₗ[L] WL :=
  Th.quotKerEquivOfSurjective (LinearMap.range_eq_top.mp hs)
theorem kerStab_le {Th : XS →ₗ[L] WL} (hk : KerStab Th TV) :
    LinearMap.ker Th ≤ (LinearMap.ker Th).comap TV := by
  intro x hx
  simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
  exact hk x hx
def desc (Th : XS →ₗ[L] WL) (TV : XS →ₗ[L] XS) (hs : LinearMap.range Th = ⊤) (hk : KerStab Th TV) :
    WL →ₗ[L] WL :=
  (eqvTh Th hs).toLinearMap ∘ₗ (LinearMap.ker Th).mapQ (LinearMap.ker Th) TV (kerStab_le hk) ∘ₗ
    (eqvTh Th hs).symm.toLinearMap
def thE (e : WL →ₗ[L] WL) (th : XS → WL) : XS → LinearMap.range e :=
  fun x => ⟨e (th x), LinearMap.mem_range_self e (th x)⟩
def actE (e : WL →ₗ[L] WL) (act : G → WL →ₗ[L] WL) (hc : ∀ g, e ∘ₗ act g = act g ∘ₗ e) (g : G) :
    LinearMap.range e →ₗ[L] LinearMap.range e :=
  (act g).restrict (p := LinearMap.range e) (q := LinearMap.range e) fun w hw => by
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
    exact LinearMap.mem_range.mpr ⟨act g v, LinearMap.congr_fun (hc g) v⟩
def hLe (e : WL →ₗ[L] WL) (act : G → WL →ₗ[L] WL) (hc : ∀ g, e ∘ₗ act g = act g ∘ₗ e) (th : XS → WL)
    (TV : XS →ₗ[L] XS) : LinearMap.range e →ₗ[L] LinearMap.range e :=
  hLby (actE e act hc) (thE e th) TV
def extE (e : WL →ₗ[L] WL) (T : LinearMap.range e →ₗ[L] LinearMap.range e) : WL →ₗ[L] WL :=
  (LinearMap.range e).subtype ∘ₗ T ∘ₗ e.rangeRestrict
def hLext (e : WL →ₗ[L] WL) (act : G → WL →ₗ[L] WL) (hc : ∀ g, e ∘ₗ act g = act g ∘ₗ e) (th : XS → WL)
    (TV : XS →ₗ[L] XS) : WL →ₗ[L] WL :=
  extE e (hLe e act hc th TV)
end Gen
section Str
variable {L : Type*} [Field L] {XS : Type*} [AddCommGroup XS] [Module L XS]
def HeckeIdentityAtZero (tV : ℕ → XS →ₗ[L] XS) : Prop := tV 0 = LinearMap.id
def cStr (B q : L) (r t : ℕ) : L[X] :=
  ∏ j ∈ Finset.range t, (1 - C (B * q ^ ((r - 1) / 2 + j)) * X)
def cInvCoeff (cX : L[X]) (m : ℕ) : L := PowerSeries.coeff (R := L) m ((cX : PowerSeries L)⁻¹)
def Gk (cX : L[X]) (q : L) (tV : ℕ → XS →ₗ[L] XS) (k : ℕ) : XS →ₗ[L] XS :=
  (-1 : L) ^ k • ∑ i ∈ Finset.range (k + 1),
    (cInvCoeff cX (k - i) * ((-1 : L) ^ i * q ^ (i * (i - 1) / 2))) • tV i
def kap (B q : L) (r n : ℕ) : L := B⁻¹ * q ^ ((((r + 1) / 2 : ℕ) : ℤ) - (n : ℤ))
def TVk (B q : L) (r n t : ℕ) (tV : ℕ → XS →ₗ[L] XS) (k : ℕ) : XS →ₗ[L] XS :=
  ((q ^ (k * (k - 1) / 2))⁻¹ * kap B q r n ^ k) • Gk (cStr B q r t) q tV k
def ROdd (r : ℕ) : Prop := Odd r
def CStrIs (cRec : L[X]) (B q : L) (r t : ℕ) : Prop := cRec = cStr B q r t
end Str
section Test
def tvT : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) := LinearMap.prodMap ((2 : ℚ) • LinearMap.id) ((3 : ℚ) • LinearMap.id)
end Test
end KsHecke
end Formalism.L2.Pj


