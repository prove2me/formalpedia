-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_OneCosetSharp
-- name    : Formalism_PeriodIntegrals_OneCosetSharp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:22.065503+00:00
-- url     : https://prove2.me/theorems/871a0e1b-9ff4-49e7-975c-70bba73a4a94
-- title:
--   One Coset Sharp
-- statement:
--   Definitions and structural lemmas for One Coset Sharp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OneCosetSharp.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module MvPolynomial
noncomputable section
namespace PI.OneCosetSharp
namespace Loc
section Groups
variable (k : Type) [CommRing k] (n c : ℕ)
def atN {k : Type} [CommRing k] {N : ℕ} (v : Fin N → k) (i : ℕ) : k := if h : i < N then v ⟨i, h⟩ else 0
def eN (N i : ℕ) : Fin N → k := fun l => if l.1 = i then 1 else 0
def supp (N : ℕ) (s : Set ℕ) : Submodule k (Fin N → k) where
  carrier := {v | ∀ l : Fin N, l.1 ∉ s → v l = 0}
  add_mem' := fun {a b} ha hb l hl => by simp [ha l hl, hb l hl]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r a ha l hl => by simp [ha l hl]
def Ufl (i : ℕ) : Submodule k (Fin (n + c) → k) := supp k (n + c) {l | l < n + i}
def inX : (Fin n → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if h : l.1 < n then LinearMap.proj ⟨l.1, h⟩ else 0
def R1cond (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ i, ∀ v ∈ Ufl k n c i, r v ∈ Ufl k n c i) ∧ r (eN k (n + c) n) = eN k (n + c) n ∧
    ∀ i, r (eN k (n + c) (n + i)) - eN k (n + c) (n + i) ∈ Ufl k n c i
variable {k n c} in
theorem R1cond.mul {r s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hs : R1cond k n c s) :
    R1cond k n c (r * s) := by
  refine ⟨fun i v hv => hr.1 i _ (hs.1 i v hv), ?_, fun i => ?_⟩
  · show r (s _) = _
    rw [hs.2.1, hr.2.1]
  · have h1 := hr.1 i _ (hs.2.2 i)
    have h2 := hr.2.2 i
    have key : (r * s) (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i) =
        r (s (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) +
          (r (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) := by
      show r (s _) - _ = _
      rw [map_sub]
      abel
    rw [key]
    exact Submodule.add_mem _ h1 h2
theorem R1cond_one : R1cond k n c 1 := by
  refine ⟨fun i v hv => hv, rfl, fun i => ?_⟩
  show eN k (n + c) (n + i) - eN k (n + c) (n + i) ∈ _
  rw [sub_self]
  exact Submodule.zero_mem _
def R1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | R1cond k n c r ∧ R1cond k n c r⁻¹}
  one_mem' := ⟨R1cond_one k n c, by rw [inv_one]; exact R1cond_one k n c⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, by rw [mul_inv_rev]; exact hb.2.mul ha.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩
def fixX : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | ∀ x, r (inX k n c x) = inX k n c x}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb x => by
    show a (b _) = _
    rw [hb, ha]
  inv_mem' := fun {a} ha x => by
    have h := ha x
    show a.symm _ = _
    rw [LinearEquiv.symm_apply_eq, h]
def N1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) := R1 k n c ⊓ fixX k n c
variable {k n c}
def n1Arg (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range (c - 1), atN (r (eN k (n + c) (n + i + 1))) (n + i)
def Cbe (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :=
  R1 k n c ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom
def prX (C : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) : Subgroup ((Fin n → k) ≃ₗ[k] (Fin n → k)) where
  carrier := {g | ∃ r ∈ C, ∀ x, r (inX k n c x) = inX k n c (g x)}
  one_mem' := ⟨1, C.one_mem, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨r, hr, h1⟩ ⟨s, hs, h2⟩
    refine ⟨r * s, C.mul_mem hr hs, fun x => ?_⟩
    show r (s _) = _
    rw [h2, h1]
    rfl
  inv_mem' := by
    rintro a ⟨r, hr, h1⟩
    refine ⟨r⁻¹, C.inv_mem hr, fun x => ?_⟩
    show r.symm _ = _
    rw [LinearEquiv.symm_apply_eq, h1]
    show _ = inX k n c (a (a.symm x))
    rw [LinearEquiv.apply_symm_apply]
def volN (K : Type) [Field K] (C N1O : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) : K :=
  ((N1O.relIndex (C ⊓ N1 k n c) : ℕ) : K) / (((C ⊓ N1 k n c).relIndex N1O : ℕ) : K)
end Groups
section Data
variable {k K : Type} [CommRing k] [Field K]
abbrev SF (k K : Type) [CommRing k] (a b : ℕ) : Type := ((Fin a → k) →ₗ[k] (Fin b → k)) → K
def om {a b : ℕ} (mu : k → K) (v : k → ℤ) (sq : K) (g₀ : (Fin a → k) ≃ₗ[k] (Fin a → k))
    (h : (Fin b → k) ≃ₗ[k] (Fin b → k)) (Φ : SF k K a b) : SF k K a b := fun x =>
  mu (LinearEquiv.det g₀ : kˣ) * (mu (LinearEquiv.det h : kˣ))⁻¹ * sq ^ (-(v (LinearEquiv.det g₀ : kˣ)) * b) *
    sq ^ (v (LinearEquiv.det h : kˣ) * a) * Φ (h.symm.toLinearMap ∘ₗ x ∘ₗ g₀.toLinearMap)
variable (n' c' n c : ℕ)
def IsFree (l s : ℕ) : Prop := n' ≤ s ∧ (s - n' = c ∨ (1 ≤ s - n' ∧ (l < n ∨ l - n < s - n')))
instance (l s : ℕ) : Decidable (IsFree n' n c l s) := by unfold IsFree; infer_instance
abbrev FC : Type := {p : Fin (n + c) × Fin (n' + c') // IsFree n' n c p.1.1 p.2.1}
variable {n' c' n c}
def xx1 (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' c' n c → k) : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
    else if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
    else if l.1 = n + (s.1 - n') then 1 else 0)
def chArg (x : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range c, atN (x (eN k (n' + c') (n' + i + 1))) (n + i)
def E1 (psi : k → K) (vals : Finset k) (wt : K) (Φ : SF k K (n' + c') (n + c)) : SF k K n' n := fun xj =>
  wt ^ Fintype.card (FC n' c' n c) *
    ∑ t ∈ Fintype.piFinset fun _ : FC n' c' n c => vals, Φ (xx1 xj t) * psi (-chArg (xx1 xj t))
end Data
end Loc
namespace LocE
def fIdx (k₀ c n s : ℕ) : ℕ := if s < k₀ then s else if s < k₀ + c then n + (s - k₀) else s - c
end LocE
open Loc LocE
def chiV {k : Type} [Field k] [DecidableEq k] (χ : kˣ →* ℂˣ) (x : k) : ℂ := if h : x = 0 then 0 else ((χ (Units.mk0 x h) : ℂˣ) : ℂ)
def ent {k : Type} [Field k] {A B : ℕ} (k₀ cA nA cB nB : ℕ) (x : (Fin A → k) →ₗ[k] (Fin B → k)) (p p' : ℕ) : k :=
  atN (x (eN k A (fIdx k₀ cA nA p'))) (fIdx k₀ cB nB p)
def Allow (k₀ m t N p p' : ℕ) : Prop :=
  if p' < k₀ then p < p' ∨ (k₀ ≤ p ∧ p < k₀ + (m / 2 - 1))
  else if p' < k₀ + m - 1 then (k₀ ≤ p ∧ p < p') ∨ (m / 2 < p' + 1 - k₀ ∧ p < k₀)
  else p < k₀ + m - 1 ∨ (p < N ∧ (p - (k₀ + m - 1)) / t ≤ (p' - (k₀ + m - 1)) / t)
open Classical in

def PhiS {k : Type} [Field k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ) : SF k ℂ (n' + (c + 1)) (n + c) :=
  fun x =>
    let M := ent k₀ (c + 1) n' c n x
    let r := k₀ + m - 1
    let a := r + (j - 1) * t
    if (∀ p', p' < r → M p' p' = 1) ∧ (∀ p p', p < n + c → p' < a → p ≠ p' → M p p' ≠ 0 → Allow k₀ m t a p p')
    then ψ₀ (∑ i ∈ Finset.range (r - 1), M i (i + 1)) *
        (∏ i ∈ Finset.range (j - 1),
          chiV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1)))) *
        (chiV (χ (j - 1)) (Matrix.det (Matrix.of fun s s' : Fin a => M s.1 s'.1)))⁻¹
    else 0
def InJS {k : Type} [Field k] (k₀ m t c n : ℕ) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ p', p' < k₀ + m - 1 → ent k₀ c n c n κ.toLinearMap p' p' = 1) ∧
    ∀ p p', p < n + c → p' < n + c → p ≠ p' → ent k₀ c n c n κ.toLinearMap p p' ≠ 0 → Allow k₀ m t (n + c) p p'
def OneCosetSharp : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ),
    1 ≤ k₀ → Even m → 4 ≤ m → 1 ≤ j → j ≤ m - 2 → c = m - 1 - j →
    n' + (c + 1) = k₀ + m - 1 + (j - 1) * t → n + c = k₀ + m - 1 + j * t →
    (∀ h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k),
        (∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
          E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1
            (om (fun _ => 1) (fun _ => 0) 1 (LinearEquiv.refl k _) h (PhiS ψ₀ χ k₀ m t j n' c n)) xj ≠ 0) →
        ∃ ρ ∈ R1 k n c, ∃ κ, InJS k₀ m t c n κ ∧ h = ρ * κ) ∧
    ∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
      E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1 (PhiS ψ₀ χ k₀ m t j n' c n) xj ≠ 0
end PI.OneCosetSharp
end


