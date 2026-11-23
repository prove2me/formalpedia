-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnfoldEquiv
-- name    : Formalism_PeriodIntegrals_UnfoldEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:24.230957+00:00
-- url     : https://prove2.me/theorems/194f4942-8890-4299-8d54-9ad5181be7c9
-- title:
--   Unfold Equiv
-- statement:
--   Definitions and structural lemmas for Unfold Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnfoldEquiv.lean

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
namespace PI.UnfoldEquiv
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
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · rw [LinearEquiv.mul_apply]
    exact hr.1 i _ (hs.1 i v hv)
  · rw [LinearEquiv.mul_apply, hs.2.1, hr.2.1]
  · rw [LinearEquiv.mul_apply]
    have h1 : r (s (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i))) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i) =
        r (s (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) +
          (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) := by
      rw [map_sub]; abel
    rw [h1]
    exact Submodule.add_mem _ (hr.1 i _ (hs.2.2 i)) (hr.2.2 i)
theorem R1cond_one : R1cond k n c 1 := by
  refine ⟨fun i v hv => hv, rfl, fun i => ?_⟩
  rw [show (1 : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (eN k (n + c) (n + i)) =
      eN k (n + c) (n + i) from rfl, sub_self]
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
def UnfoldEquiv : Prop :=
  ∀ (k K : Type) [CommRing k] [Fintype k] [Field K] (n' n c : ℕ) (psi : k → K), (∀ a b, psi (a + b) = psi a * psi b) →
    ∀ (wt : K) (Φ : Loc.SF k K (n' + (c + 1)) (n + c)) (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))
      (g : (Fin n → k) ≃ₗ[k] (Fin n → k)),
      r ∈ Loc.R1 k n c → (∀ x, r (Loc.inX k n c x) = Loc.inX k n c (g x)) →
      ∀ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
        Loc.E1 (n' := n') (c' := c + 1) (n := n) (c := c) psi Finset.univ wt (fun x => Φ (r.symm.toLinearMap ∘ₗ x)) xj =
          psi (-(Loc.n1Arg r)) * Loc.E1 (n' := n') (c' := c + 1) (n := n) (c := c) psi Finset.univ wt Φ (g.symm.toLinearMap ∘ₗ xj)
end PI.UnfoldEquiv
end


