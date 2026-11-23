-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:54.136827+00:00
-- url     : https://prove2.me/theorems/a04910a3-f5e4-4f14-ad4e-e5157a9a50f6
-- title:
--   Is Open Alt
-- statement:
--   Definitions and structural lemmas for Is Open Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IsOpenAlt.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def conePts (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Set ((Σ k, ι k) → ℂ) :=
  {z | (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ P, eval z f = 0}
def SameOrbit (z z' : (Σ k, ι k) → ℂ) : Prop :=
  ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = fun q => c q.1 * z' q
def affCoord (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => z q / z ⟨q.1, p q.1⟩
def IsMultiHomog (s : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) : Prop :=
  ∀ m ∈ s.support, ∀ k, ∑ i, m ⟨k, i⟩ = a k
structure SncData {m : ℕ} (I bd : Ideal (MvPolynomial (Fin m) ℂ)) (p : Fin m → ℂ) (e rc : ℕ) where

  r : Fin e → MvPolynomial (Fin m) ℂ

  J : Finset (Fin e)

  h : MvPolynomial (Fin m) ℂ

  σ : Fin e → Option (Fin rc)
  σ_injOn : Set.InjOn σ J
  σ_eq_none : ∀ l, σ l = none ↔ l ∉ J
  span_eq : Ideal.span (Set.range fun l => algebraMap _ (locRing I p) (r l)) =
    Ideal.map (algebraMap _ (locRing I p)) (ptIdeal p)
  eval_h : eval p h ≠ 0
  mem_bd : h * ∏ l ∈ J, r l ∈ bd
  le_span : ∀ g ∈ bd, h * g ∈ Ideal.span {∏ l ∈ J, r l} ⊔ I
variable (ι) in

structure AlgRes (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) where

  M : Type
  [top : TopologicalSpace M]
  [compact : CompactSpace M]
  [t2 : T2Space M]

  n : ℕ

  amb : Fin n → ℕ

  ideal : ∀ i, Ideal (MvPolynomial (Fin (amb i)) ℂ)

  src : Fin n → Set M
  isOpen_alt_bis : ∀ i, IsOpen (src i)
  cover : ∀ x, ∃ i, x ∈ src i

  coord : ∀ i, M → Fin (amb i) → ℂ
  isEmbedding : ∀ i, Topology.IsEmbedding fun y : src i => coord i y
  image : ∀ i, coord i '' src i = {y | ∀ h ∈ ideal i, eval y h = 0}

  trans : ∀ i j, ∀ x ∈ src i ∩ src j, ∃ (q : MvPolynomial (Fin (amb i)) ℂ)
    (F : Fin (amb j) → MvPolynomial (Fin (amb i)) ℂ), eval (coord i x) q ≠ 0 ∧
      ∀ y ∈ src i ∩ src j, eval (coord i y) q ≠ 0 →
        ∀ l, coord j y l * eval (coord i y) q = eval (coord i y) (F l)
  regular : ∀ i, ∀ x ∈ src i, IsRegularLocalRing (locRing (ideal i) (coord i x))
  dim : ∀ i, ∀ x ∈ src i, ringKrullDim (locRing (ideal i) (coord i x)) = e

  lift : ∀ i, (Σ k, ι k) → MvPolynomial (Fin (amb i)) ℂ
  lift_one : ∀ i, ∃ p : (k : K) → ι k, ∀ k, lift i ⟨k, p k⟩ = 1
  lift_mem : ∀ i, ∀ x ∈ src i, (fun q => eval (coord i x) (lift i q)) ∈ conePts P
  compat : ∀ i j, ∀ x ∈ src i ∩ src j,
    SameOrbit (fun q => eval (coord i x) (lift i q)) (fun q => eval (coord j x) (lift j q))
  surj : ∀ z ∈ conePts P, z ∉ conePts D →
    ∃ i, ∃ x ∈ src i, SameOrbit (fun q => eval (coord i x) (lift i q)) z
  inj : ∀ i j, ∀ x ∈ src i, ∀ x' ∈ src j, (fun q => eval (coord i x) (lift i q)) ∉ conePts D →
    SameOrbit (fun q => eval (coord i x) (lift i q)) (fun q => eval (coord j x') (lift j q)) →
      x = x'

  inv : ∀ i, ∀ x ∈ src i, (fun q => eval (coord i x) (lift i q)) ∉ conePts D →
    ∀ p : (k : K) → ι k, (∀ k, eval (coord i x) (lift i ⟨k, p k⟩) ≠ 0) →
      ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ O ⊆ src i ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ)
        (F : Fin (amb i) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O,
          (∀ k, eval (coord i y) (lift i ⟨k, p k⟩) ≠ 0) ∧
          eval (affCoord p fun q => eval (coord i y) (lift i q)) q ≠ 0 ∧
          ∀ l, coord i y l * eval (affCoord p fun q => eval (coord i y) (lift i q)) q =
            eval (affCoord p fun q => eval (coord i y) (lift i q)) (F l)

  bd : ∀ i, Ideal (MvPolynomial (Fin (amb i)) ℂ)
  le_bd : ∀ i, ideal i ≤ bd i
  zero_bd : ∀ i, ∀ x ∈ src i,
    (∀ h ∈ bd i, eval (coord i x) h = 0) ↔ (fun q => eval (coord i x) (lift i q)) ∈ conePts D

  rc : ℕ

  comp : Fin rc → Set M

  sncAt : ∀ i, ∀ x ∈ src i, SncData (ideal i) (bd i) (coord i x) e rc

  comp_eq : ∀ i x (hx : x ∈ src i), ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ O ⊆ src i ∧ ∀ k,
    comp k ∩ O = {y ∈ O | ∃ l, (sncAt i x hx).σ l = some k ∧ eval (coord i y) ((sncAt i x hx).r l) = 0}

  mult : ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomog f a → f ∉ P →
    (∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D) → ∃ m : Fin rc → ℕ, ∀ i x (hx : x ∈ src i),
      ∃ u : locRing (ideal i) (coord i x), IsUnit u ∧
        algebraMap _ (locRing (ideal i) (coord i x)) (bind₁ (lift i) f) =
          u * ∏ l ∈ (sncAt i x hx).J,
            algebraMap _ (locRing (ideal i) (coord i x)) ((sncAt i x hx).r l) ^ ((sncAt i x hx).σ l).elim 0 m
attribute [instance] AlgRes.top AlgRes.compact AlgRes.t2
end
end ReciprocityTheory.AnForm.R


