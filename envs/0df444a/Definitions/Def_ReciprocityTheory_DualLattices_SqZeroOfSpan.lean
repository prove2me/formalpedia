-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
-- name    : ReciprocityTheory_DualLattices_SqZeroOfSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:29.048706+00:00
-- url     : https://prove2.me/theorems/e9c068bf-fcf4-4eac-81bc-71d1ac1dc002
-- title:
--   Sq Zero Of Span
-- statement:
--   Definitions and structural lemmas for Sq Zero Of Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SqZeroOfSpan.lean

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
open IsLocalRing TensorProduct
namespace ReciprocityTheory.PGsh
universe u
structure LAlg (R₀ : Type u) [CommRing R₀] where
  carrier : Type u
  [cr : CommRing carrier]
  [alg : Algebra R₀ carrier]
  [loc : IsLocalRing carrier]
attribute [instance] LAlg.cr LAlg.alg LAlg.loc
variable {R₀ : Type u} [CommRing R₀]
instance : CoeSort (LAlg R₀) (Type u) := ⟨LAlg.carrier⟩
def LHom (R S : LAlg R₀) : Type u := {f : R →ₐ[R₀] S // IsLocalHom (f : R →+* S)}
def LHom.id (R : LAlg R₀) : LHom R R := ⟨AlgHom.id R₀ R, ⟨fun _ h => h⟩⟩
def LHom.comp {R S T : LAlg R₀} (g : LHom S T) (f : LHom R S) : LHom R T :=
  ⟨g.1.comp f.1, ⟨fun a h => f.2.map_nonunit a (g.2.map_nonunit (f.1 a) h)⟩⟩
abbrev LHom.ker {R S : LAlg R₀} (π : LHom R S) : Submodule R₀ R :=
  (RingHom.ker π.1).restrictScalars R₀
def LHom.SqZero {R S : LAlg R₀} (π : LHom R S) : Prop :=
  Function.Surjective π.1 ∧ RingHom.ker π.1 ^ 2 = ⊥
def LHom.NilSurj {R S : LAlg R₀} (π : LHom R S) : Prop :=
  Function.Surjective π.1 ∧ ∃ n : ℕ, RingHom.ker π.1 ^ n = ⊥
def IsFibreSq {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R)
    (f₂ : LHom R₂ R) : Prop :=
  f₁.1.comp p₁.1 = f₂.1.comp p₂.1 ∧ f₁.NilSurj ∧ f₂.NilSurj ∧
    ∀ a b, f₁.1 a = f₂.1 b → ∃! c, p₁.1 c = a ∧ p₂.1 c = b
def CarriesFibre {X₁ X₂ X Y : Type*} (q₁ : Y → X₁) (q₂ : Y → X₂) (g₁ : X₁ → X) (g₂ : X₂ → X) :
    Prop :=
  ∀ a b, g₁ a = g₂ b → ∃! c, q₁ c = a ∧ q₂ c = b
structure BX (R₀ : Type u) [CommRing R₀] where
  G : LAlg R₀ → Type u
  [grp : ∀ R, AddCommGroup (G R)]
  map : ∀ {R S : LAlg R₀}, LHom R S → G R →+ G S
  map_id : ∀ (R : LAlg R₀) (x : G R), map (LHom.id R) x = x
  map_comp : ∀ {R S T : LAlg R₀} (f : LHom R S) (g : LHom S T) (x : G R),
    map (g.comp f) x = map g (map f x)
  gg : Type u
  [ggg : AddCommGroup gg]
  [ggm : Module R₀ gg]
  [ggfree : Module.Free R₀ gg]
  [ggfin : Module.Finite R₀ gg]
  tg : ∀ {R S : LAlg R₀} (π : LHom R S), π.SqZero → gg ⊗[R₀] π.ker →+ G R
  tg_nat : ∀ {R S R' S' : LAlg R₀} (π : LHom R S) (π' : LHom R' S') (hπ : π.SqZero)
    (hπ' : π'.SqZero) (f : LHom R R') (hf : ∀ a ∈ π.ker, f.1.toLinearMap a ∈ π'.ker)
    (v : gg ⊗[R₀] π.ker),
    tg π' hπ' (LinearMap.lTensor gg (f.1.toLinearMap.restrict hf) v) = map f (tg π hπ v)
  surj : ∀ {R S : LAlg R₀} (π : LHom R S), π.SqZero → Function.Surjective (map π)
  tg_inj : ∀ {R S : LAlg R₀} (π : LHom R S) (hπ : π.SqZero), Function.Injective (tg π hπ)
  tg_ker : ∀ {R S : LAlg R₀} (π : LHom R S) (hπ : π.SqZero) (x : G R),
    map π x = 0 ↔ ∃ v, tg π hπ v = x
  P : ∀ R : LAlg R₀, G R → G R → Type u
  smul : ∀ {R : LAlg R₀} {x y : G R}, (R : Type u)ˣ → P R x y → P R x y
  one_smul : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), smul 1 u = u
  mul_smul : ∀ {R : LAlg R₀} {x y : G R} (l l' : (R : Type u)ˣ) (u : P R x y),
    smul (l * l') u = smul l (smul l' u)
  nonempty : ∀ (R : LAlg R₀) (x y : G R), Nonempty (P R x y)
  trans : ∀ {R : LAlg R₀} {x y : G R} (u w : P R x y), ∃! l : (R : Type u)ˣ, smul l u = w
  pmap : ∀ {R S : LAlg R₀} (f : LHom R S) {x y : G R}, P R x y → P S (map f x) (map f y)
  pmap_smul : ∀ {R S : LAlg R₀} (f : LHom R S) {x y : G R} (l : (R : Type u)ˣ) (u : P R x y),
    pmap f (smul l u) = smul (Units.map (f.1 : R →* S) l) (pmap f u)
  pmap_id : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), HEq (pmap (LHom.id R) u) u
  pmap_comp : ∀ {R S T : LAlg R₀} (f : LHom R S) (g : LHom S T) {x y : G R} (u : P R x y),
    HEq (pmap (g.comp f) u) (pmap g (pmap f u))
  add1 : ∀ {R : LAlg R₀} {x x' y : G R}, P R x y → P R x' y → P R (x + x') y
  add2 : ∀ {R : LAlg R₀} {x y y' : G R}, P R x y → P R x y' → P R x (y + y')
  zero1 : ∀ {R : LAlg R₀} (y : G R), P R 0 y
  zero2 : ∀ {R : LAlg R₀} (x : G R), P R x 0
  addFst_assoc : ∀ {R : LAlg R₀} {x x' x'' y : G R} (u : P R x y) (u' : P R x' y)
    (u'' : P R x'' y), HEq (add1 (add1 u u') u'') (add1 u (add1 u' u''))
  addSnd_assoc : ∀ {R : LAlg R₀} {x y y' y'' : G R} (u : P R x y) (u' : P R x y')
    (u'' : P R x y''), HEq (add2 (add2 u u') u'') (add2 u (add2 u' u''))
  addFst_comm : ∀ {R : LAlg R₀} {x x' y : G R} (u : P R x y) (u' : P R x' y),
    HEq (add1 u u') (add1 u' u)
  addSnd_comm : ∀ {R : LAlg R₀} {x y y' : G R} (u : P R x y) (u' : P R x y'),
    HEq (add2 u u') (add2 u' u)
  zeroFst_add : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), HEq (add1 (zero1 y) u) u
  zeroSnd_add : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), HEq (add2 (zero2 x) u) u
  addFst_smul : ∀ {R : LAlg R₀} {x x' y : G R} (l l' : (R : Type u)ˣ) (u : P R x y)
    (u' : P R x' y), add1 (smul l u) (smul l' u') = smul (l * l') (add1 u u')
  addSnd_smul : ∀ {R : LAlg R₀} {x y y' : G R} (l l' : (R : Type u)ˣ) (u : P R x y)
    (u' : P R x y'), add2 (smul l u) (smul l' u') = smul (l * l') (add2 u u')
  interchange : ∀ {R : LAlg R₀} {x x' y y' : G R} (u : P R x y) (u' : P R x' y)
    (w : P R x y') (w' : P R x' y'),
    add2 (add1 u u') (add1 w w') = add1 (add2 u w) (add2 u' w')
  addFst_nat : ∀ {R S : LAlg R₀} (f : LHom R S) {x x' y : G R} (u : P R x y) (u' : P R x' y),
    HEq (pmap f (add1 u u')) (add1 (pmap f u) (pmap f u'))
  addSnd_nat : ∀ {R S : LAlg R₀} (f : LHom R S) {x y y' : G R} (u : P R x y) (u' : P R x y'),
    HEq (pmap f (add2 u u')) (add2 (pmap f u) (pmap f u'))
  zeroFst_nat : ∀ {R S : LAlg R₀} (f : LHom R S) (y : G R),
    HEq (pmap f (zero1 y)) (zero1 (map f y))
  zeroSnd_nat : ∀ {R S : LAlg R₀} (f : LHom R S) (x : G R),
    HEq (pmap f (zero2 x)) (zero2 (map f x))
  sw : ∀ {R : LAlg R₀} {x y : G R}, P R x y → P R y x
  sw_smul : ∀ {R : LAlg R₀} {x y : G R} (l : (R : Type u)ˣ) (u : P R x y),
    sw (smul l u) = smul l (sw u)
  sw_nat : ∀ {R S : LAlg R₀} (f : LHom R S) {x y : G R} (u : P R x y),
    sw (pmap f u) = pmap f (sw u)
  swap_addFst : ∀ {R : LAlg R₀} {x x' y : G R} (u : P R x y) (u' : P R x' y),
    sw (add1 u u') = add2 (sw u) (sw u')
  sw_sw : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), sw (sw u) = u
  fibre_G : ∀ {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R)
    (f₂ : LHom R₂ R), IsFibreSq p₁ p₂ f₁ f₂ → CarriesFibre (map p₁) (map p₂) (map f₁) (map f₂)
  fibre_P : ∀ {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R)
    (f₂ : LHom R₂ R), IsFibreSq p₁ p₂ f₁ f₂ →
    CarriesFibre
      (fun t : (Σ x y : G F, P F x y) =>
        (⟨map p₁ t.1, map p₁ t.2.1, pmap p₁ t.2.2⟩ : Σ x y : G R₁, P R₁ x y))
      (fun t : (Σ x y : G F, P F x y) =>
        (⟨map p₂ t.1, map p₂ t.2.1, pmap p₂ t.2.2⟩ : Σ x y : G R₂, P R₂ x y))
      (fun t : (Σ x y : G R₁, P R₁ x y) =>
        (⟨map f₁ t.1, map f₁ t.2.1, pmap f₁ t.2.2⟩ : Σ x y : G R, P R x y))
      (fun t : (Σ x y : G R₂, P R₂ x y) =>
        (⟨map f₂ t.1, map f₂ t.2.1, pmap f₂ t.2.2⟩ : Σ x y : G R, P R x y))
attribute [instance] BX.grp BX.ggg BX.ggm BX.ggfree BX.ggfin
namespace BX
variable (B : BX R₀) {R : LAlg R₀}
def tr1 {x x' y : B.G R} (h : x = x') (u : B.P R x y) : B.P R x' y := h ▸ u
def tr2 {x y y' : B.G R} (h : y = y') (u : B.P R x y) : B.P R x y' := h ▸ u
def nsmul1 {x y : B.G R} (u : B.P R x y) : (n : ℕ) → B.P R (n • x) y
  | 0 => B.tr1 (zero_nsmul x).symm (B.zero1 y)
  | n + 1 => B.tr1 (succ_nsmul x n).symm (B.add1 (nsmul1 u n) u)
def nsmul2 {x y : B.G R} (u : B.P R x y) : (n : ℕ) → B.P R x (n • y)
  | 0 => B.tr2 (zero_nsmul y).symm (B.zero2 x)
  | n + 1 => B.tr2 (succ_nsmul y n).symm (B.add2 (nsmul2 u n) u)
def IsPairing (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ) : Prop :=
  ∃ (hx : N • x = 0) (hy : N • y = 0) (u : B.P R x y) (l₁ l₂ : (R : Type u)ˣ),
    B.tr1 hx (B.nsmul1 u N) = B.smul l₁ (B.zero1 y) ∧
      B.tr2 hy (B.nsmul2 u N) = B.smul l₂ (B.zero2 x) ∧ z = l₁ / l₂
end BX
end ReciprocityTheory.PGsh


