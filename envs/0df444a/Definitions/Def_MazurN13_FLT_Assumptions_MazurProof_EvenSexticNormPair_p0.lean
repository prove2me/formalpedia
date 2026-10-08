-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_EvenSexticNormPair_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_EvenSexticNormPair_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:48:16.166128+00:00
-- url     : https://prove2.me/theorems/d98f3548-d9d4-4565-bed8-d429db9eef51
-- title:
--   FLT.Assumptions.MazurProof.EvenSexticNormPair source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.EvenSexticNormPair

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.EvenSexticNormPair
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_FakeSquareClass_p0

set_option autoImplicit false




/-!
# Full norm-pair and fake targets for an even sextic

For an even sextic, the full two-descent target remembers a pair
`(α,s)` satisfying `N(α)=s²`.  It is quotiented by

* `(β²,N(β))`, and
* `(q,q³)` for ground-field scalars.

Forgetting the second coordinate gives the usual fake square-class target.
This file develops that target algebra for abstract commutative groups.  The
only sextic-specific input is that the norm of a scalar is its sixth power.
No Picard group or Kummer exactness theorem is used here.
-/

namespace MazurProof.EvenSexticNormPair

noncomputable section

variable {A B : Type*} [CommGroup A] [CommGroup B]

/-- Pairs `(α,s)` satisfying the norm-square equation. -/
def normPairSubgroup (N : A →* B) : Subgroup (A × B) where
  carrier := {p | N p.1 = p.2 ^ 2}
  one_mem' := by
    change N 1 = (1 : B) ^ 2
    simp
  mul_mem' := by
    rintro ⟨a, s⟩ ⟨b, t⟩ ha hb
    change N (a * b) = (s * t) ^ 2
    rw [map_mul, ha, hb, mul_pow]
  inv_mem' := by
    rintro ⟨a, s⟩ ha
    change N a⁻¹ = s⁻¹ ^ 2
    rw [map_inv, ha, inv_pow]

abbrev NormPair (N : A →* B) :=
  ↥(normPairSubgroup N)

/-- Projection of a norm pair to its first coordinate. -/
def fstHom (N : A →* B) : NormPair N →* A :=
  (MonoidHom.fst A B).comp (normPairSubgroup N).subtype

@[simp] theorem fstHom_apply (N : A →* B) (p : NormPair N) :
    fstHom N p = p.1.1 :=
  rfl

/-- Projection of a norm pair to its chosen norm root. -/
def sndHom (N : A →* B) : NormPair N →* B :=
  (MonoidHom.snd A B).comp (normPairSubgroup N).subtype

@[simp] theorem sndHom_apply (N : A →* B) (p : NormPair N) :
    sndHom N p = p.1.2 :=
  rfl

@[simp] theorem norm_fst_eq_snd_sq (N : A →* B) (p : NormPair N) :
    N (fstHom N p) = sndHom N p ^ 2 :=
  p.2

/-- The square/norm gauge element `(β²,N(β))`. -/
def chi (N : A →* B) : A →* NormPair N where
  toFun β :=
    ⟨(β ^ 2, N β), by
      change N (β ^ 2) = (N β) ^ 2
      rw [map_pow]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' β γ := by
    apply Subtype.ext
    ext <;> simp [mul_pow]

@[simp] theorem chi_fst (N : A →* B) (β : A) :
    fstHom N (chi N β) = β ^ 2 :=
  rfl

@[simp] theorem chi_snd (N : A →* B) (β : A) :
    (chi N β : A × B).2 = N β :=
  rfl

/-- The scalar gauge element `(q,q³)`.  The hypothesis is the degree-six
norm formula for scalars. -/
def iota (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :
    B →* NormPair N where
  toFun q :=
    ⟨(e q, q ^ 3), by
      change N (e q) = (q ^ 3) ^ 2
      rw [norm_scalar]
      group⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' q r := by
    apply Subtype.ext
    ext <;> simp [mul_pow]

@[simp] theorem iota_fst
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (q : B) :
    fstHom N (iota N e norm_scalar q) = e q :=
  rfl

@[simp] theorem iota_snd
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (q : B) :
    (iota N e norm_scalar q : A × B).2 = q ^ 3 :=
  rfl

/-- Squares and scalars in the first-coordinate fake target. -/
def fakeGauge (e : B →* A) : Subgroup A :=
  Subgroup.square A ⊔ (⊤ : Subgroup B).map e

/-- Membership in the fake gauge has the expected square-times-scalar
normal form.  This is subgroup plumbing, not an arithmetic input. -/
theorem mem_fakeGauge_iff_exists (e : B →* A) (a : A) :
    a ∈ fakeGauge e ↔
      ∃ β : A, ∃ q : B, a = β ^ 2 * e q := by
  constructor
  · intro ha
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      (Subgroup.mem_sup.mp ha)
    obtain ⟨β, hβ⟩ := Subgroup.mem_square.mp hx
    obtain ⟨q, -, hq⟩ := hy
    refine ⟨β, q, ?_⟩
    rw [← hxy, ← hq, hβ, pow_two]
  · rintro ⟨β, q, rfl⟩
    apply Subgroup.mul_mem_sup
    · exact Subgroup.mem_square.mpr ⟨β, by simp [pow_two]⟩
    · exact Subgroup.mem_map_of_mem e trivial

abbrev FakeTarget (e : B →* A) :=
  A ⧸ fakeGauge e

/-- The two gauge families in the full norm-pair target. -/
def fullGauge
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :
    Subgroup (NormPair N) :=
  (chi N).range ⊔ (iota N e norm_scalar).range

abbrev FullTarget
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :=
  NormPair N ⧸ fullGauge N e norm_scalar

/-- Forget the norm-root coordinate before quotienting the full target. -/
def forgetRaw (N : A →* B) (e : B →* A) :
    NormPair N →* FakeTarget e :=
  (QuotientGroup.mk' (fakeGauge e)).comp (fstHom N)

@[simp] theorem forgetRaw_apply
    (N : A →* B) (e : B →* A) (p : NormPair N) :
    forgetRaw N e p =
      QuotientGroup.mk' (fakeGauge e) p.1.1 :=
  rfl

theorem fullGauge_le_forgetRaw_ker
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :
    fullGauge N e norm_scalar ≤ (forgetRaw N e).ker := by
  rw [fullGauge, sup_le_iff]
  constructor
  · rintro _ ⟨β, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    apply Subgroup.mem_sup_left
    change β ^ 2 ∈ Subgroup.square A
    exact Subgroup.mem_square.mpr ⟨β, by simp [pow_two]⟩
  · rintro _ ⟨q, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    apply Subgroup.mem_sup_right
    exact Subgroup.mem_map_of_mem e trivial

/-- Forgetting the second coordinate descends from the full target to the
fake target. -/
def forget
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6) :
    FullTarget N e norm_scalar →* FakeTarget e :=
  QuotientGroup.lift
    (fullGauge N e norm_scalar)
    (forgetRaw N e)
    (fullGauge_le_forgetRaw_ker N e norm_scalar)

@[simp] theorem forget_mk
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) :
    forget N e norm_scalar
        (QuotientGroup.mk' (fullGauge N e norm_scalar) p) =
      QuotientGroup.mk' (fakeGauge e) p.1.1 :=
  rfl

/-- A norm pair with first coordinate one and square-one second coordinate.
Over the rational units there are only the choices `+1` and `-1`. -/
def signPair (N : A →* B) (ε : B) (hε : ε ^ 2 = 1) :
    NormPair N :=
  ⟨(1, ε), by
    change N 1 = ε ^ 2
    simpa using hε.symm⟩

@[simp] theorem forget_signPair
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (ε : B) (hε : ε ^ 2 = 1) :
    forget N e norm_scalar
        (QuotientGroup.mk' (fullGauge N e norm_scalar)
          (signPair N ε hε)) = 1 := by
  rw [forget_mk]
  exact map_one _

/-! ## The kernel of forgetting the norm root -/

/-- Remove a square gauge and a scalar gauge from a norm pair. -/
def normalize
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) (β : A) (q : B) :
    NormPair N :=
  p / (chi N β * iota N e norm_scalar q)

theorem fstHom_normalize_eq_one
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) (β : A) (q : B)
    (hp : fstHom N p = β ^ 2 * e q) :
    fstHom N (normalize N e norm_scalar p β q) = 1 := by
  change fstHom N p / (β ^ 2 * e q) = 1
  rw [hp]
  simp

theorem fullClass_normalize
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) (β : A) (q : B) :
    QuotientGroup.mk' (fullGauge N e norm_scalar) p =
      QuotientGroup.mk' (fullGauge N e norm_scalar)
        (normalize N e norm_scalar p β q) := by
  let g : NormPair N := chi N β * iota N e norm_scalar q
  have hg : g ∈ fullGauge N e norm_scalar := by
    apply Subgroup.mul_mem_sup
    · exact ⟨β, rfl⟩
    · exact ⟨q, rfl⟩
  have hgclass :
      QuotientGroup.mk' (fullGauge N e norm_scalar) g = 1 :=
    (QuotientGroup.eq_one_iff g).2 hg
  have hp : p = normalize N e norm_scalar p β q * g := by
    simp [normalize, g]
  calc
    QuotientGroup.mk' (fullGauge N e norm_scalar) p =
        QuotientGroup.mk' (fullGauge N e norm_scalar)
          (normalize N e norm_scalar p β q * g) := by
      exact congrArg
        (QuotientGroup.mk' (fullGauge N e norm_scalar)) hp
    _ = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (normalize N e norm_scalar p β q) *
        QuotientGroup.mk' (fullGauge N e norm_scalar) g := by
      rw [map_mul]
    _ = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (normalize N e norm_scalar p β q) := by
      rw [hgclass, mul_one]

theorem sndHom_normalize_sq_eq_one
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (p : NormPair N) (β : A) (q : B)
    (hp : fstHom N p = β ^ 2 * e q) :
    sndHom N (normalize N e norm_scalar p β q) ^ 2 = 1 := by
  have hnorm :=
    norm_fst_eq_snd_sq N
      (normalize N e norm_scalar p β q)
  rw [fstHom_normalize_eq_one N e norm_scalar p β q hp] at hnorm
  simpa using hnorm.symm

/-- The fibre of the full target over the trivial fake class consists of
classes represented by `(1, ε)` with `ε²=1`. -/
theorem forget_eq_one_iff_exists_signPair
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (z : FullTarget N e norm_scalar) :
    forget N e norm_scalar z = 1 ↔
      ∃ ε : B, ∃ hε : ε ^ 2 = 1,
        z = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (signPair N ε hε) := by
  constructor
  · intro hz
    obtain ⟨p, rfl⟩ :=
      QuotientGroup.mk'_surjective
        (fullGauge N e norm_scalar) z
    have hfake :
        QuotientGroup.mk' (fakeGauge e) (fstHom N p) = 1 := by
      change QuotientGroup.mk' (fakeGauge e) p.1.1 = 1
      simpa only [forget_mk] using hz
    have hmem : fstHom N p ∈ fakeGauge e :=
      (QuotientGroup.eq_one_iff (fstHom N p)).1 hfake
    obtain ⟨β, q, hp⟩ :=
      (mem_fakeGauge_iff_exists e (fstHom N p)).1 hmem
    let r : NormPair N := normalize N e norm_scalar p β q
    have hrfst : fstHom N r = 1 :=
      fstHom_normalize_eq_one N e norm_scalar p β q hp
    have hrsq : sndHom N r ^ 2 = 1 :=
      sndHom_normalize_sq_eq_one N e norm_scalar p β q hp
    have hr :
        r = signPair N (sndHom N r) hrsq := by
      apply Subtype.ext
      apply Prod.ext
      · exact hrfst
      · rfl
    refine ⟨sndHom N r, hrsq, ?_⟩
    calc
      QuotientGroup.mk' (fullGauge N e norm_scalar) p =
          QuotientGroup.mk' (fullGauge N e norm_scalar) r :=
        fullClass_normalize N e norm_scalar p β q
      _ = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (signPair N (sndHom N r) hrsq) :=
        congrArg
          (QuotientGroup.mk' (fullGauge N e norm_scalar)) hr
  · rintro ⟨ε, hε, rfl⟩
    exact forget_signPair N e norm_scalar ε hε

/-- If the base group has only two square roots of one, the forgetting
kernel has at most the identity and one sign class. -/
theorem forget_eq_one_iff_eq_one_or_eq_sign
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (σ : B) (hσ : σ ^ 2 = 1)
    (sqOne : ∀ ε : B, ε ^ 2 = 1 → ε = 1 ∨ ε = σ)
    (z : FullTarget N e norm_scalar) :
    forget N e norm_scalar z = 1 ↔
      z = 1 ∨
        z = QuotientGroup.mk' (fullGauge N e norm_scalar)
          (signPair N σ hσ) := by
  constructor
  · intro hz
    obtain ⟨ε, hε, hzε⟩ :=
      (forget_eq_one_iff_exists_signPair N e norm_scalar z).1 hz
    rcases sqOne ε hε with rfl | rfl
    · left
      rw [hzε]
      have hraw : signPair N 1 hε = 1 := by
        apply Subtype.ext
        ext <;> simp [signPair]
      rw [hraw]
      exact map_one _
    · exact Or.inr hzε
  · rintro (rfl | rfl)
    · exact map_one _
    · exact forget_signPair N e norm_scalar σ hσ

/-- Every class in the full norm-pair target has exponent two. -/
@[simp] theorem fullTarget_sq_eq_one
    (N : A →* B) (e : B →* A)
    (norm_scalar : ∀ q : B, N (e q) = q ^ 6)
    (z : FullTarget N e norm_scalar) :
    z ^ 2 = 1 := by
  obtain ⟨p, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (fullGauge N e norm_scalar) z
  have hp : p ^ 2 = chi N (fstHom N p) := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simpa [pow_two] using (norm_fst_eq_snd_sq N p).symm
  change QuotientGroup.mk' (fullGauge N e norm_scalar) (p ^ 2) = 1
  rw [hp]
  apply (QuotientGroup.eq_one_iff _).2
  apply Subgroup.mem_sup_left
  exact ⟨fstHom N p, rfl⟩

end

end MazurProof.EvenSexticNormPair


