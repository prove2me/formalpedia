-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordOrientedFullKummer_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordOrientedFullKummer_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:27:20.789781+00:00
-- url     : https://prove2.me/theorems/00a17d8e-289b-4e8b-a473-203e08e9377e
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordOrientedFullKummer source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordOrientedFullKummer

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordOrientedFullKummer
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerKernelForward_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerNorm_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FullNormPairGaussian_p0

set_option autoImplicit false




/-!
# The oriented full N13 Mumford Kummer value

The raw norm pair `(u(θ), Res(u,v))` forgets the integer recording the two
points at infinity.  For an even sextic the missing coordinate is exactly

`(-1) ^ (n∞ - 1)`.

The shift by one is forced by the oriented Picard convention: the identity
Mumford datum has `n∞ = 1`, whereas the difference of the two infinity
points has `n∞ = 0`.  Thus the identity gives the trivial full class and the
infinity difference gives the unique possible sign class.

This file identifies that orientation bit before attempting to descend the
full value through principal relations.  No Cantor inverse, divisor
enumeration, or finite certificate is used.
-/

namespace MazurProof.N13MumfordOrientedFullKummer

noncomputable section

abbrev LowRep : Type :=
  N13LowDegreeKummerHom.LowRep

abbrev L : Type :=
  N13FullNormPair.L

/-- The exponent carried by the oriented infinity coordinate. -/
def orientationExponent (D : LowRep) : ℤ :=
  D.toSemi.nInf - 1

/-- The sign missing from the affine resultant norm root. -/
def orientationSignUnit (D : LowRep) : ℚˣ :=
  (-1 : ℚˣ) ^ orientationExponent D

@[simp] theorem orientationSignUnit_sq (D : LowRep) :
    orientationSignUnit D ^ 2 = 1 := by
  have heven :
      Even (orientationExponent D * (2 : ℤ)) :=
    ⟨orientationExponent D, by ring⟩
  rw [orientationSignUnit, ← zpow_natCast, ← zpow_mul]
  exact heven.neg_one_zpow

/-- The full norm pair with the infinity orientation retained. -/
def orientedMumfordNormPair (D : LowRep) :
    N13FullNormPair.NormPair :=
  ⟨(N13MumfordKummerValue.uThetaUnit
      (N13LowDegreeKummerHom.asMumford D),
    orientationSignUnit D *
      N13MumfordKummerNorm.normRootUnit D), by
    change
      N13FullNormPair.normUnits
          (N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D)) =
        (orientationSignUnit D *
          N13MumfordKummerNorm.normRootUnit D) ^ 2
    rw [mul_pow, orientationSignUnit_sq, one_mul]
    exact (N13MumfordKummerNorm.mumfordNormPair D).property⟩

@[simp] theorem orientedMumfordNormPair_fst (D : LowRep) :
    EvenSexticNormPair.fstHom N13FullNormPair.normUnits
        (orientedMumfordNormPair D) =
      N13MumfordKummerValue.uThetaUnit
        (N13LowDegreeKummerHom.asMumford D) :=
  rfl

@[simp] theorem orientedMumfordNormPair_snd (D : LowRep) :
    EvenSexticNormPair.sndHom N13FullNormPair.normUnits
        (orientedMumfordNormPair D) =
      orientationSignUnit D *
        N13MumfordKummerNorm.normRootUnit D :=
  rfl

/-- The corresponding class in the full even-sextic descent target. -/
def orientedMumfordFullClass (D : LowRep) :
    N13FullNormPair.FullTarget :=
  QuotientGroup.mk'
    (EvenSexticNormPair.fullGauge
      N13FullNormPair.normUnits
      N13FullNormPair.scalarUnits
      N13FullNormPair.normUnits_scalarUnits)
    (orientedMumfordNormPair D)

/-- Forgetting the orientation-sensitive norm root recovers the existing
fake Mumford value. -/
theorem forget_orientedMumfordFullClass (D : LowRep) :
    N13FullNormPair.forget (orientedMumfordFullClass D) =
      ((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) : Lˣ) :
        N13FullNormPair.FakeTarget) := by
  rfl

/-- Before quotienting, the oriented norm pair is the affine norm pair
multiplied by the sign pair to the oriented infinity exponent. -/
theorem orientedMumfordNormPair_eq_sign_zpow_mul
    (D : LowRep) :
    orientedMumfordNormPair D =
      (EvenSexticNormPair.signPair
          N13FullNormPair.normUnits (-1)
          N13FullNormPair.minusOne_sq) ^
          orientationExponent D *
        N13MumfordKummerNorm.mumfordNormPair D := by
  apply Subtype.ext
  apply Prod.ext
  · change
      N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) =
        (1 : Lˣ) ^ orientationExponent D *
          N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D)
    simp
  · change
      orientationSignUnit D *
          N13MumfordKummerNorm.normRootUnit D =
        (-1 : ℚˣ) ^ orientationExponent D *
          N13MumfordKummerNorm.normRootUnit D
    rfl

/-- After quotienting, changing the infinity orientation is precisely
multiplication by the distinguished sign class. -/
theorem orientedMumfordFullClass_eq_sign_zpow_mul
    (D : LowRep) :
    orientedMumfordFullClass D =
      N13FullNormPair.signClass ^ orientationExponent D *
        N13MumfordKummerNorm.mumfordFullClass D := by
  rw [orientedMumfordFullClass,
    orientedMumfordNormPair_eq_sign_zpow_mul]
  rw [map_mul, map_zpow]
  rfl

/-! ## The two oriented base classes -/

private theorem mumfordNormPair_eq_one_of_u_eq_one_v_eq_zero
    (D : LowRep)
    (hu : D.toSemi.u = 1)
    (hv : D.toSemi.v = 0) :
    N13MumfordKummerNorm.mumfordNormPair D = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    change
      N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D) = 1
    rw [N13MumfordKummerValue.uTheta_eq_mk]
    simp [N13LowDegreeKummerHom.asMumford_u, hu]
  · apply Units.ext
    change N13MumfordKummerNorm.normRoot D = 1
    simp [N13MumfordKummerNorm.normRoot, hu, hv]

private theorem mumfordFullClass_eq_one_of_u_eq_one_v_eq_zero
    (D : LowRep)
    (hu : D.toSemi.u = 1)
    (hv : D.toSemi.v = 0) :
    N13MumfordKummerNorm.mumfordFullClass D = 1 := by
  change
    QuotientGroup.mk'
        (EvenSexticNormPair.fullGauge
          N13FullNormPair.normUnits
          N13FullNormPair.scalarUnits
          N13FullNormPair.normUnits_scalarUnits)
        (N13MumfordKummerNorm.mumfordNormPair D) =
      1
  rw [mumfordNormPair_eq_one_of_u_eq_one_v_eq_zero D hu hv]
  exact map_one _

@[simp] theorem orientationExponent_zeroLow :
    orientationExponent N13LowDegreeKummerHom.zeroLow = 0 := by
  norm_num [orientationExponent, N13LowDegreeKummerHom.zeroLow,
    SexticMumford.zero]

@[simp] theorem orientedMumfordFullClass_zeroLow :
    orientedMumfordFullClass
        N13LowDegreeKummerHom.zeroLow = 1 := by
  rw [orientedMumfordFullClass_eq_sign_zpow_mul,
    orientationExponent_zeroLow, zpow_zero, one_mul]
  apply mumfordFullClass_eq_one_of_u_eq_one_v_eq_zero
  · rfl
  · rfl

@[simp] theorem orientationExponent_infinityMinusLow :
    orientationExponent
        N13MumfordKummerKernelForward.infinityMinusLow = -1 := by
  norm_num [orientationExponent,
    N13MumfordKummerKernelForward.infinityMinusLow,
    SexticMumford.infinityMinusMumford]

/-- The difference of the two infinity points is exactly the sign class in
the full norm-pair target. -/
@[simp] theorem orientedMumfordFullClass_infinityMinusLow :
    orientedMumfordFullClass
        N13MumfordKummerKernelForward.infinityMinusLow =
      N13FullNormPair.signClass := by
  apply congrArg
    (QuotientGroup.mk'
      (EvenSexticNormPair.fullGauge
        N13FullNormPair.normUnits
        N13FullNormPair.scalarUnits
        N13FullNormPair.normUnits_scalarUnits))
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    change
      N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford
            N13MumfordKummerKernelForward.infinityMinusLow) =
        1
    rw [N13MumfordKummerValue.uTheta_eq_mk]
    simp [N13LowDegreeKummerHom.asMumford_u,
      N13MumfordKummerKernelForward.infinityMinusLow,
      SexticMumford.infinityMinusMumford]
  · apply Units.ext
    change
      ((orientationSignUnit
          N13MumfordKummerKernelForward.infinityMinusLow *
        N13MumfordKummerNorm.normRootUnit
          N13MumfordKummerKernelForward.infinityMinusLow :
          ℚˣ) : ℚ) = -1
    norm_num [orientationSignUnit, orientationExponent,
      N13MumfordKummerNorm.normRootUnit,
      N13MumfordKummerNorm.normRoot,
      N13MumfordKummerKernelForward.infinityMinusLow,
      SexticMumford.infinityMinusMumford]

/-! ## The full lift of the actual structural Kummer map -/

abbrev G : Type :=
  N13LowDegreeKummerHom.G

abbrev infinityClass : G :=
  N13MumfordKummerKernelForward.infinityClass

/-- Use exactly the same chosen low-degree representative as the existing
fake Kummer homomorphism, but retain its oriented norm root.  No
well-definedness or additivity assertion is hidden in this definition. -/
def orientedFullKummer (P : G) :
    N13FullNormPair.FullTarget :=
  orientedMumfordFullClass
    (N13LowDegreeKummerHom.representative P)

/-- Forgetting the norm root is definitionally the actual structural fake
Kummer map. -/
theorem ofMul_forget_orientedFullKummer (P : G) :
    Additive.ofMul
        (N13FullNormPair.forget
          (orientedFullKummer P)) =
      N13LowDegreeKummerHom.mumfordKummer P := by
  rfl

/-- Multiplicative form of the compatibility with the existing additive
fake-Kummer homomorphism. -/
theorem forget_orientedFullKummer (P : G) :
    N13FullNormPair.forget (orientedFullKummer P) =
      Additive.toMul
        (N13LowDegreeKummerHom.mumfordKummer P) := by
  exact congrArg Additive.toMul
    (ofMul_forget_orientedFullKummer P)

/-- Injectivity of the N13 forgetful map makes the chosen full lift send
the identity to the identity. -/
@[simp] theorem orientedFullKummer_zero :
    orientedFullKummer (0 : G) = 1 := by
  apply N13FullNormPairGaussian.forget_injective
  rw [forget_orientedFullKummer, map_one]
  exact congrArg Additive.toMul
    (map_zero N13LowDegreeKummerHom.mumfordKummer)

/-- The same injectivity upgrades additivity of the fake value to genuine
multiplicativity of the oriented full value. -/
theorem orientedFullKummer_add (P Q : G) :
    orientedFullKummer (P + Q) =
      orientedFullKummer P * orientedFullKummer Q := by
  apply N13FullNormPairGaussian.forget_injective
  rw [forget_orientedFullKummer, map_mul,
    forget_orientedFullKummer, forget_orientedFullKummer,
    map_add]
  rfl

/-- The N13 oriented norm pair therefore descends to a genuine homomorphism,
without choosing compatible Mumford representatives. -/
def fullKummer :
    G →+ Additive N13FullNormPair.FullTarget where
  toFun P := Additive.ofMul (orientedFullKummer P)
  map_zero' := by
    change orientedFullKummer (0 : G) = 1
    exact orientedFullKummer_zero
  map_add' P Q := by
    change
      orientedFullKummer (P + Q) =
        orientedFullKummer P * orientedFullKummer Q
    exact orientedFullKummer_add P Q

@[simp] theorem fullKummer_apply (P : G) :
    fullKummer P =
      Additive.ofMul (orientedFullKummer P) :=
  rfl

/-- The full target has exponent two, so the genuine full Kummer
homomorphism kills every double. -/
@[simp] theorem orientedFullKummer_two_nsmul (Q : G) :
    orientedFullKummer (2 • Q) = 1 := by
  rw [two_nsmul, orientedFullKummer_add]
  simpa only [pow_two] using
    N13FullNormPair.fullTarget_sq_eq_one
      (orientedFullKummer Q)

@[simp] theorem fullKummer_two_nsmul (Q : G) :
    fullKummer (2 • Q) = 0 := by
  change
    Additive.ofMul (orientedFullKummer (2 • Q)) =
      Additive.ofMul 1
  rw [orientedFullKummer_two_nsmul]

/-- The explicit N13 half of the infinity difference also explains its
trivial full Kummer value, now as a formal consequence of homomorphy rather
than a separate representative computation. -/
@[simp] theorem orientedFullKummer_infinityClass :
    orientedFullKummer infinityClass = 1 := by
  change
    orientedFullKummer
        N13KummerKernelAssembly.infinityClass = 1
  rw [← N13KummerKernelAssembly.two_nsmul_infinityHalfClass]
  exact
    orientedFullKummer_two_nsmul
      N13KummerKernelAssembly.infinityHalfClass

/-- The fake kernel has only the two full norm-pair fibres: the identity
and the distinguished sign class.  This is unconditional target algebra;
the geometric principal-genus theorem must identify the two fibres with
the double and infinity-shifted-double branches. -/
theorem structuralKummer_eq_zero_iff_full_eq_one_or_sign
    (P : G) :
    N13LowDegreeKummerHom.mumfordKummer P = 0 ↔
      orientedFullKummer P = 1 ∨
        orientedFullKummer P =
          N13FullNormPair.signClass := by
  rw [← ofMul_forget_orientedFullKummer]
  change
    N13FullNormPair.forget (orientedFullKummer P) = 1 ↔
      orientedFullKummer P = 1 ∨
        orientedFullKummer P =
          N13FullNormPair.signClass
  exact N13FullNormPair.forget_eq_one_iff
    (orientedFullKummer P)

/-- In the N13 sextic field the Gaussian unit makes the sign class
gauge-trivial.  Hence the fake kernel is a single full-target fibre. -/
theorem structuralKummer_eq_zero_iff_full_eq_one
    (P : G) :
    N13LowDegreeKummerHom.mumfordKummer P = 0 ↔
      orientedFullKummer P = 1 := by
  constructor
  · intro hP
    rcases
        (structuralKummer_eq_zero_iff_full_eq_one_or_sign P).mp hP with
      hone | hsign
    · exact hone
    · exact hsign.trans
        N13FullNormPairGaussian.signClass_eq_one
  · intro hone
    exact
      (structuralKummer_eq_zero_iff_full_eq_one_or_sign P).mpr
        (Or.inl hone)

/-- Once the two full fibres receive their geometric interpretations, the
standard even-sextic kernel theorem follows.  Its reverse implication is
already the compiled forward Kummer theorem. -/
theorem kernel_double_or_infinity_of_full_fibers
    (one_fiber :
      ∀ P : G, orientedFullKummer P = 1 →
        ∃ Q : G, P = 2 • Q)
    (sign_fiber :
      ∀ P : G,
        orientedFullKummer P =
            N13FullNormPair.signClass →
        ∃ Q : G, P = 2 • Q + infinityClass) :
    ∀ P : G,
      N13LowDegreeKummerHom.mumfordKummer P = 0 ↔
        (∃ Q : G, P = 2 • Q) ∨
        (∃ Q : G,
          P = 2 • Q + infinityClass) := by
  intro P
  constructor
  · intro hP
    rcases
        (structuralKummer_eq_zero_iff_full_eq_one_or_sign P).mp hP with
      hone | hsign
    · exact Or.inl (one_fiber P hone)
    · exact Or.inr (sign_fiber P hsign)
  · rintro (⟨Q, rfl⟩ | ⟨Q, rfl⟩)
    · exact
        N13MumfordKummerKernelForward.structuralKummer_two_nsmul Q
    · exact
        N13MumfordKummerKernelForward.structuralKummer_two_nsmul_add_infinityClass
          Q

/-- For N13 the Gaussian sign collapse removes the second geometric
fibre altogether.  A half theorem for the identity fibre alone gives the
exact kernel of doubling. -/
theorem kernel_eq_doubles_of_full_identity_fiber
    (one_fiber :
      ∀ P : G, orientedFullKummer P = 1 →
        ∃ Q : G, P = 2 • Q) :
    ∀ P : G,
      N13LowDegreeKummerHom.mumfordKummer P = 0 ↔
        ∃ Q : G, P = 2 • Q := by
  intro P
  constructor
  · intro hP
    exact one_fiber P
      ((structuralKummer_eq_zero_iff_full_eq_one P).mp hP)
  · rintro ⟨Q, rfl⟩
    exact
      N13MumfordKummerKernelForward.structuralKummer_two_nsmul Q

end

end MazurProof.N13MumfordOrientedFullKummer


