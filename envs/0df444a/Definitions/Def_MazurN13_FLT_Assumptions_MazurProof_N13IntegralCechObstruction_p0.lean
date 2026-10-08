-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralCechObstruction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralCechObstruction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:33:33.102796+00:00
-- url     : https://prove2.me/theorems/0902bdff-0306-4d25-b10f-e3c3b48a4e39
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralCechObstruction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralCechObstruction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralCechObstruction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CechLaurentCore_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CechNakayama_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialCechObstruction_p0
import Mathlib.NumberTheory.Padics.RingHoms

set_option autoImplicit false




/-!
# The integral N13 Čech obstruction at two

The Laurent two-chart quotient is ring-generic, so over `ℤ₂` it is already
the free rank-two module with basis `v t⁻², v t⁻¹`.  The integral base
divisor is `(0,0)+(-1,0)`.  Expanding its two simple principal parts at
infinity gives the columns

`(1,0), (1,-1)`.

Thus the integral connecting matrix has determinant `-1`.  Its reduction
modulo two is exactly the special-fibre matrix with columns `(1,0),(1,1)`.
This supplies the finite bounded-pole integral complex to which the general
Čech--Nakayama correction applies.
-/

namespace MazurProof.N13IntegralCechObstruction

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

abbrev K : Type :=
  N13GoodModelTwo.F2

/-- The infinity-chart conjugate numerator over the two-adic integers. -/
def conjugateNumerator (t v : R₂) : R₂ :=
  v + (1 + t ^ 2 + t ^ 3)

/-- The principal part at `(0,0)`. -/
theorem zeroPrincipal_transition (t v : R₂) :
    conjugateNumerator t v =
      (v + 1) + t ^ 2 * (1 + t) := by
  simp only [conjugateNumerator]
  ring

/-- The principal part at `(-1,0)`.  Division by `1+t` has Taylor
coefficients `1,-1` at `t=0`; the last summand is regular after inverting
`1+t`. -/
theorem negOnePrincipal_transition (t v : R₂) :
    conjugateNumerator t v =
      (1 + t) * (1 - t) * (v + 1) +
        t ^ 2 * (v + 2 + t) := by
  simp only [conjugateNumerator]
  ring

abbrev Obstruction : Type :=
  N13CechLaurentCore.Obstruction (R := R₂)

abbrev PrincipalParts : Type :=
  Fin 2 → R₂

abbrev StructureCechH1 : Type :=
  N13CechLaurentCore.StructureCechH1 (R := R₂)

/-- Integral principal-part connecting map. -/
def connectingMap :
    PrincipalParts →ₗ[R₂] Obstruction where
  toFun a := ![a 0 + a 1, -a 1]
  map_add' a b := by
    funext i
    fin_cases i <;>
      simp [add_assoc, add_left_comm, add_comm]
  map_smul' c a := by
    funext i
    fin_cases i <;> simp [mul_add]

def connectingMatrix :
    Matrix (Fin 2) (Fin 2) R₂ :=
  !![1, 1; 0, -1]

@[simp] theorem connectingMatrix_det :
    connectingMatrix.det = -1 := by
  rw [Matrix.det_fin_two]
  simp [connectingMatrix]

theorem connectingMatrix_det_isUnit :
    IsUnit connectingMatrix.det := by
  rw [connectingMatrix_det]
  exact IsUnit.neg isUnit_one

/-- The integral connecting map is an equivalence. -/
def connectingEquiv :
    PrincipalParts ≃ₗ[R₂] Obstruction where
  toFun := connectingMap
  invFun b := ![b 0 + b 1, -b 1]
  left_inv a := by
    funext i
    fin_cases i <;> simp [connectingMap]
  right_inv b := by
    funext i
    fin_cases i <;> simp [connectingMap]
  map_add' := connectingMap.map_add
  map_smul' := connectingMap.map_smul

theorem connectingMap_surjective :
    Function.Surjective connectingMap :=
  connectingEquiv.surjective

theorem connectingMap_range_eq_top :
    LinearMap.range connectingMap = ⊤ :=
  LinearMap.range_eq_top.mpr connectingMap_surjective

/-- The ring-generic Laurent decomposition identifies integral
structure-sheaf Čech cohomology with the two obstruction coefficients. -/
abbrev structureCechH1Equiv :
    StructureCechH1 ≃ₗ[R₂] Obstruction :=
  N13CechLaurentCore.structureCechH1Equiv

/-- Integral principal parts mapped to the actual Laurent Čech quotient. -/
def principalToStructureCechH1 :
    PrincipalParts →ₗ[R₂] StructureCechH1 :=
  structureCechH1Equiv.symm.toLinearMap.comp connectingMap

def principalToStructureCechH1Equiv :
    PrincipalParts ≃ₗ[R₂] StructureCechH1 :=
  connectingEquiv.trans structureCechH1Equiv.symm

theorem principalToStructureCechH1_surjective :
    Function.Surjective principalToStructureCechH1 :=
  principalToStructureCechH1Equiv.surjective

theorem principalToStructureCechH1_range_eq_top :
    LinearMap.range principalToStructureCechH1 = ⊤ :=
  LinearMap.range_eq_top.mpr
    principalToStructureCechH1_surjective

/-- Integral additive `H¹` after twisting by the base divisor. -/
abbrev TwistedCechH1 : Type :=
  StructureCechH1 ⧸
    LinearMap.range principalToStructureCechH1

noncomputable instance twistedCechH1_subsingleton :
    Subsingleton TwistedCechH1 := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  exact principalToStructureCechH1_range_eq_top

theorem twistedCechH1_eq_zero
    (z : TwistedCechH1) :
    z = 0 :=
  Subsingleton.elim _ _

/-! ## Compatibility with the special fibre -/

/-- Pointwise reduction of the finite principal-part and obstruction
modules. -/
def reduceCoefficients
    (a : Fin 2 → R₂) :
    Fin 2 → K :=
  fun i => PadicInt.toZMod (a i)

@[simp] theorem reduceCoefficients_zero (a : Fin 2 → R₂) :
    reduceCoefficients a 0 =
      PadicInt.toZMod (a 0) := rfl

@[simp] theorem reduceCoefficients_one (a : Fin 2 → R₂) :
    reduceCoefficients a 1 =
      PadicInt.toZMod (a 1) := rfl

/-- The integral connecting map reduces to the actual special-fibre
connecting map. -/
theorem reduce_connectingMap
    (a : PrincipalParts) :
    reduceCoefficients (connectingMap a) =
      N13SpecialCechObstruction.connectingMap
        (reduceCoefficients a) := by
  funext i
  fin_cases i
  · simp [reduceCoefficients, connectingMap,
      N13SpecialCechObstruction.connectingMap]
  · simp [reduceCoefficients, connectingMap,
      N13SpecialCechObstruction.connectingMap,
      ZMod.neg_eq_self_mod_two]

/-! ## Nakayama lifting from the computed special complex -/

local notation "𝔪" =>
  IsLocalRing.maximalIdeal R₂

/-- Coefficientwise lift of an `𝔽₂` vector to `ℤ₂`. -/
def liftCoefficients
    (a : Fin 2 → K) :
    Fin 2 → R₂ :=
  fun i => (a i).val

@[simp] theorem reduce_liftCoefficients
    (a : Fin 2 → K) :
    reduceCoefficients (liftCoefficients a) = a := by
  funext i
  change
    PadicInt.toZMod ((a i).val : R₂) = a i
  rw [map_natCast]
  exact ZMod.natCast_zmod_val (a i)

/-- A two-vector reduces to zero exactly where needed for membership in the
maximal-ideal multiple of the free obstruction module. -/
theorem vector_mem_maximal_smul_top_of_reduce_eq_zero
    (z : Fin 2 → R₂)
    (hz : reduceCoefficients z = 0) :
    z ∈ 𝔪 • (⊤ : Submodule R₂ (Fin 2 → R₂)) := by
  have hz0 : z 0 ∈ 𝔪 := by
    rw [← PadicInt.ker_toZMod]
    apply RingHom.mem_ker.mpr
    simpa [reduceCoefficients] using congrFun hz 0
  have hz1 : z 1 ∈ 𝔪 := by
    rw [← PadicInt.ker_toZMod]
    apply RingHom.mem_ker.mpr
    simpa [reduceCoefficients] using congrFun hz 1
  let e0 : Fin 2 → R₂ := ![1, 0]
  let e1 : Fin 2 → R₂ := ![0, 1]
  have h0 :
      z 0 • e0 ∈
        𝔪 • (⊤ : Submodule R₂ (Fin 2 → R₂)) :=
    Submodule.smul_mem_smul hz0 Submodule.mem_top
  have h1 :
      z 1 • e1 ∈
        𝔪 • (⊤ : Submodule R₂ (Fin 2 → R₂)) :=
    Submodule.smul_mem_smul hz1 Submodule.mem_top
  have hdecomp :
      z = z 0 • e0 + z 1 • e1 := by
    funext i
    fin_cases i <;> simp [e0, e1]
  rw [hdecomp]
  exact Submodule.add_mem _ h0 h1

/-- A finite integral Čech coboundary has the computed N13 special fibre. -/
def ResidueCompatible
    (d : PrincipalParts →ₗ[R₂] Obstruction) : Prop :=
  ∀ a,
    reduceCoefficients (d a) =
      N13SpecialCechObstruction.connectingMap
        (reduceCoefficients a)

theorem connectingMap_residueCompatible :
    ResidueCompatible connectingMap :=
  reduce_connectingMap

/-- Compatibility with the computed special connecting map supplies the
exact quotient-range hypothesis in the Čech--Nakayama theorem. -/
theorem residue_range_eq_top
    (d : PrincipalParts →ₗ[R₂] Obstruction)
    (hd : ResidueCompatible d) :
    (LinearMap.range d).map
        (Submodule.mkQ
          (𝔪 • (⊤ : Submodule R₂ Obstruction))) = ⊤ := by
  rw [Submodule.map_mkQ_eq_top]
  apply top_unique
  intro y hy
  obtain ⟨aBar, haBar⟩ :=
    N13SpecialCechObstruction.connectingMap_surjective
      (reduceCoefficients y)
  let x : PrincipalParts :=
    liftCoefficients aBar
  have hxred :
      reduceCoefficients x = aBar :=
    reduce_liftCoefficients aBar
  have hdx :
      reduceCoefficients (d x) =
        reduceCoefficients y := by
    calc
      reduceCoefficients (d x) =
          N13SpecialCechObstruction.connectingMap
            (reduceCoefficients x) := hd x
      _ =
          N13SpecialCechObstruction.connectingMap
            aBar := by rw [hxred]
      _ = reduceCoefficients y := haBar
  have hdiffred :
      reduceCoefficients (y - d x) = 0 := by
    funext i
    have hi := congrFun hdx i
    simp only [reduceCoefficients, Pi.zero_apply,
      Pi.sub_apply, map_sub]
    exact sub_eq_zero.mpr hi.symm
  have hdiff :
      y - d x ∈
        𝔪 • (⊤ : Submodule R₂ Obstruction) :=
    vector_mem_maximal_smul_top_of_reduce_eq_zero
      (y - d x) hdiffred
  have hrange :
      d x ∈ LinearMap.range d :=
    LinearMap.mem_range_self d x
  have hsum :
      (y - d x) + d x = y := by
    abel
  rw [← hsum]
  exact Submodule.add_mem_sup hdiff hrange

/-- Any finite two-adic Čech coboundary with the computed special fibre is
surjective. -/
theorem surjective_of_residueCompatible
    (d : PrincipalParts →ₗ[R₂] Obstruction)
    (hd : ResidueCompatible d) :
    Function.Surjective d :=
  N13CechNakayama.surjective_of_residue_range_eq_top
    d (residue_range_eq_top d hd)

/-- The corresponding cocycle correction: a cochain closed modulo two can
be corrected, without changing its reduction, to an actual cocycle. -/
theorem exists_kernel_lift_of_residueCompatible
    (d : PrincipalParts →ₗ[R₂] Obstruction)
    (hd : ResidueCompatible d)
    (x : PrincipalParts)
    (hx :
      d x ∈
        𝔪 • (⊤ : Submodule R₂ Obstruction)) :
    ∃ z : PrincipalParts,
      d z = 0 ∧
        x - z ∈
          𝔪 • (⊤ : Submodule R₂ PrincipalParts) :=
  N13CechNakayama.exists_kernel_lift_of_residue_range_eq_top
    d (residue_range_eq_top d hd) x hx

end

end MazurProof.N13IntegralCechObstruction


