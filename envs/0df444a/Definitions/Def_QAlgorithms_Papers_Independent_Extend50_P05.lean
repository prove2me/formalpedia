-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P05
-- name    : QAlgorithms_Papers_Independent_Extend50_P05
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T13:18:33.68346+00:00
-- url     : https://prove2.me/theorems/dcccdf58-a80f-497c-b035-f1743d4ffb60
-- title:
--   Definitions for A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region
-- statement:
--   The objects the formalized statements of *A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region* (arXiv:2106.09655) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CloningOutputs`: PDF pp.3–4: N ordered qudit output registers.
--   - `CloningChoiBasis`: PDF p.5: input-first computational basis for an unnormalized Choi matrix.
--   - `outputTrace`: PDF p.3: ordinary, unnormalized partial trace onto output register i.
--   - `cloningMarginal`: PDF p.3: the i-th marginal map, on all input operators.
--   - `depolarizingShrink`: PDF pp.2,6: D_p(X)=pX+(1-p)Tr(X)I/d; p is not constrained to be positive.
--   - `cloningTwirl`: PDF p.4, Definition 3: explicit normalized-Haar twirl of the actual joint map.
--   - `physicalPermutation`: PDF p.5: V(pi)(v_0 tensor ... tensor v_N) has factor pi^{-1}(j) at j.
--   - `pureInputFidelity`: PDF p.3: squared pure-input fidelity, <psi|E(|psi><psi|)|psi>.
--   - `worstMarginal`: PDF p.4: the infimum is taken over normalized pure inputs.
--   - `worstObjective`: PDF p.4: sum of separately minimized marginal fidelities; weights need not sum to one.
--   - `averageObjective`: PDF p.4: Haar average of each marginal's pure-input fidelity.
--   - `worstOptimum`: PDF pp.3–4, Definition 2: optimize over all complex-linear CPTP joint maps.
--   - `averageOptimum`: PDF pp.3–4, Definition 2: the average optimum over the same full set of channels.
--   - `CloningAchievable`: PDF pp.2,10,12: physical attainability of the two depolarizing marginal maps.
--   - `CloningFidelityAchievable`: PDF pp.2,6: the corresponding constant squared pure-input fidelities.
--   - `cupOne`: PDF p.8, Eq.(2): u_i=sum_a |a,a,i>; its squared norm is d.
--   - `cupTwo`: PDF p.8, Eq.(3): v_i=sum_a |a,i,a>; <u_i,v_j>=delta_ij.
--   - `cupOperatorOne`: PDF pp.7–9: the rank-d operator V^Gamma((0 1)), sum_i |u_i><u_i|.
--   - `cupOperatorTwo`: PDF pp.7–9: the rank-d operator V^Gamma((0 2)), sum_i |v_i><v_i|.
--   - `cycleOperator`: PDF pp.8–9: one partially transposed three-cycle, sum_i |v_i><u_i|.
--   - `restrictedChoi`: PDF p.9, Eq.(6): exactly the four rank-d operators, with Hermitian coefficients.
--   - `RestrictedAchievable`: PDF pp.9–10: a restricted physical channel, retaining an actual channel witness.
--   - `ellipseAxisA`: PDF pp.2,10,12: a=(d^2-1)^(-1/2).
--   - `ellipseAxisB`: PDF pp.2,10,12: b=(d^2-1)^(-1).
--   - `ellipseCenter`: PDF p.12: c_lambda=(lambda*d-2)/(d^2-1).
--   - `InEllipse`: PDF p.12, Eq.(10): filled ellipse, expressed in s=p+q and t=p-q coordinates.
--   - `InEllipseUnion`: PDF p.12, Theorem 6: both endpoints of the continuous parameter interval are included.
--   - `IsParetoOptimal`: PDF p.13: the upper-right boundary, interpreted as coordinatewise Pareto optimality.
--   - `IsRestrictedParetoOptimal`: PDF p.13: coordinatewise Pareto optimality within the four-operator family.
--   - `cloningReferenceMarginal`: PDF pp.1,5: trace out the other output while retaining the shared reference A.
--   - `IsotropicCompatible`: PDF pp.1–2: two possibly different isotropic states sharing their reference subsystem.
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, https://arxiv.org/abs/2106.09655v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

/-!
Statements from Nechita, Pellegrini and Rochette, arXiv:2106.09655v1.
The source's "singlet fractions" are real depolarizing shrink parameters.
All registers use the fixed computational basis of C^d; the Choi input is first.
The frozen QuditFidelity.depolarizingMap uses the complementary noise parameter,
so depolarizingShrink below explicitly follows this paper's convention.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P05

-- Exact frozen interfaces: input-first unnormalized Choi, normalized isotropic state,
-- and matrix tensor power on Fin N → Fin d. See ASSESSMENT.json for the comparisons.
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Information100.P60 (isotropic)
open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF pp.3–4: N ordered qudit output registers. -/
abbrev CloningOutputs (d N : ℕ) := Fin N → Fin d

/-- PDF p.5: input-first computational basis for an unnormalized Choi matrix. -/
abbrev CloningChoiBasis (d N : ℕ) := Fin d × CloningOutputs d N

/-- PDF p.3: ordinary, unnormalized partial trace onto output register i. -/
def outputTrace {d N : ℕ} (i : Fin N)
    (X : Matrix (CloningOutputs d N) (CloningOutputs d N) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun a b => ∑ z : CloningOutputs d N,
    if z i = a then X z (Function.update z i b) else 0

/-- PDF p.3: the i-th marginal map, on all input operators. -/
def cloningMarginal {d N : ℕ} (T : Superop (Fin d) (CloningOutputs d N)) (i : Fin N) :
    Superop (Fin d) (Fin d) := fun X => outputTrace i (T X)

/-- PDF pp.2,6: D_p(X)=pX+(1-p)Tr(X)I/d; p is not constrained to be positive. -/
def depolarizingShrink (d : ℕ) (p : ℝ) : Superop (Fin d) (Fin d) :=
  fun X => (p : ℂ) • X + (((1 - p : ℝ) : ℂ) * X.trace / (d : ℂ)) • 1

/-- PDF p.4, Definition 3: explicit normalized-Haar twirl of the actual joint map. -/
def cloningTwirl {d N : ℕ} (T : Superop (Fin d) (CloningOutputs d N)) :
    Superop (Fin d) (CloningOutputs d N) :=
  fun X => ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    conjSuperop (tensorPower N (U : Matrix (Fin d) (Fin d) ℂ))
      (T (conjSuperop (star (U : Matrix (Fin d) (Fin d) ℂ)) X))
    ∂Schur.unitaryHaar d

/-- PDF p.5: V(pi)(v_0 tensor ... tensor v_N) has factor pi^{-1}(j) at j. -/
def physicalPermutation (d N : ℕ) (pi : Equiv.Perm (Fin (N + 1))) :
    Matrix (CloningChoiBasis d N) (CloningChoiBasis d N) ℂ :=
  fun x y => if Fin.cons x.1 x.2 = (Fin.cons y.1 y.2) ∘ pi.symm then 1 else 0

/-- PDF p.3: squared pure-input fidelity, <psi|E(|psi><psi|)|psi>. -/
def pureInputFidelity {d : ℕ} (E : Superop (Fin d) (Fin d))
    (psi : EuclideanSpace ℂ (Fin d)) : ℝ :=
  effectProb (pureDensity psi) (E (pureDensity psi))

/-- PDF p.4: the infimum is taken over normalized pure inputs. -/
def worstMarginal {d N : ℕ} (T : Superop (Fin d) (CloningOutputs d N)) (i : Fin N) : ℝ :=
  sInf {r : ℝ | ∃ psi : EuclideanSpace ℂ (Fin d),
    IsState psi ∧ r = pureInputFidelity (cloningMarginal T i) psi}

/-- PDF p.4: sum of separately minimized marginal fidelities; weights need not sum to one. -/
def worstObjective {d N : ℕ} (w : Fin N → ℝ)
    (T : Superop (Fin d) (CloningOutputs d N)) : ℝ :=
  ∑ i, w i * worstMarginal T i

/-- PDF p.4: Haar average of each marginal's pure-input fidelity. -/
def averageObjective {d N : ℕ} (hd : 0 < d) (w : Fin N → ℝ)
    (T : Superop (Fin d) (CloningOutputs d N)) : ℝ :=
  ∑ i, w i * QuditFidelity.averageFidelity d hd (cloningMarginal T i)

/-- PDF pp.3–4, Definition 2: optimize over all complex-linear CPTP joint maps. -/
def worstOptimum (d N : ℕ) (w : Fin N → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ T : Superop (Fin d) (CloningOutputs d N),
    IsChannel T ∧ r = worstObjective w T}

/-- PDF pp.3–4, Definition 2: the average optimum over the same full set of channels. -/
def averageOptimum (d N : ℕ) (hd : 0 < d) (w : Fin N → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ T : Superop (Fin d) (CloningOutputs d N),
    IsChannel T ∧ r = averageObjective hd w T}

/-- PDF pp.2,10,12: physical attainability of the two depolarizing marginal maps. -/
def CloningAchievable (d : ℕ) (p q : ℝ) : Prop :=
  ∃ T : Superop (Fin d) (CloningOutputs d 2), IsChannel T ∧
    cloningMarginal T 0 = depolarizingShrink d p ∧ cloningMarginal T 1 = depolarizingShrink d q

/-- PDF pp.2,6: the corresponding constant squared pure-input fidelities. -/
def CloningFidelityAchievable (d : ℕ) (f g : ℝ) : Prop :=
  ∃ p q : ℝ, CloningAchievable d p q ∧
    f = p + (1 - p) / (d : ℝ) ∧ g = q + (1 - q) / (d : ℝ)

/-- PDF p.8, Eq.(2): u_i=sum_a |a,a,i>; its squared norm is d. -/
def cupOne (d : ℕ) (i : Fin d) (x : CloningChoiBasis d 2) : ℂ :=
  if x.1 = x.2 0 ∧ x.2 1 = i then 1 else 0

/-- PDF p.8, Eq.(3): v_i=sum_a |a,i,a>; <u_i,v_j>=delta_ij. -/
def cupTwo (d : ℕ) (i : Fin d) (x : CloningChoiBasis d 2) : ℂ :=
  if x.1 = x.2 1 ∧ x.2 0 = i then 1 else 0

/-- PDF pp.7–9: the rank-d operator V^Gamma((0 1)), sum_i |u_i><u_i|. -/
def cupOperatorOne (d : ℕ) : Matrix (CloningChoiBasis d 2) (CloningChoiBasis d 2) ℂ :=
  fun x y => ∑ i, cupOne d i x * conj (cupOne d i y)

/-- PDF pp.7–9: the rank-d operator V^Gamma((0 2)), sum_i |v_i><v_i|. -/
def cupOperatorTwo (d : ℕ) : Matrix (CloningChoiBasis d 2) (CloningChoiBasis d 2) ℂ :=
  fun x y => ∑ i, cupTwo d i x * conj (cupTwo d i y)

/-- PDF pp.8–9: one partially transposed three-cycle, sum_i |v_i><u_i|. -/
def cycleOperator (d : ℕ) : Matrix (CloningChoiBasis d 2) (CloningChoiBasis d 2) ℂ :=
  fun x y => ∑ i, cupTwo d i x * conj (cupOne d i y)

/-- PDF p.9, Eq.(6): exactly the four rank-d operators, with Hermitian coefficients. -/
def restrictedChoi (d : ℕ) (alpha beta : ℝ) (gamma : ℂ) :
    Matrix (CloningChoiBasis d 2) (CloningChoiBasis d 2) ℂ :=
  (alpha : ℂ) • cupOperatorOne d + (beta : ℂ) • cupOperatorTwo d +
    gamma • cycleOperator d + conj gamma • (cycleOperator d)ᴴ

/-- PDF pp.9–10: a restricted physical channel, retaining an actual channel witness. -/
def RestrictedAchievable (d : ℕ) (p q : ℝ) : Prop :=
  ∃ T : Superop (Fin d) (CloningOutputs d 2), IsChannel T ∧
    cloningMarginal T 0 = depolarizingShrink d p ∧ cloningMarginal T 1 = depolarizingShrink d q ∧
    ∃ alpha beta : ℝ, ∃ gamma : ℂ, choi T = restrictedChoi d alpha beta gamma

/-- PDF pp.2,10,12: a=(d^2-1)^(-1/2). -/
def ellipseAxisA (d : ℕ) : ℝ := 1 / Real.sqrt ((d : ℝ) ^ 2 - 1)

/-- PDF pp.2,10,12: b=(d^2-1)^(-1). -/
def ellipseAxisB (d : ℕ) : ℝ := 1 / ((d : ℝ) ^ 2 - 1)

/-- PDF p.12: c_lambda=(lambda*d-2)/(d^2-1). -/
def ellipseCenter (d : ℕ) (lambda : ℝ) : ℝ :=
  (lambda * (d : ℝ) - 2) / ((d : ℝ) ^ 2 - 1)

/-- PDF p.12, Eq.(10): filled ellipse, expressed in s=p+q and t=p-q coordinates. -/
def InEllipse (d : ℕ) (lambda s t : ℝ) : Prop :=
  t ^ 2 / ellipseAxisA d ^ 2 + (s - ellipseCenter d lambda) ^ 2 / ellipseAxisB d ^ 2
    ≤ lambda ^ 2

/-- PDF p.12, Theorem 6: both endpoints of the continuous parameter interval are included. -/
def InEllipseUnion (d : ℕ) (s t : ℝ) : Prop :=
  ∃ lambda : ℝ, 0 ≤ lambda ∧ lambda ≤ (d : ℝ) ∧ InEllipse d lambda s t

/-- PDF p.13: the upper-right boundary, interpreted as coordinatewise Pareto optimality. -/
def IsParetoOptimal (d : ℕ) (p q : ℝ) : Prop :=
  CloningAchievable d p q ∧ ∀ r s : ℝ, CloningAchievable d r s → p ≤ r → q ≤ s → r = p ∧ s = q

/-- PDF p.13: coordinatewise Pareto optimality within the four-operator family. -/
def IsRestrictedParetoOptimal (d : ℕ) (p q : ℝ) : Prop :=
  RestrictedAchievable d p q ∧ ∀ r s : ℝ,
    RestrictedAchievable d r s → p ≤ r → q ≤ s → r = p ∧ s = q

/-- PDF pp.1,5: trace out the other output while retaining the shared reference A. -/
def cloningReferenceMarginal {d : ℕ} (i : Fin 2)
    (rho : Matrix (CloningChoiBasis d 2) (CloningChoiBasis d 2) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun a b => ∑ z : CloningOutputs d 2,
    if z i = a.2 then rho (a.1, z) (b.1, Function.update z i b.2) else 0

/-- PDF pp.1–2: two possibly different isotropic states sharing their reference subsystem. -/
def IsotropicCompatible (d : ℕ) (p q : ℝ) : Prop :=
  ∃ rho : Matrix (CloningChoiBasis d 2) (CloningChoiBasis d 2) ℂ, IsDensityMatrix rho ∧
    cloningReferenceMarginal 0 rho = isotropic d p ∧ cloningReferenceMarginal 1 rho = isotropic d q

/-! Small definitional sanity checks; no theorem proofs are supplied below. -/

example (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) :
    depolarizingShrink d 1 X = X := by
  simp [depolarizingShrink]

example (d : ℕ) (p q : ℝ) :
    CloningAchievable d p q ↔ ∃ T : Superop (Fin d) (CloningOutputs d 2), IsChannel T ∧
      cloningMarginal T 0 = depolarizingShrink d p ∧ cloningMarginal T 1 = depolarizingShrink d q := Iff.rfl

example (d : ℕ) (i : Fin d) (a : Fin d) :
    cupOne d i (a, ![a, i]) = 1 := by
  simp [cupOne]

example (d : ℕ) (i : Fin d) (a : Fin d) :
    cupTwo d i (a, ![i, a]) = 1 := by
  simp [cupTwo]

example (d : ℕ) : ellipseCenter d 0 = -2 / ((d : ℝ) ^ 2 - 1) := by
  simp [ellipseCenter]

example (d : ℕ) : isotropic d 0 = (((1 / (d : ℝ) ^ 2 : ℝ) : ℂ)) • 1 := by
  ext x y
  simp [isotropic, Matrix.one_apply]

example {d N : ℕ} (T : Superop (Fin d) (CloningOutputs d N))
    (x y : CloningChoiBasis d N) :
    choi T x y = T (Matrix.single x.1 y.1 1) x.2 y.2 := rfl

example {d N : ℕ} (i : Fin N) :
    outputTrace (d := d) i (0 : Matrix (CloningOutputs d N) (CloningOutputs d N) ℂ) = 0 := by
  ext a b
  simp [outputTrace]

example (d : ℕ) (x y : CloningOutputs d 0) (U : Matrix (Fin d) (Fin d) ℂ) :
    tensorPower 0 U x y = 1 := by
  simp [tensorPower]

example (d N : ℕ) (x : CloningChoiBasis d N) :
    physicalPermutation d N (Equiv.refl _) x x = 1 := by
  simp [physicalPermutation]

example {d N : ℕ} (T : Superop (Fin d) (CloningOutputs d N)) :
    worstObjective (fun _ => 0) T = 0 := by
  simp [worstObjective]

example {d N : ℕ} (hd : 0 < d) (T : Superop (Fin d) (CloningOutputs d N)) :
    averageObjective hd (fun _ => 0) T = 0 := by
  simp [averageObjective]

example (d : ℕ) : restrictedChoi d 0 0 0 = 0 := by
  simp [restrictedChoi]

example (d N : ℕ) :
    cloningTwirl (fun _ : Matrix (Fin d) (Fin d) ℂ => (0 : Matrix (CloningOutputs d N) (CloningOutputs d N) ℂ)) =
      (fun _ => 0) := by
  funext X
  simp [cloningTwirl, conjSuperop]

end QAlgorithms.Papers.Independent.Extend50.P05


