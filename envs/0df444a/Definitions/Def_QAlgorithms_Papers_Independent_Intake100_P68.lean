-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68
-- name    : QAlgorithms_Papers_Independent_Intake100_P68
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T18:04:29.076218+00:00
-- url     : https://prove2.me/theorems/2566199a-87bf-4192-825f-288b6f4049a7
-- title:
--   Definitions for On the continuity of asymptotic measures of entanglement
-- statement:
--   The objects the formalized statements of *On the continuity of asymptotic measures of entanglement* (arXiv:quant-ph/0203107) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `VidalOperator`: PDF p.1: owned bipartite indexing of the imported finite operator type.
--   - `copyBasis`: PDF pp.1,4 [2]: a fixed basis enumeration of n copies of a local register.
--   - `ownedCopies`: PDF pp.1,4 [13]: integer tensor powers, regrouped by owner; n=0 is scalar 1. This is only a basis adapter for the frozen Information100.P04.copies constructor.
--   - `Supply`: PDF p.4 [14]: an independent bipartite resource with a real copy supply. Validity is separate, so constructed tensor powers need no assumed proof field.
--   - `SupplyProduct`
--   - `ValidResource`: PDF pp.1,4: only positive-dimensional normalized densities and nonnegative supplies.
--   - `scaleSupplies`: PDF p.4 [14]: multiplication of formal supplies, without assuming homogeneity of E.
--   - `single`: PDF p.2 (8): one resource species.
--   - `supplyCopiesAt`: PDF p.4 [2],[13]: actual integer supply at block length N.
--   - `aliceBlockDim`: PDF p.4 [14]: Alice's local dimension of the independent input product.
--   - `blockB`: PDF p.4 [14]: Bob's local dimension of the independent input product.
--   - `ownedProduct`: PDF p.4 [14]: owned tensor product, using the same local product enumeration on both axes.
--   - `supplyBlock`: PDF p.4 [14]: the actual independent-copy product at N, with the empty resource scalar 1.
--   - `AsymptoticLOCCConverts`: PDF p.4 [13],[14]: asymptotic LOCC with arbitrary error and positive rate slack. A common relative slack on all output supplies is equivalent to arbitrarily small slack in each positive supply. Protocols depend on N, error and slack. The output is unconditional and normalized. Zero supplies require no special division and include free disposal. No output optimizer is postulated.
--   - `IsAsymptoticMeasure`: PDF p.2 (9), pp.4–5 [14]: the sole asymptotic monotonicity axiom, for actual conversions of independent resource products. No continuity, additivity, homogeneity, sign, or ebit normalization is an axiom here. Cross multiplication avoids division by a zero input rate.
--   - `resourceSingleValue`: PDF p.2: restriction of the common resource functional to a single density.
--   - `phiPlusDensity`: PDF p.1 (1): normalized positive-sign two-qubit Phi-plus projector.
--   - `loccDistillationRates`: PDF p.1 (4): computed achievable ebit yields, not a free numerical field.
--   - `loccDistillable`: PDF p.1 (4): optimal LOCC ebit yield. The feasible set contains 0 and is bounded above by the logarithm of the smaller positive local dimension.
--   - `loccPreparationRates`: PDF p.1 (5): computed achievable preparation costs, including zero.
--   - `loccEntanglementCost`: PDF p.1 (5): optimal LOCC ebit supply. On densities this nonempty set is bounded below by zero and has a finite teleportation upper bound.
--   - `AffineState`: PDF p.2: affine ambient space, not the relatively open density set.
--   - `DensitySpace`: PDF pp.3–4: density-relative topology at surface and distillability boundaries.
--   - `affineMixture`: PDF p.3 (21): affine mixture; statements restrict p to [0,1].
--   - `densityBall`: PDF p.2: density ball, with the source's numerical trace distance.
--   - `ballYield`: PDF p.2: actual infimum of distillable entanglement on B.
--   - `ballCost`: PDF p.2: actual supremum of preparation cost on B.
--   - `conversionLoss`: PDF p.2: rewritten kappa, extending the source formula continuously to r=1.
--   - `PPTAssistedConverts`: PDF p.4: PPT assistance is an actual supplied PPT density inserted into an adaptive LOCC protocol. Its dimensions and state can depend on N, error and slack. This is distinct from optimizing all PPT-preserving channels.
--   - `pptAssistedDistillable`: PDF p.4: operational distillation with supplied PPT resources. The rate set contains 0 and is bounded by logarithmic negativity.
--   - `MultiBasis`: PDF p.5 [16]: finite multipartite product coordinates.
--   - `MultiOp`: PDF p.5 [16]: operators with the party decomposition retained.
--   - `multiCopies`: PDF p.5 [16]: n copies of every party, regrouped by owner.
--   - `MultiReach`: PDF p.5 [16]: an actual deterministic multipartite LOCC conversion, using accepted normalized states and the accepted adaptive local instruments. The terminal transcript is forgotten, so no success branch is postselected.
--   - `MultiConverts`: PDF p.5 [16] with p.4 [13]: asymptotic multipartite LOCC conversion, with positive rate slack and arbitrary error, integer floors, and unconditional normalized outputs. The family of protocols is constructed from actual local instruments on the same named parties.
--   - `IsMultiAsymptoticMeasure`: PDF p.5 [16], condition (9): one finite real functional across all positive multipartite dimensions, monotone for the actual asymptotic independent-copy conversions between normalized pure states. No pure-state entropy or continuity assumption.
--   - `localLift`: PDF p.5 [16]: an operator on the chosen local subsystem, identity on the other parties. This fixes which party owns the filter.
--   - `filterAction`: PDF p.5 [16]: the successful local filter M1=sqrt(I-epsilon A^dagger A). The theorem uses 0<epsilon<1 and traceNorm(A^dagger A)=1; hence its argument is positive definite and M1 is invertible. The omitted branch is M2=sqrt(epsilon) A and completes the local POVM.
--   - `filterProbability`: PDF p.5 [16]: actual success probability of M1, before normalization.
--   - `filterVector`: PDF p.5 [16]: successful branch normalized by its actual norm=sqrt(p). The small-epsilon hypotheses make this denominator strictly positive.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, https://arxiv.org/abs/quant-ph/0203107v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

/-!
Vidal, arXiv:quant-ph/0203107v1. All locators are PDF pages.
The two catalytic nodes are deferred: the source does not specify their
asymptotic catalyst size and return model. New resource and rate definitions are paper-local; imported primitives are reused.
Finite adaptive LOCC is reused from the pinned accepted library. Arbitrarily
accurate finite protocols suffice for the asymptotic conversion relation; no
identification with separable channels or PPT-preserving channels is made.
All resource exponents denote copy supplies with floors, never matrix powers.
The real operational extrema below are used only on normalized densities in
positive finite dimensions. Disposal makes the yield set nonempty; local
preparation and teleportation make the cost set nonempty. Nonnegativity and
the finite local dimension bound prevent empty/unbounded real-extremum defaults.
Compilation is pending the separate mechanical-check stage.
-/

noncomputable section

open Filter Topology
open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.1: owned bipartite indexing of the imported finite operator type. -/
abbrev VidalOperator (a b : ℕ) :=
  QAlgorithms.Papers.Independent.Information100.P21.Op (Fin a × Fin b)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF pp.1,4 [2]: a fixed basis enumeration of n copies of a local register. -/
def copyBasis (a n : ℕ) : Fin (a ^ n) ≃ (Fin n → Fin a) :=
  Fintype.equivOfCardEq (by simp)

/-- PDF pp.1,4 [13]: integer tensor powers, regrouped by owner; n=0 is scalar 1.
This is only a basis adapter for the frozen Information100.P04.copies constructor. -/
def ownedCopies {a b : ℕ} (rho : VidalOperator a b) (n : ℕ) : VidalOperator (a ^ n) (b ^ n) :=
  (QAlgorithms.Papers.Independent.Information100.P04.copies rho n).submatrix
    (fun i => (copyBasis a n i.1, copyBasis b n i.2))
    (fun j => (copyBasis a n j.1, copyBasis b n j.2))

/-- PDF p.4 [14]: an independent bipartite resource with a real copy supply.
Validity is separate, so constructed tensor powers need no assumed proof field. -/
structure Supply where
  a : ℕ
  b : ℕ
  rho : VidalOperator a b
  amount : ℝ

abbrev SupplyProduct := List Supply

/-- PDF pp.1,4: only positive-dimensional normalized densities and nonnegative supplies. -/
def ValidResource (R : SupplyProduct) : Prop :=
  ∀ s ∈ R, 0 < s.a ∧ 0 < s.b ∧ IsDensityMatrix s.rho ∧ 0 ≤ s.amount

/-- PDF p.4 [14]: multiplication of formal supplies, without assuming homogeneity of E. -/
def scaleSupplies (x : ℝ) (R : SupplyProduct) : SupplyProduct :=
  R.map fun s => { s with amount := x * s.amount }

/-- PDF p.2 (8): one resource species. -/
def single {a b : ℕ} (rho : VidalOperator a b) (x : ℝ) : SupplyProduct := [⟨a, b, rho, x⟩]

/-- PDF p.4 [2],[13]: actual integer supply at block length N. -/
def supplyCopiesAt (s : Supply) (N : ℕ) : ℕ := ⌊s.amount * (N : ℝ)⌋₊

/-- PDF p.4 [14]: Alice's local dimension of the independent input product. -/
def aliceBlockDim (N : ℕ) : SupplyProduct → ℕ
  | [] => 1
  | s :: R => s.a ^ supplyCopiesAt s N * aliceBlockDim N R

/-- PDF p.4 [14]: Bob's local dimension of the independent input product. -/
def blockB (N : ℕ) : SupplyProduct → ℕ
  | [] => 1
  | s :: R => s.b ^ supplyCopiesAt s N * blockB N R

/-- PDF p.4 [14]: owned tensor product, using the same local product enumeration on both axes. -/
def ownedProduct {a b c d : ℕ} (rho : VidalOperator a b) (sigma : VidalOperator c d) : VidalOperator (a*c) (b*d) :=
  fun i j =>
    let ia := (finProdFinEquiv : Fin a × Fin c ≃ Fin (a*c)).symm i.1
    let ib := (finProdFinEquiv : Fin b × Fin d ≃ Fin (b*d)).symm i.2
    let ja := (finProdFinEquiv : Fin a × Fin c ≃ Fin (a*c)).symm j.1
    let jb := (finProdFinEquiv : Fin b × Fin d ≃ Fin (b*d)).symm j.2
    rho (ia.1, ib.1) (ja.1, jb.1) * sigma (ia.2, ib.2) (ja.2, jb.2)

/-- PDF p.4 [14]: the actual independent-copy product at N, with the empty resource scalar 1. -/
def supplyBlock (N : ℕ) : (R : SupplyProduct) → VidalOperator (aliceBlockDim N R) (blockB N R)
  | [] => 1
  | s :: R => ownedProduct (ownedCopies s.rho (supplyCopiesAt s N)) (supplyBlock N R)

/-- PDF p.4 [13],[14]: asymptotic LOCC with arbitrary error and positive rate slack.
A common relative slack on all output supplies is equivalent to arbitrarily
small slack in each positive supply. Protocols depend on N, error and slack.
The output is unconditional and normalized. Zero supplies require no special
division and include free disposal. No output optimizer is postulated. -/
def AsymptoticLOCCConverts (R S : SupplyProduct) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∃ L : Superop (Fin (aliceBlockDim N R) × Fin (blockB N R))
          (Fin (aliceBlockDim N (scaleSupplies (1-delta) S)) × Fin (blockB N (scaleSupplies (1-delta) S))),
        FiniteLOCC L ∧ IsDensityMatrix (L (supplyBlock N R)) ∧
        traceDistance (L (supplyBlock N R)) (supplyBlock N (scaleSupplies (1-delta) S)) ≤ epsilon

/-- PDF p.2 (9), pp.4–5 [14]: the sole asymptotic monotonicity axiom,
for actual conversions of independent resource products. No continuity,
additivity, homogeneity, sign, or ebit normalization is an axiom here.
Cross multiplication avoids division by a zero input rate. -/
def IsAsymptoticMeasure (E : SupplyProduct → ℝ) : Prop :=
  ∀ R S : SupplyProduct, ValidResource R → ValidResource S →
    ∀ x y : ℝ, 0 < x → 0 ≤ y → AsymptoticLOCCConverts (scaleSupplies x R) (scaleSupplies y S) →
      y * E S ≤ x * E R

/-- PDF p.2: restriction of the common resource functional to a single density. -/
def resourceSingleValue (E : SupplyProduct → ℝ) {a b : ℕ} (rho : VidalOperator a b) : ℝ := E (single rho 1)

/-- PDF p.1 (1): normalized positive-sign two-qubit Phi-plus projector. -/
def phiPlusDensity : VidalOperator 2 2 := pureDensity (finiteMaxEntangled (Fin 2))

/-- PDF p.1 (4): computed achievable ebit yields, not a free numerical field. -/
def loccDistillationRates {a b : ℕ} (rho : VidalOperator a b) : Set ℝ :=
  {r | 0 ≤ r ∧ AsymptoticLOCCConverts (single rho 1) (single phiPlusDensity r)}

/-- PDF p.1 (4): optimal LOCC ebit yield. The feasible set contains 0 and
is bounded above by the logarithm of the smaller positive local dimension. -/
def loccDistillable {a b : ℕ} (rho : VidalOperator a b) : ℝ := sSup (loccDistillationRates rho)

/-- PDF p.1 (5): computed achievable preparation costs, including zero. -/
def loccPreparationRates {a b : ℕ} (rho : VidalOperator a b) : Set ℝ :=
  {r | 0 ≤ r ∧ AsymptoticLOCCConverts (single phiPlusDensity r) (single rho 1)}

/-- PDF p.1 (5): optimal LOCC ebit supply. On densities this nonempty
set is bounded below by zero and has a finite teleportation upper bound. -/
def loccEntanglementCost {a b : ℕ} (rho : VidalOperator a b) : ℝ := sInf (loccPreparationRates rho)

/-- PDF p.2: affine ambient space, not the relatively open density set. -/
abbrev AffineState (a b : ℕ) := {rho : VidalOperator a b // rho.IsHermitian ∧ rho.trace = 1}

/-- PDF pp.3–4: density-relative topology at surface and distillability boundaries. -/
abbrev DensitySpace (a b : ℕ) := {rho : VidalOperator a b // IsDensityMatrix rho}

/-- PDF p.3 (21): affine mixture; statements restrict p to [0,1]. -/
def affineMixture {a b : ℕ} (rho sigma : VidalOperator a b) (p : ℝ) : VidalOperator a b :=
  ((1-p : ℝ) : ℂ) • rho + (p : ℂ) • sigma

/-- PDF p.2: density ball, with the source's numerical trace distance. -/
def densityBall {a b : ℕ} (rho : VidalOperator a b) (epsilon : ℝ) : Set (VidalOperator a b) :=
  {sigma | IsDensityMatrix sigma ∧ traceDistance rho sigma ≤ epsilon}

/-- PDF p.2: actual infimum of distillable entanglement on B. -/
def ballYield {a b : ℕ} (rho : VidalOperator a b) (epsilon : ℝ) : ℝ :=
  sInf (loccDistillable '' densityBall rho epsilon)

/-- PDF p.2: actual supremum of preparation cost on B. -/
def ballCost {a b : ℕ} (rho : VidalOperator a b) (epsilon : ℝ) : ℝ :=
  sSup (loccEntanglementCost '' densityBall rho epsilon)

/-- PDF p.2: rewritten kappa, extending the source formula continuously to r=1. -/
def conversionLoss (p r : ℝ) : ℝ := p * (1-r) / (r + (1-r)*p)

/-- PDF p.4: PPT assistance is an actual supplied PPT density inserted into
an adaptive LOCC protocol. Its dimensions and state can depend on N, error
and slack. This is distinct from optimizing all PPT-preserving channels. -/
def PPTAssistedConverts (R S : SupplyProduct) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∃ u v : ℕ, 0 < u ∧ 0 < v ∧
      ∃ tau : VidalOperator u v, IsDensityMatrix tau ∧
        (Entanglement.partialTransposeFirst tau).PosSemidef ∧
      ∃ L : Superop (Fin (aliceBlockDim N R * u) × Fin (blockB N R * v))
          (Fin (aliceBlockDim N (scaleSupplies (1-delta) S)) × Fin (blockB N (scaleSupplies (1-delta) S))),
        FiniteLOCC L ∧ IsDensityMatrix (L (ownedProduct (supplyBlock N R) tau)) ∧
        traceDistance (L (ownedProduct (supplyBlock N R) tau))
          (supplyBlock N (scaleSupplies (1-delta) S)) ≤ epsilon

/-- PDF p.4: operational distillation with supplied PPT resources.
The rate set contains 0 and is bounded by logarithmic negativity. -/
def pptAssistedDistillable {a b : ℕ} (rho : VidalOperator a b) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ PPTAssistedConverts (single rho 1) (single phiPlusDensity r)}

example {a b : ℕ} (rho : VidalOperator a b) : ownedCopies rho 0 = 1 := by
  ext i j
  letI : Subsingleton (Fin (a ^ 0) × Fin (b ^ 0)) := by
    simpa only [pow_zero] using (inferInstance : Subsingleton (Fin 1 × Fin 1))
  have hij : i = j := Subsingleton.elim i j
  rw [hij]
  change (∏ k : Fin 0,
    rho ((copyBasis a 0 j.1) k, (copyBasis b 0 j.2) k)
      ((copyBasis a 0 j.1) k, (copyBasis b 0 j.2) k)) =
    (if j = j then (1 : ℂ) else 0)
  rw [if_pos (Eq.refl j)]
  apply Finset.prod_eq_one
  intro k _
  exact Fin.elim0 k

example {a b : ℕ} (rho sigma : VidalOperator a b) : affineMixture rho sigma 0 = rho := by
  simp [affineMixture]

example (R : SupplyProduct) : scaleSupplies 1 R = R := by
  simp [scaleSupplies]

example : supplyBlock 0 [] = (1 : VidalOperator 1 1) := rfl

example (p : ℝ) : conversionLoss p 1 = 0 := by simp [conversionLoss]

example (r : ℝ) : conversionLoss 0 r = 0 := by simp [conversionLoss]

/-- PDF p.5 [16]: finite multipartite product coordinates. -/
abbrev MultiBasis {m : ℕ} (d : Fin m → ℕ) := (i : Fin m) → Fin (d i)

/-- PDF p.5 [16]: operators with the party decomposition retained. -/
abbrev MultiOp {m : ℕ} (d : Fin m → ℕ) := Matrix (MultiBasis d) (MultiBasis d) ℂ

/-- PDF p.5 [16]: n copies of every party, regrouped by owner. -/
def multiCopies {m : ℕ} {d : Fin m → ℕ} (rho : MultiOp d) (n : ℕ) :
    MultiOp (fun i => d i ^ n) :=
  fun x y => ∏ k : Fin n,
    rho (fun i => copyBasis (d i) n (x i) k) (fun i => copyBasis (d i) n (y i) k)

/-- PDF p.5 [16]: an actual deterministic multipartite LOCC conversion,
using accepted normalized states and the accepted adaptive local instruments.
The terminal transcript is forgotten, so no success branch is postselected. -/
def MultiReach {m : ℕ} (d e : Fin m → ℕ)
    (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i) (rho : MultiOp d) (sigma : MultiOp e) : Prop :=
  ∃ hrho : IsDensityMatrix rho, ∃ hsigma : IsDensityMatrix sigma,
    QAlgorithms.Papers.Independent.Claimed50.P33.LOCC
      ⟨d, hd, rho, hrho⟩ [(1, ⟨e, he, sigma, hsigma⟩)]

/-- PDF p.5 [16] with p.4 [13]: asymptotic multipartite LOCC conversion,
with positive rate slack and arbitrary error, integer floors, and unconditional
normalized outputs. The family of protocols is constructed from actual local
instruments on the same named parties. -/
def MultiConverts {m : ℕ} (d e : Fin m → ℕ)
    (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i)
    (rho : MultiOp d) (sigma : MultiOp e) (x y : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      let ni := ⌊x * (N : ℝ)⌋₊
      let no := ⌊((1-delta)*y) * (N : ℝ)⌋₊
      ∃ tau : MultiOp (fun i => e i ^ no),
        MultiReach (fun i => d i ^ ni) (fun i => e i ^ no)
          (fun i => pow_pos (hd i) ni) (fun i => pow_pos (he i) no)
          (multiCopies rho ni) tau ∧
        traceDistance tau (multiCopies sigma no) ≤ epsilon

/-- PDF p.5 [16], condition (9): one finite real functional across all
positive multipartite dimensions, monotone for the actual asymptotic
independent-copy conversions between normalized pure states. No pure-state entropy or continuity assumption. -/
def IsMultiAsymptoticMeasure {m : ℕ} (E : (d : Fin m → ℕ) → MultiOp d → ℝ) : Prop :=
  ∀ (d e : Fin m → ℕ) (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i)
    (psi : EuclideanSpace ℂ (MultiBasis d)) (phi : EuclideanSpace ℂ (MultiBasis e)),
    ‖psi‖ = 1 → ‖phi‖ = 1 →
    ∀ x y : ℝ, 0 < x → 0 ≤ y →
      MultiConverts d e hd he (pureDensity psi) (pureDensity phi) x y →
      y * E e (pureDensity phi) ≤ x * E d (pureDensity psi)

/-- PDF p.5 [16]: an operator on the chosen local subsystem, identity
on the other parties. This fixes which party owns the filter. -/
def localLift {m : ℕ} (d : Fin m → ℕ) (party : Fin m)
    (A : Matrix (Fin (d party)) (Fin (d party)) ℂ) : MultiOp d :=
  fun x y => if ∀ i, i ≠ party → x i = y i then A (x party) (y party) else 0

/-- PDF p.5 [16]: the successful local filter M1=sqrt(I-epsilon A^dagger A).
The theorem uses 0<epsilon<1 and traceNorm(A^dagger A)=1; hence its
argument is positive definite and M1 is invertible. The omitted branch is
M2=sqrt(epsilon) A and completes the local POVM. -/
def filterAction {m : ℕ} (d : Fin m → ℕ) (party : Fin m)
    (A : Matrix (Fin (d party)) (Fin (d party)) ℂ)
    (psi : EuclideanSpace ℂ (MultiBasis d)) (epsilon : ℝ) :
    EuclideanSpace ℂ (MultiBasis d) :=
  act (localLift d party (cfc Real.sqrt (1 - (epsilon : ℂ) • (Aᴴ * A)))) psi

/-- PDF p.5 [16]: actual success probability of M1, before normalization. -/
def filterProbability {m : ℕ} (d : Fin m → ℕ) (party : Fin m)
    (A : Matrix (Fin (d party)) (Fin (d party)) ℂ)
    (psi : EuclideanSpace ℂ (MultiBasis d)) (epsilon : ℝ) : ℝ :=
  ‖filterAction d party A psi epsilon‖ ^ 2

/-- PDF p.5 [16]: successful branch normalized by its actual norm=sqrt(p).
The small-epsilon hypotheses make this denominator strictly positive. -/
def filterVector {m : ℕ} (d : Fin m → ℕ) (party : Fin m)
    (A : Matrix (Fin (d party)) (Fin (d party)) ℂ)
    (psi : EuclideanSpace ℂ (MultiBasis d)) (epsilon : ℝ) :
    EuclideanSpace ℂ (MultiBasis d) :=
  let v := filterAction d party A psi epsilon
  ((‖v‖)⁻¹ : ℂ) • v

example {m : ℕ} (d : Fin m → ℕ) (party : Fin m)
    (A : Matrix (Fin (d party)) (Fin (d party)) ℂ) (x : MultiBasis d) :
    localLift d party A x x = A (x party) (x party) := by simp [localLift]

end QAlgorithms.Papers.Independent.Intake100.P68


