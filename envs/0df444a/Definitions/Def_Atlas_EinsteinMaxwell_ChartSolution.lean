-- Prove2me | Definitions.Def_Atlas_EinsteinMaxwell_ChartSolution
-- name    : Atlas_EinsteinMaxwell_ChartSolution
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T23:48:36.140704+00:00
-- url     : https://prove2.me/theorems/98eeec2c-799d-434c-9c6b-1b7a78f523c7
-- title:
--   Einstein–Maxwell chart solutions and change of coordinates
-- statement:
--   A chart solution packages the metric coefficients, a genuine inverse metric and a smooth antisymmetric Faraday field on an open four-dimensional domain. Its values satisfy the Einstein residual equation, the inhomogeneous Maxwell equation and the closed-field equation. The change-of-coordinates constructor takes a smooth regular coordinate transformation and the transformed coefficient functions, and returns a solution on the new domain. The metric, inverse and field projections are the specified functions. The proof of the constructor uses the coordinate transformation laws for all three residuals; it does not assume that the transformed coefficients satisfy any field equation.
-- source:
--   The Prove2Me Atlas project, https://prove2.me/submissions/edd46219-5d5a-4adc-a78d-9deb92001a1f . Individual verified source submissions for curvature and Maxwell tensor covariance are referenced in the Lean source.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_Curvature
import Definitions.Def_Atlas_Transport_MatrixCalc
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
/-! Four-dimensional Einstein–Maxwell solutions on coordinate domains and change of coordinates.
Original proofs of the change-of-coordinates identities:
https://prove2.me/submissions/54ab245e-b5e9-4c0d-8d7d-23f2257d6ca4
https://prove2.me/submissions/5148d962-38d9-41a3-af23-e3de1752b678
https://prove2.me/submissions/1a38b27f-8565-4a06-948a-cf826a98147b
https://prove2.me/submissions/c77be6c1-2e96-4972-ad35-8ec42732b151
https://prove2.me/submissions/ce54483a-45d8-4b83-9fad-1de2b323f24e
https://prove2.me/submissions/957172ab-b5d6-4007-aa4f-32e6917990e9
https://prove2.me/submissions/54a511d5-ae1c-479b-af34-66d077a4e96e
https://prove2.me/submissions/05ab9ff5-0dd7-4769-9e61-5893c59a0366
https://prove2.me/submissions/7b48c831-9efc-4088-b1e9-ca64179c383a
https://prove2.me/submissions/923ea4ab-4ea3-4a86-b55c-e941aa21668a
https://prove2.me/submissions/edd46219-5d5a-4adc-a78d-9deb92001a1f
https://prove2.me/submissions/cfe34a12-badd-4814-8461-38dc29911347
https://prove2.me/submissions/21d91e41-8866-461c-ae85-da4077851a0e
https://prove2.me/submissions/c32b798d-88a8-4094-895a-8a53b0262a06
https://prove2.me/submissions/12a6cbf1-905e-47f9-a5b1-a58827711ae7
https://prove2.me/submissions/78a8402b-193c-41c4-8a9c-e68130d6892c
https://prove2.me/submissions/0602f095-5c6f-4ccd-ba70-5b183523cf10
https://prove2.me/submissions/e23b32ec-82f0-4bf9-8476-f725ef966eb8
-/
set_option linter.all false

section











open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

private theorem pd_eq_of_hasDerivAt {f : Pt n → ℝ} {x : Pt n} {i : Fin n} {d : ℝ}
    (h : HasDerivAt (fun u : ℝ => f (Function.update x i u)) d (x i)) : pd i f x = d :=
  h.deriv

private theorem hasDerivAt_slice {f : Pt n → ℝ} {x : Pt n} (i : Fin n) (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun u : ℝ => f (Function.update x i u)) (fderiv ℝ f x (Pi.single i 1)) (x i) := by
  have h1 : HasDerivAt (Function.update x i) (Pi.single i 1) (x i) := hasDerivAt_update x i (x i)
  have h2 : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    rw [Function.update_eq_self]; exact hf.hasFDerivAt
  exact HasFDerivAt.comp_hasDerivAt (hl := h2) (hf := h1)

private theorem differentiableAt_of_contDiffOn {f : Pt n → ℝ} {U : Set (Pt n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : Pt n} (hx : x ∈ U) : DifferentiableAt ℝ f x :=
  (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)

private theorem contDiffOn_pd {f : Pt n → ℝ} {U : Set (Pt n)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (i : Fin n) : ContDiffOn ℝ ∞ (pd i f) U := by
  have hd : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x (Pi.single i 1)) U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  refine hd.congr fun x hx => ?_
  exact pd_eq_of_hasDerivAt (hasDerivAt_slice i (differentiableAt_of_contDiffOn hU hf hx))

end ExactVacuumAtlas


















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

@[simp] private theorem pdM_apply (i : Fin n) (A : Pt n → Matrix (Fin n) (Fin n) ℝ) (y : Pt n) (a b : Fin n) :
    pdM i A y a b = pd i (fun z => A z a b) y := rfl

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

private theorem congr (hA : SmoothOn A U) (h : Set.EqOn A B U) : SmoothOn B U :=
  fun a b => (hA a b).congr fun y hy => by rw [h hy]

private theorem mul (hA : SmoothOn A U) (hB : SmoothOn B U) : SmoothOn (fun y => A y * B y) U := by
  intro a b
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun c _ => (hA a c).mul (hB c b)

private theorem transpose (hA : SmoothOn A U) : SmoothOn (fun y => (A y).transpose) U :=
  fun a b => by simpa only [Matrix.transpose_apply] using hA b a

private theorem comp {Φ : Pt n → Pt n} (hA : SmoothOn A V) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hmaps : Set.MapsTo Φ U V) : SmoothOn (fun y => A (Φ y)) U :=
  fun a b => (hA a b).comp hΦ hmaps

end SmoothOn



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy

end rules




private theorem smoothOn_jacobian {U : Set (Pt n)} (hU : IsOpen U) {Φ : Pt n → Pt n}
    {J : Pt n → Matrix (Fin n) (Fin n) ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hJ : ∀ y ∈ U, ∀ k i : Fin n,
      HasDerivAt (fun u : ℝ => Φ (Function.update y i u) k) (J y k i) (y i)) :
    SmoothOn J U := by
  intro k i
  have hk : ContDiffOn ℝ ∞ (fun y => Φ y k) U := (contDiffOn_pi.mp hΦ) k
  exact (contDiffOn_pd hU hk i).congr fun y hy => (pd_eq_of_hasDerivAt (hJ y hy k i)).symm

private theorem contDiffOn_finset_prod {U : Set (Pt n)} {ι : Type*} (s : Finset ι) {f : ι → Pt n → ℝ}
    (hf : ∀ e ∈ s, ContDiffOn ℝ ∞ (f e) U) : ContDiffOn ℝ ∞ (fun y => ∏ e ∈ s, f e y) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using contDiffOn_const
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul (ih fun e he => hf e (Finset.mem_insert_of_mem he))

private theorem SmoothOn.det {U : Set (Pt n)} {J : Pt n → Matrix (Fin n) (Fin n) ℝ} (hJ : SmoothOn J U) :
    ContDiffOn ℝ ∞ (fun y => (J y).det) U := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul
    (contDiffOn_finset_prod Finset.univ fun e _ => hJ (σ e) e)

private theorem SmoothOn.updateRow_single {U : Set (Pt n)} {J : Pt n → Matrix (Fin n) (Fin n) ℝ}
    (hJ : SmoothOn J U) (j a : Fin n) :
    SmoothOn (fun y => (J y).updateRow j (Pi.single a 1)) U := by
  intro p q
  by_cases hp : p = j
  · subst hp
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simp only [Matrix.updateRow_ne hp]
    exact hJ p q

private theorem SmoothOn.adjugate {U : Set (Pt n)} {J : Pt n → Matrix (Fin n) (Fin n) ℝ}
    (hJ : SmoothOn J U) : SmoothOn (fun y => (J y).adjugate) U := by
  intro a b
  simp only [Matrix.adjugate_apply]
  exact (hJ.updateRow_single b a).det

private theorem det_ne_zero_of_mul_eq_one {J K : Matrix (Fin n) (Fin n) ℝ} (h : J * K = 1) : J.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this


private theorem eq_inv_smul_adjugate {J K : Matrix (Fin n) (Fin n) ℝ} (h : J * K = 1) :
    K = (J.det)⁻¹ • J.adjugate := by
  have hd : J.det ≠ 0 := det_ne_zero_of_mul_eq_one h
  have hKJ : K * J = 1 := mul_eq_one_comm.mp h
  have e : J.det • K = J.adjugate := by
    calc J.det • K = K * (J.det • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
          rw [Matrix.mul_smul, mul_one]
      _ = K * (J * J.adjugate) := by rw [Matrix.mul_adjugate]
      _ = (K * J) * J.adjugate := by rw [mul_assoc]
      _ = J.adjugate := by rw [hKJ, one_mul]
  rw [← e, smul_smul, inv_mul_cancel₀ hd, one_smul]


private theorem SmoothOn.of_right_inverse {U : Set (Pt n)} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
    (hJ : SmoothOn J U) (hJK : ∀ y ∈ U, J y * K y = 1) : SmoothOn K U := by
  intro a b
  have hd : ContDiffOn ℝ ∞ (fun y => ((J y).det)⁻¹) U :=
    hJ.det.inv fun y hy => det_ne_zero_of_mul_eq_one (hJK y hy)
  refine (hd.mul (hJ.adjugate a b)).congr fun y hy => ?_
  rw [eq_inv_smul_adjugate (hJK y hy)]
  simp only [Matrix.smul_apply, smul_eq_mul]

end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}



@[simp] private theorem connMat_apply (Γ : Fin n → Fin n → Fin n → Pt n → ℝ) (c : Fin n) (y : Pt n)
    (a b : Fin n) : connMat Γ c y a b = Γ a c b y := rfl



namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

private theorem smoothOn_jac (hc : CoordChange U V Φ J K) : SmoothOn J U :=
  smoothOn_jacobian hc.isOpen hc.smooth hc.jacobian

private theorem smoothOn_inv (hc : CoordChange U V Φ J K) : SmoothOn K U :=
  hc.smoothOn_jac.of_right_inverse hc.mul_inv

private theorem inv_mul (hc : CoordChange U V Φ J K) {y : Pt n} (hy : y ∈ U) : K y * J y = 1 :=
  mul_eq_one_comm.mp (hc.mul_inv y hy)

end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

private theorem smoothOn (hm : MetricData g gi U) : SmoothOn (metricMatrix g) U :=
  fun a b => hm.smooth a b

private theorem smoothOn_inv (hm : MetricData g gi U) : SmoothOn (metricMatrix gi) U :=
  fun a b => hm.smooth_inv a b

private theorem transpose_eq (hm : MetricData g gi U) {x : Pt n} (hx : x ∈ U) :
    (metricMatrix g x).transpose = metricMatrix g x := by
  ext i j
  simp only [Matrix.transpose_apply, metricMatrix, Matrix.of_apply]
  exact hm.symm x hx j i

end MetricData







section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end transform

end ExactVacuumAtlas




















open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}

section
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

private theorem CoordChange.transpose_mul_transpose (hc : CoordChange U V Φ J K) {y : Pt n} (hy : y ∈ U) :
    (K y)ᵀ * (J y)ᵀ = 1 := by
  rw [← Matrix.transpose_mul, hc.mul_inv y hy, Matrix.transpose_one]

end

end ExactVacuumAtlas

open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}
private theorem ExactVacuumAtlas.MetricData.transport (hc : CoordChange U V Φ J K) (hm : MetricData h hi V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix h (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix hi (Φ y) * (K y)ᵀ) :
    MetricData g gi U where
  isOpen := hc.isOpen
  symm x hx i j := by
    have ht : (metricMatrix g x)ᵀ = metricMatrix g x := by
      rw [hg x hx, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        hm.transpose_eq (hc.mapsTo hx), Matrix.mul_assoc]
    have := congrFun (congrFun ht i) j
    simpa [Matrix.transpose_apply, metricMatrix] using this.symm
  inv x hx := by
    rw [hgi x hx, hg x hx]
    calc K x * metricMatrix hi (Φ x) * (K x)ᵀ * ((J x)ᵀ * metricMatrix h (Φ x) * J x)
        = K x * metricMatrix hi (Φ x) * ((K x)ᵀ * (J x)ᵀ) * (metricMatrix h (Φ x) * J x) := by
          simp only [Matrix.mul_assoc]
      _ = K x * (metricMatrix hi (Φ x) * metricMatrix h (Φ x)) * J x := by
          rw [hc.transpose_mul_transpose hx, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hm.inv _ (hc.mapsTo hx), Matrix.mul_one, hc.inv_mul hx]
  smooth i j :=
    ((hc.smoothOn_jac.transpose.mul (hm.smoothOn.comp hc.smooth hc.mapsTo)).mul hc.smoothOn_jac
      |>.congr fun x hx => (hg x hx).symm) i j
  smooth_inv i j :=
    ((hc.smoothOn_inv.mul (hm.smoothOn_inv.comp hc.smooth hc.mapsTo)).mul hc.smoothOn_inv.transpose
      |>.congr fun x hx => (hgi x hx).symm) i j
end


section



















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

end SmoothOn



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy

end rules



end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}



namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

end MetricData





private theorem entry_sandwich (X H Y : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    (X.transpose * H * Y) p q = ∑ b, ∑ a, X a p * H a b * Y b q := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]



section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end transform

end ExactVacuumAtlas

open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}
private theorem ExactVacuumAtlas.d_part {Jm : Matrix (Fin n) (Fin n) ℝ} {D : Fin n → Fin n → Fin n → ℝ} {i j l : Fin n}
    (Di Dj Dl : Matrix (Fin n) (Fin n) ℝ)
    (hDi : ∀ a b, Di a b = ∑ e, D a b e * Jm e i) (hDj : ∀ a b, Dj a b = ∑ e, D a b e * Jm e j)
    (hDl : ∀ a b, Dl a b = ∑ e, D a b e * Jm e l) :
    (Jm.transpose * Dj * Jm) l i + (Jm.transpose * Di * Jm) l j - (Jm.transpose * Dl * Jm) i j
      = 2 * ∑ a, Jm a l * ∑ b, ∑ e, Jm b i * Jm e j * ((D a b e + D a e b - D b e a) / 2) := by
  have hR : 2 * ∑ a, Jm a l * ∑ b, ∑ e, Jm b i * Jm e j * ((D a b e + D a e b - D b e a) / 2)
      = ∑ a, ∑ b, ∑ e, Jm a l * Jm b i * Jm e j * D a b e
        + ∑ a, ∑ b, ∑ e, Jm a l * Jm b i * Jm e j * D a e b
        - ∑ a, ∑ b, ∑ e, Jm a l * Jm b i * Jm e j * D b e a := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hR]
  simp only [entry_sandwich, hDi, hDj, hDl, Finset.mul_sum, Finset.sum_mul]
  have t1 : ∑ b, ∑ a, ∑ e, Jm a l * (D a b e * Jm e j) * Jm b i
      = ∑ a, ∑ b, ∑ e, Jm a l * Jm b i * Jm e j * D a b e := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun e _ => ?_
    ring
  have t2 : ∑ b, ∑ a, ∑ e, Jm a l * (D a b e * Jm e i) * Jm b j
      = ∑ a, ∑ b, ∑ e, Jm a l * Jm b i * Jm e j * D a e b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  have t3 : ∑ b, ∑ a, ∑ e, Jm a i * (D a b e * Jm e l) * Jm b j
      = ∑ a, ∑ b, ∑ e, Jm a l * Jm b i * Jm e j * D b e a := by
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [t1, t2, t3]
end


section











open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

end ExactVacuumAtlas

















open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
include hU hy

end rules

end ExactVacuumAtlas

open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}
private theorem ExactVacuumAtlas.pd_comp {V : Set (Pt n)} (hV : IsOpen V) {f : Pt n → ℝ} (hf : ContDiffOn ℝ ∞ f V)
    {Φ : Pt n → Pt n} {J : Pt n → Matrix (Fin n) (Fin n) ℝ} {y : Pt n} (hy : Φ y ∈ V)
    (hJ : ∀ k i : Fin n, HasDerivAt (fun u : ℝ => Φ (Function.update y i u) k) (J y k i) (y i))
    (i : Fin n) : pd i (fun z => f (Φ z)) y = ∑ e, pd e f (Φ y) * J y e i := by
  have hγ : HasDerivAt (fun u => Φ (Function.update y i u)) (fun k => J y k i) (y i) :=
    hasDerivAt_pi.mpr fun k => hJ k i
  have hd : DifferentiableAt ℝ f (Φ y) := differentiableAt_of_contDiffOn hV hf hy
  have hd' : HasFDerivAt f (fderiv ℝ f (Φ y)) (Φ (Function.update y i (y i))) := by
    rw [Function.update_eq_self]; exact hd.hasFDerivAt
  have hcomp := HasFDerivAt.comp_hasDerivAt (x := y i) (hl := hd') (hf := hγ)
  rw [pd_eq_of_hasDerivAt hcomp]
  have hv : (fun k => J y k i) = ∑ k : Fin n, (J y k i) • (Pi.single k (1 : ℝ) : Pt n) := by
    ext m; simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum]
  simp only [map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pd_eq_of_hasDerivAt (hasDerivAt_slice k hd), mul_comm]
end


section











open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

end ExactVacuumAtlas

open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}
private theorem ExactVacuumAtlas.eventually_update_mem {V : Set (Pt n)} (hV : IsOpen V) {x : Pt n} (hx : x ∈ V)
    (i : Fin n) : ∀ᶠ u in 𝓝 (x i), Function.update x i u ∈ V := by
  have hc : Continuous fun u : ℝ => Function.update x i u :=
    continuous_const.update i continuous_id
  have hmem : V ∈ 𝓝 (Function.update x i (x i)) := by
    rw [Function.update_eq_self]; exact hV.mem_nhds hx
  exact hc.continuousAt.preimage_mem_nhds hmem
end


section











open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

end ExactVacuumAtlas

open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}
private theorem ExactVacuumAtlas.pd_congr_of_eqOn {f h : Pt n → ℝ} {V : Set (Pt n)} (hV : IsOpen V) {x : Pt n}
    (hx : x ∈ V) (hfh : Set.EqOn f h V) (i : Fin n) : pd i f x = pd i h x := by
  unfold pd
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_update_mem hV hx i] with u hu
  exact hfh hu
end


section



















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

end SmoothOn



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy

end rules



end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}



namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

end MetricData






private theorem entry_transpose_trick {H A B : Matrix (Fin n) (Fin n) ℝ} (hH : H.transpose = H) (i j : Fin n) :
    (A.transpose * H * B) i j = (B.transpose * H * A) j i := by
  have : (A.transpose * H * B).transpose = B.transpose * H * A := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH, Matrix.mul_assoc]
  rw [← this, Matrix.transpose_apply]

section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end transform

end ExactVacuumAtlas

open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}
private theorem ExactVacuumAtlas.s_part {Jm H Si Sj Sl : Matrix (Fin n) (Fin n) ℝ} (hH : H.transpose = H) {i j l : Fin n}
    (hjl : ∀ a, Sj a l = Sl a j) (hil : ∀ a, Si a l = Sl a i) (hji : ∀ a, Sj a i = Si a j) :
    (Sj.transpose * H * Jm) l i + (Jm.transpose * H * Sj) l i
      + (Si.transpose * H * Jm) l j + (Jm.transpose * H * Si) l j
      - (Sl.transpose * H * Jm) i j - (Jm.transpose * H * Sl) i j
      = 2 * ∑ a, Jm a l * ∑ b, H a b * Si b j := by
  have hH' : ∀ p q, H p q = H q p := fun p q => by
    have := congrFun (congrFun hH q) p
    simpa [Matrix.transpose_apply] using this
  rw [entry_transpose_trick hH (A := Jm) (B := Sj) l i, entry_transpose_trick hH (A := Jm) (B := Si) l j,
    entry_transpose_trick hH (A := Jm) (B := Sl) i j]
  simp only [entry_sandwich, hjl, hil, hji]
  have e : ∑ a, Jm a l * ∑ b, H a b * Si b j = ∑ b, ∑ a, Si a j * H a b * Jm b l := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hH' a b]; ring
  rw [e]; ring
end


section











open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

private theorem hasDerivAt_pd {f : Pt n → ℝ} {U : Set (Pt n)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {x : Pt n} (hx : x ∈ U) (i : Fin n) :
    HasDerivAt (fun u : ℝ => f (Function.update x i u)) (pd i f x) (x i) := by
  have h := hasDerivAt_slice i (differentiableAt_of_contDiffOn hU hf hx)
  rwa [pd_eq_of_hasDerivAt h]

end ExactVacuumAtlas

















open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
include hU hy

private theorem pd_mul_of {f g : Pt n → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    pd i (fun z => f z * g z) y = pd i f y * g y + f y * pd i g y := by
  have h := ((hasDerivAt_pd hU hf hy i).mul (hasDerivAt_pd hU hg hy i)).deriv
  simp only [Function.update_eq_self] at h
  exact h

private theorem pd_sum_of {ι : Type*} (s : Finset ι) {f : ι → Pt n → ℝ}
    (hf : ∀ e ∈ s, ContDiffOn ℝ ∞ (f e) U) :
    pd i (fun z => ∑ e ∈ s, f e z) y = ∑ e ∈ s, pd i (f e) y :=
  (HasDerivAt.fun_sum fun e he => hasDerivAt_pd hU (hf e he) hy i).deriv

end rules


private theorem pd_eq_fderiv_of {U : Set (Pt n)} (hU : IsOpen U) {f : Pt n → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    {y : Pt n} (hy : y ∈ U) (i : Fin n) : pd i f y = fderiv ℝ f y (Pi.single i 1) :=
  pd_eq_of_hasDerivAt (hasDerivAt_slice i (differentiableAt_of_contDiffOn hU hf hy))


private theorem hasDerivAt_slice_fderiv {U : Set (Pt n)} (hU : IsOpen U) {f : Pt n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) {y : Pt n} (hy : y ∈ U) (i : Fin n) (v : Pt n) :
    HasDerivAt (fun u : ℝ => fderiv ℝ f (Function.update y i u) v)
      (fderiv ℝ (fderiv ℝ f) y (Pi.single i 1) v) (y i) := by
  have hF : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hF.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have h1 : HasDerivAt (Function.update y i) (Pi.single i 1) (y i) := hasDerivAt_update y i (y i)
  have h2 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) (Function.update y i (y i)) := by
    rw [Function.update_eq_self]; exact hd.hasFDerivAt
  have h3 := HasFDerivAt.comp_hasDerivAt (x := y i) (hl := h2) (hf := h1)
  have h4 := h3.clm_apply (hasDerivAt_const (y i) v)
  simp only [Function.update_eq_self, map_zero, add_zero] at h4
  exact h4


private theorem pd_pd_symm {U : Set (Pt n)} (hU : IsOpen U) {f : Pt n → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    {y : Pt n} (hy : y ∈ U) (i j : Fin n) : pd i (pd j f) y = pd j (pd i f) y := by
  have key : ∀ i j : Fin n,
      pd i (pd j f) y = fderiv ℝ (fderiv ℝ f) y (Pi.single i 1) (Pi.single j 1) := by
    intro i j
    rw [pd_congr_of_eqOn hU hy (fun z hz => pd_eq_fderiv_of hU hf hz j) i]
    exact pd_eq_of_hasDerivAt (hasDerivAt_slice_fderiv hU hf hy i (Pi.single j 1))
  rw [key i j, key j i]
  have hsymm : IsSymmSndFDerivAt ℝ f y :=
    (hf.contDiffAt (hU.mem_nhds hy)).isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
  exact hsymm _ _

end ExactVacuumAtlas


















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

end SmoothOn

private theorem pdM_transpose (i : Fin n) (A : Pt n → Matrix (Fin n) (Fin n) ℝ) (y : Pt n) :
    pdM i (fun z => (A z).transpose) y = (pdM i A y).transpose := by
  ext a b; rfl



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy


private theorem pdM_mul (hA : SmoothOn A U) (hB : SmoothOn B U) :
    pdM i (fun z => A z * B z) y = pdM i A y * B y + A y * pdM i B y := by
  ext a b
  simp only [pdM_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [pd_sum_of hU hy i Finset.univ (fun c _ => (hA a c).mul (hB c b)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact pd_mul_of hU hy i (hA a c) (hB c b)

private theorem pdM_congr_of_eqOn (h : Set.EqOn A B U) : pdM i A y = pdM i B y := by
  ext a b
  simp only [pdM_apply]
  exact pd_congr_of_eqOn hU hy (fun z hz => by rw [h hz]) i

end rules



private theorem pdM_comp {V : Set (Pt n)} (hV : IsOpen V) {B : Pt n → Matrix (Fin n) (Fin n) ℝ}
    (hB : SmoothOn B V) {Φ : Pt n → Pt n} {J : Pt n → Matrix (Fin n) (Fin n) ℝ} {y : Pt n}
    (hy : Φ y ∈ V)
    (hJ : ∀ k i : Fin n, HasDerivAt (fun u : ℝ => Φ (Function.update y i u) k) (J y k i) (y i))
    (i : Fin n) : pdM i (fun z => B (Φ z)) y = ∑ e, J y e i • pdM e B (Φ y) := by
  ext a b
  simp only [pdM_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [pd_comp hV (hB a b) hy hJ i]
  exact Finset.sum_congr rfl fun e _ => mul_comm _ _




end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}



namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

private theorem jac_eq_pd (hc : CoordChange U V Φ J K) {y : Pt n} (hy : y ∈ U) (k i : Fin n) :
    J y k i = pd i (fun z => Φ z k) y :=
  (pd_eq_of_hasDerivAt (hc.jacobian y hy k i)).symm


private theorem pdM_jac_symm (hc : CoordChange U V Φ J K) {y : Pt n} (hy : y ∈ U) (p q a : Fin n) :
    pdM p J y a q = pdM q J y a p := by
  have hk : ContDiffOn ℝ ∞ (fun z => Φ z a) U := (contDiffOn_pi.mp hc.smooth) a
  simp only [pdM_apply]
  rw [pd_congr_of_eqOn hc.isOpen hy (fun z hz => hc.jac_eq_pd hz a q) p,
    pd_congr_of_eqOn hc.isOpen hy (fun z hz => hc.jac_eq_pd hz a p) q]
  exact pd_pd_symm hc.isOpen hk hy p q

end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

end MetricData







section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}


private theorem pdM_comp_metric (hc : CoordChange U V Φ J K) (hm : MetricData h hi V) {y : Pt n}
    (hy : y ∈ U) (p a b : Fin n) :
    pdM p (fun z => metricMatrix h (Φ z)) y a b = ∑ e, pd e (h a b) (Φ y) * J y e p := by
  rw [pdM_comp hc.isOpen_target hm.smoothOn (hc.mapsTo hy) (hc.jacobian y hy) p]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pdM_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_comm]
  rfl


private theorem pdM_pullback (hc : CoordChange U V Φ J K) (hm : MetricData h hi V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix h (Φ y) * J y) {y : Pt n}
    (hy : y ∈ U) (p : Fin n) :
    pdM p (metricMatrix g) y = (pdM p J y)ᵀ * metricMatrix h (Φ y) * J y
      + (J y)ᵀ * pdM p (fun z => metricMatrix h (Φ z)) y * J y
      + (J y)ᵀ * metricMatrix h (Φ y) * pdM p J y := by
  have hJs := hc.smoothOn_jac
  have hH : SmoothOn (fun z => metricMatrix h (Φ z)) U := hm.smoothOn.comp hc.smooth hc.mapsTo
  rw [pdM_congr_of_eqOn hc.isOpen hy p (B := fun z => (J z)ᵀ * metricMatrix h (Φ z) * J z)
      (fun z hz => hg z hz),
    pdM_mul hc.isOpen hy p (hJs.transpose.mul hH) hJs, pdM_mul hc.isOpen hy p hJs.transpose hH,
    pdM_transpose, add_mul]

end transform

end ExactVacuumAtlas

open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}
private theorem ExactVacuumAtlas.chr1_pullback (hc : CoordChange U V Φ J K) (hm : MetricData h hi V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix h (Φ y) * J y) {y : Pt n}
    (hy : y ∈ U) (l i j : Fin n) :
    chr1 g l i j y = ((J y)ᵀ * (metricMatrix h (Φ y) * pdM i J y + pullC h Φ J y i)) l j := by
  have hyV : Φ y ∈ V := hc.mapsTo hy
  have e0 : chr1 g l i j y = (pdM j (metricMatrix g) y l i + pdM i (metricMatrix g) y l j
      - pdM l (metricMatrix g) y i j) / 2 := rfl
  rw [e0, pdM_pullback hc hm hg hy j, pdM_pullback hc hm hg hy i, pdM_pullback hc hm hg hy l]
  have hS := s_part (Jm := J y) (hm.transpose_eq hyV) (Si := pdM i J y) (Sj := pdM j J y)
    (Sl := pdM l J y) (i := i) (j := j) (l := l)
    (fun a => hc.pdM_jac_symm hy j l a) (fun a => hc.pdM_jac_symm hy i l a)
    (fun a => hc.pdM_jac_symm hy j i a)
  have hD := d_part (Jm := J y) (D := fun a b e => pd e (h a b) (Φ y)) (i := i) (j := j) (l := l)
    (pdM i (fun z => metricMatrix h (Φ z)) y) (pdM j (fun z => metricMatrix h (Φ z)) y)
    (pdM l (fun z => metricMatrix h (Φ z)) y)
    (pdM_comp_metric hc hm hy i) (pdM_comp_metric hc hm hy j) (pdM_comp_metric hc hm hy l)
  have hR : ((J y)ᵀ * (metricMatrix h (Φ y) * pdM i J y + pullC h Φ J y i)) l j
      = ∑ a, J y a l * ∑ b, metricMatrix h (Φ y) a b * pdM i J y b j
        + ∑ a, J y a l * ∑ b, ∑ e, J y b i * J y e j *
          ((pd e (h a b) (Φ y) + pd b (h a e) (Φ y) - pd a (h b e) (Φ y)) / 2) := by
    simp only [pullC, Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply, Matrix.of_apply,
      mul_add, Finset.sum_add_distrib]
    rfl
  rw [hR]
  simp only [Matrix.add_apply]
  linear_combination (hS + hD) / 2
end


section



















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

end SmoothOn



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy

end rules



end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}




private theorem christoffel_eq_sum_chr1 (g gi : Metric n) (k i j : Fin n) (y : Pt n) :
    christoffel g gi k i j y = ∑ l, gi k l y * chr1 g l i j y := by
  unfold christoffel chr1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

end MetricData







section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end transform

end ExactVacuumAtlas

open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}
private theorem ExactVacuumAtlas.inv_mul_pullC (h hi : Metric n) (Φ : Pt n → Pt n) (J : Pt n → Matrix (Fin n) (Fin n) ℝ)
    (y : Pt n) (i : Fin n) :
    metricMatrix hi (Φ y) * pullC h Φ J y i
      = (∑ b, J y b i • connMat (christoffel h hi) b (Φ y)) * J y := by
  ext c j
  simp only [pullC, metricMatrix, Matrix.mul_apply, Matrix.of_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, connMat_apply, christoffel_eq_sum_chr1, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun e _ => ?_
  ring
end


section



















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

end SmoothOn



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy

end rules



end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}




namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

end MetricData







section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end transform

end ExactVacuumAtlas

open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}
private theorem ExactVacuumAtlas.christoffel_transform (hc : CoordChange U V Φ J K) (hm : MetricData h hi V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix h (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix hi (Φ y) * (K y)ᵀ)
    {y : Pt n} (hy : y ∈ U) (i : Fin n) :
    connMat (christoffel g gi) i y
      = ∑ e, J y e i • (K y * connMat (christoffel h hi) e (Φ y) * J y) + K y * pdM i J y := by
  have hyV := hc.mapsTo hy
  have h1 : connMat (christoffel g gi) i y
      = metricMatrix gi y * ((J y)ᵀ * (metricMatrix h (Φ y) * pdM i J y + pullC h Φ J y i)) := by
    ext k j
    rw [connMat_apply, christoffel_eq_sum_chr1, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [chr1_pullback hc hm hg hy l i j]
    rfl
  have hKJ : (K y)ᵀ * (J y)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hc.mul_inv y hy, Matrix.transpose_one]
  have hHH : metricMatrix hi (Φ y) * metricMatrix h (Φ y) = 1 := hm.inv _ hyV
  have h2 : K y * metricMatrix hi (Φ y) * (K y)ᵀ
        * ((J y)ᵀ * (metricMatrix h (Φ y) * pdM i J y + pullC h Φ J y i))
      = K y * pdM i J y + K y * (metricMatrix hi (Φ y) * pullC h Φ J y i) := by
    calc K y * metricMatrix hi (Φ y) * (K y)ᵀ
          * ((J y)ᵀ * (metricMatrix h (Φ y) * pdM i J y + pullC h Φ J y i))
        = K y * metricMatrix hi (Φ y) * ((K y)ᵀ * (J y)ᵀ)
          * (metricMatrix h (Φ y) * pdM i J y + pullC h Φ J y i) := by
          simp only [Matrix.mul_assoc]
      _ = K y * (metricMatrix hi (Φ y) * (metricMatrix h (Φ y) * pdM i J y + pullC h Φ J y i)) := by
          rw [hKJ, Matrix.mul_one, Matrix.mul_assoc]
      _ = K y * pdM i J y + K y * (metricMatrix hi (Φ y) * pullC h Φ J y i) := by
          rw [Matrix.mul_add, ← Matrix.mul_assoc (metricMatrix hi (Φ y)), hHH, Matrix.one_mul,
            Matrix.mul_add]
  rw [h1, hgi y hy, h2, inv_mul_pullC, Finset.sum_mul, Matrix.mul_sum, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
end


section











open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

private theorem pd_const (c : ℝ) (i : Fin n) (x : Pt n) : pd i (fun _ => c) x = 0 := by
  simp [pd]

end ExactVacuumAtlas

















open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
include hU hy

private theorem pd_add_of {f g : Pt n → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    pd i (fun z => f z + g z) y = pd i f y + pd i g y :=
  ((hasDerivAt_pd hU hf hy i).add (hasDerivAt_pd hU hg hy i)).deriv

end rules


end ExactVacuumAtlas


















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

private theorem smul {f : Pt n → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hA : SmoothOn A U) :
    SmoothOn (fun y => f y • A y) U :=
  fun a b => by simpa only [Matrix.smul_apply, smul_eq_mul] using hf.mul (hA a b)

private theorem sum {ι : Type*} (s : Finset ι) {A : ι → Pt n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ e ∈ s, SmoothOn (A e) U) : SmoothOn (fun y => ∑ e ∈ s, A e y) U := by
  intro a b
  simp only [Matrix.sum_apply]
  exact ContDiffOn.sum fun e he => hA e he a b

private theorem pdM (hU : IsOpen U) (hA : SmoothOn A U) (i : Fin n) : SmoothOn (fun y => pdM i A y) U :=
  fun a b => contDiffOn_pd hU (hA a b) i

end SmoothOn



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy

private theorem pdM_add (hA : SmoothOn A U) (hB : SmoothOn B U) :
    pdM i (fun z => A z + B z) y = pdM i A y + pdM i B y := by
  ext a b
  simp only [pdM_apply, Matrix.add_apply]
  exact pd_add_of hU hy i (hA a b) (hB a b)


private theorem pdM_smul {f : Pt n → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hA : SmoothOn A U) :
    pdM i (fun z => f z • A z) y = pd i f y • A y + f y • pdM i A y := by
  ext a b
  simp only [pdM_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  exact pd_mul_of hU hy i hf (hA a b)

private theorem pdM_sum {ι : Type*} (s : Finset ι) {A : ι → Pt n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ e ∈ s, SmoothOn (A e) U) :
    pdM i (fun z => ∑ e ∈ s, A e z) y = ∑ e ∈ s, pdM i (A e) y := by
  ext a b
  simp only [pdM_apply, Matrix.sum_apply]
  exact pd_sum_of hU hy i s fun e he => hA e he a b

private theorem pdM_inv {J K : Pt n → Matrix (Fin n) (Fin n) ℝ} (hJ : SmoothOn J U) (hK : SmoothOn K U)
    (hKJ : ∀ z ∈ U, K z * J z = 1) (hJK : J y * K y = 1) :
    pdM i K y = -(K y * pdM i J y * K y) := by
  have h0 : pdM i (fun z => K z * J z) y = 0 := by
    rw [pdM_congr_of_eqOn hU hy i (B := fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) fun z hz => hKJ z hz]
    ext a b
    simp only [pdM_apply, Matrix.zero_apply]
    exact pd_const _ i y
  rw [pdM_mul hU hy i hK hJ] at h0
  calc pdM i K y = pdM i K y * (J y * K y) := by rw [hJK, mul_one]
    _ = (pdM i K y * J y) * K y := by rw [mul_assoc]
    _ = (-(K y * pdM i J y)) * K y := by rw [eq_neg_of_add_eq_zero_left h0]
    _ = -(K y * pdM i J y * K y) := by rw [neg_mul]


private theorem pdM_pdM_symm (hA : SmoothOn A U) (c d : Fin n) :
    pdM c (fun z => pdM d A z) y = pdM d (fun z => pdM c A z) y := by
  ext a b
  simp only [pdM_apply]
  exact pd_pd_symm hU (hA a b) hy c d

end rules



end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}



namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

private theorem pdM_inv_eq (hc : CoordChange U V Φ J K) {y : Pt n} (hy : y ∈ U) (i : Fin n) :
    pdM i K y = -(K y * pdM i J y * K y) :=
  pdM_inv hc.isOpen hy i hc.smoothOn_jac hc.smoothOn_inv (fun z hz => hc.inv_mul hz)
    (hc.mul_inv y hy)

end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

end MetricData







section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end transform

end ExactVacuumAtlas

















open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}



private theorem curv_core {K J Ac Ad Sc Sd Scd Acd Adc : Matrix (Fin n) (Fin n) ℝ} (hJK : J * K = 1) :
    (-(K * Sc * K) * Ad * J + K * Acd * J + K * Ad * Sc + -(K * Sc * K) * Sd + K * Scd)
      - (-(K * Sd * K) * Ac * J + K * Adc * J + K * Ac * Sd + -(K * Sd * K) * Sc + K * Scd)
      + (K * Ac * J + K * Sc) * (K * Ad * J + K * Sd)
      - (K * Ad * J + K * Sd) * (K * Ac * J + K * Sc)
      = K * (Acd - Adc + Ac * Ad - Ad * Ac) * J := by
  have hJK' : ∀ X : Matrix (Fin n) (Fin n) ℝ, J * (K * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJK, Matrix.one_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, Matrix.mul_assoc, hJK']
  abel

section
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

private theorem smoothOn_pullConn (hc : CoordChange U V Φ J K) {Γ : Fin n → Pt n → Matrix (Fin n) (Fin n) ℝ}
    (hΓ : ∀ e, SmoothOn (Γ e) V) (d : Fin n) : SmoothOn (pullConn J Γ Φ d) U :=
  SmoothOn.sum Finset.univ fun f _ =>
    SmoothOn.smul (hc.smoothOn_jac f d) ((hΓ f).comp hc.smooth hc.mapsTo)


private theorem pdM_pullConn (hc : CoordChange U V Φ J K) {Γ : Fin n → Pt n → Matrix (Fin n) (Fin n) ℝ}
    (hΓ : ∀ e, SmoothOn (Γ e) V) {y : Pt n} (hy : y ∈ U) (c d : Fin n) :
    pdM c (pullConn J Γ Φ d) y
      = ∑ f, (pdM c J y f d • Γ f (Φ y) + J y f d • ∑ e, J y e c • pdM e (Γ f) (Φ y)) := by
  have hU := hc.isOpen
  have hJs := hc.smoothOn_jac
  unfold pullConn
  rw [pdM_sum hU hy c Finset.univ
    (fun f _ => SmoothOn.smul (hJs f d) ((hΓ f).comp hc.smooth hc.mapsTo))]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [pdM_smul hU hy c (hJs f d) ((hΓ f).comp hc.smooth hc.mapsTo),
    pdM_comp hc.isOpen_target (hΓ f) (hc.mapsTo hy) (hc.jacobian y hy) c]
  rfl

end

end ExactVacuumAtlas

open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
private theorem ExactVacuumAtlas.curv_transform (hc : CoordChange U V Φ J K)
    {Γ Γ' : Fin n → Pt n → Matrix (Fin n) (Fin n) ℝ} (hΓ : ∀ e, SmoothOn (Γ e) V)
    (hΓ' : ∀ y ∈ U, ∀ i, Γ' i y = ∑ e, J y e i • (K y * Γ e (Φ y) * J y) + K y * pdM i J y)
    {y : Pt n} (hy : y ∈ U) (c d : Fin n) :
    curv Γ' c d y = ∑ e, ∑ f, (J y e c * J y f d) • (K y * curv Γ e f (Φ y) * J y) := by
  have hU := hc.isOpen
  have hJs := hc.smoothOn_jac
  have hKs := hc.smoothOn_inv
  have hAs : ∀ d, SmoothOn (pullConn J Γ Φ d) U := smoothOn_pullConn hc hΓ
  have hΓ'' : ∀ d, Set.EqOn (Γ' d)
      (fun z => K z * pullConn J Γ Φ d z * J z + K z * pdM d J z) U := by
    intro d z hz
    rw [hΓ' z hz d]
    simp only [pullConn, Matrix.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
  have hpd : ∀ d c, pdM c (Γ' d) y
      = -(K y * pdM c J y * K y) * pullConn J Γ Φ d y * J y
        + K y * pdM c (pullConn J Γ Φ d) y * J y + K y * pullConn J Γ Φ d y * pdM c J y
        + -(K y * pdM c J y * K y) * pdM d J y + K y * pdM c (fun z => pdM d J z) y := by
    intro d c
    rw [pdM_congr_of_eqOn hU hy c (hΓ'' d),
      pdM_add hU hy c ((hKs.mul (hAs d)).mul hJs) (hKs.mul (hJs.pdM hU d)),
      pdM_mul hU hy c (hKs.mul (hAs d)) hJs, pdM_mul hU hy c hKs (hAs d),
      pdM_mul hU hy c hKs (hJs.pdM hU d), hc.pdM_inv_eq hy c]
    simp only [add_mul]
    abel
  have hsymm : pdM d (fun z => pdM c J z) y = pdM c (fun z => pdM d J z) y :=
    pdM_pdM_symm hU hy hJs d c
  have hin : pdM c (pullConn J Γ Φ d) y - pdM d (pullConn J Γ Φ c) y
      + pullConn J Γ Φ c y * pullConn J Γ Φ d y - pullConn J Γ Φ d y * pullConn J Γ Φ c y
      = ∑ e, ∑ f, (J y e c * J y f d) • curv Γ e f (Φ y) := by
    rw [pdM_pullConn hc hΓ hy c d, pdM_pullConn hc hΓ hy d c]
    have hS0 : ∑ f, (pdM c J y f d • Γ f (Φ y) + J y f d • ∑ e, J y e c • pdM e (Γ f) (Φ y))
        - ∑ f, (pdM d J y f c • Γ f (Φ y) + J y f c • ∑ e, J y e d • pdM e (Γ f) (Φ y))
        = ∑ e, ∑ f, (J y e c * J y f d) • pdM e (Γ f) (Φ y)
          - ∑ e, ∑ f, (J y e c * J y f d) • pdM f (Γ e) (Φ y) := by
      simp only [Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
      have e1 : ∑ f, pdM c J y f d • Γ f (Φ y) = ∑ f, pdM d J y f c • Γ f (Φ y) :=
        Finset.sum_congr rfl fun f _ => by rw [hc.pdM_jac_symm hy c d f]
      have e2 : ∑ f, ∑ e, (J y f d * J y e c) • pdM e (Γ f) (Φ y)
          = ∑ e, ∑ f, (J y e c * J y f d) • pdM e (Γ f) (Φ y) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => by rw [mul_comm]
      have e3 : ∑ f, ∑ e, (J y f c * J y e d) • pdM e (Γ f) (Φ y)
          = ∑ e, ∑ f, (J y e c * J y f d) • pdM f (Γ e) (Φ y) := rfl
      rw [e1, e2, e3]
      abel
    have hP1 : pullConn J Γ Φ c y * pullConn J Γ Φ d y
        = ∑ e, ∑ f, (J y e c * J y f d) • (Γ e (Φ y) * Γ f (Φ y)) := by
      unfold pullConn
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Matrix.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hP2 : pullConn J Γ Φ d y * pullConn J Γ Φ c y
        = ∑ e, ∑ f, (J y e c * J y f d) • (Γ f (Φ y) * Γ e (Φ y)) := by
      unfold pullConn
      rw [Finset.sum_mul]
      simp only [Matrix.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
    rw [add_sub_assoc, hS0, hP1, hP2]
    simp only [curv, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    abel
  show pdM c (Γ' d) y - pdM d (Γ' c) y + Γ' c y * Γ' d y - Γ' d y * Γ' c y = _
  rw [hpd d c, hpd c d, hΓ'' c hy, hΓ'' d hy, hsymm,
    curv_core (Ac := pullConn J Γ Φ c y) (Ad := pullConn J Γ Φ d y) (hc.mul_inv y hy), hin,
    Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]
end


section



















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

end SmoothOn



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy

end rules



end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}



namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

end MetricData







section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end transform

end ExactVacuumAtlas

open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}
private theorem ExactVacuumAtlas.ricci_eq_contr_curv {Γ : Fin n → Fin n → Fin n → Pt n → ℝ} {U : Set (Pt n)} (hU : IsOpen U)
    (hΓ : ∀ x ∈ U, ∀ a b c, Γ a b c x = Γ a c b x) {y : Pt n} (hy : y ∈ U) (b d : Fin n) :
    ricci Γ b d y = ∑ i, curv (connMat Γ) i d y i b := by
  unfold ricci curv
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, pdM_apply, connMat_apply]
  rw [pd_congr_of_eqOn hU hy (fun x hx => hΓ x hx i d b) i,
    pd_congr_of_eqOn hU hy (fun x hx => hΓ x hx i i b) d, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hΓ y hy e d b, hΓ y hy e i b]
end


section











open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

private theorem contDiffOn_christoffel {g ginv : Metric n} {U : Set (Pt n)} (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (g i j) U) (hgi : ∀ i j, ContDiffOn ℝ ∞ (ginv i j) U)
    (a b c : Fin n) : ContDiffOn ℝ ∞ (christoffel g ginv a b c) U := by
  have e : christoffel g ginv a b c = fun x =>
      (∑ k : Fin n, ginv a k x * (pd c (g k b) x + pd b (g k c) x - pd k (g b c) x)) / 2 := rfl
  rw [e]
  apply ContDiffOn.div_const
  apply ContDiffOn.sum
  intro k _
  exact (hgi a k).mul (((contDiffOn_pd hU (hg k b) c).add (contDiffOn_pd hU (hg k c) b)).sub
    (contDiffOn_pd hU (hg b c) k))

end ExactVacuumAtlas


















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

end SmoothOn



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy

end rules



end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}



namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

private theorem christoffel_symm (hm : MetricData g gi U) {y : Pt n} (hy : y ∈ U) (a b c : Fin n) :
    christoffel g gi a b c y = christoffel g gi a c b y := by
  unfold christoffel
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pd_congr_of_eqOn hm.isOpen hy (fun x hx => hm.symm x hx b c) k]
  ring

private theorem smoothOn_connMat (hm : MetricData g gi U) (c : Fin n) :
    SmoothOn (connMat (christoffel g gi) c) U :=
  fun a b => contDiffOn_christoffel hm.isOpen hm.smooth hm.smooth_inv a c b

end MetricData







section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end transform

end ExactVacuumAtlas




















open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}

section
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end

end ExactVacuumAtlas

open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}
private theorem ExactVacuumAtlas.ricciOf_transform (hc : CoordChange U V Φ J K) (hm : MetricData h hi V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix h (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix hi (Φ y) * (K y)ᵀ)
    {y : Pt n} (hy : y ∈ U) (i j : Fin n) :
    ricciOf g gi i j y = ∑ a, ∑ b, J y a i * J y b j * ricciOf h hi a b (Φ y) := by
  have hyV := hc.mapsTo hy
  have hmg : MetricData g gi U := MetricData.transport hc hm hg hgi
  have hΓ' : ∀ x ∈ U, ∀ k, connMat (christoffel g gi) k x
      = ∑ e, J x e k • (K x * connMat (christoffel h hi) e (Φ x) * J x) + K x * pdM k J x :=
    fun x hx k => christoffel_transform hc hm hg hgi hx k
  have hJK := hc.mul_inv y hy
  show ricci (christoffel g gi) i j y = _
  rw [ricci_eq_contr_curv hc.isOpen (fun x hx a b c => hmg.christoffel_symm hx a b c) hy i j]
  simp only [curv_transform hc hm.smoothOn_connMat hΓ' hy, ricciOf,
    ricci_eq_contr_curv hc.isOpen_target (fun x hx a b c => hm.christoffel_symm hx a b c) hyV,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hk : ∀ e f, ∑ k, (J y e k * J y f j) * (K y * curv (connMat (christoffel h hi)) e f (Φ y) * J y) k i
      = J y f j * ∑ p, curv (connMat (christoffel h hi)) e f (Φ y) e p * J y p i := by
    intro e f
    calc ∑ k, (J y e k * J y f j) * (K y * curv (connMat (christoffel h hi)) e f (Φ y) * J y) k i
        = J y f j * ∑ k, J y e k * (K y * curv (connMat (christoffel h hi)) e f (Φ y) * J y) k i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = J y f j * (J y * (K y * curv (connMat (christoffel h hi)) e f (Φ y) * J y)) e i := by
          rw [Matrix.mul_apply]
      _ = J y f j * (curv (connMat (christoffel h hi)) e f (Φ y) * J y) e i := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJK, Matrix.one_mul]
      _ = J y f j * ∑ p, curv (connMat (christoffel h hi)) e f (Φ y) e p * J y p i := by
          rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun e _ => Finset.sum_comm).trans ?_
  simp only [hk]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun f _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun f _ =>
    Finset.sum_congr rfl fun e _ => ?_
  ring
end


section



















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

end SmoothOn



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy

end rules



end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}



namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

end MetricData







section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end transform

end ExactVacuumAtlas






















open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell

namespace ExactVacuumAtlas.Variation

variable {n : ℕ}



private theorem raise2_matrix (gi : Metric n) (F : TwoForm n) (y : Pt n) :
    Matrix.of (fun a b => raise2 gi F a b y) = metricMatrix gi y * metricMatrix F y * (metricMatrix gi y)ᵀ := by
  ext a b
  simp only [Matrix.of_apply, raise2, Matrix.mul_apply, metricMatrix, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

private theorem sandwich_matrix (F : TwoForm n) (gi : Metric n) (y : Pt n) :
    Matrix.of (fun a b => ∑ c, ∑ d, F a c y * gi c d y * F b d y) =
      metricMatrix F y * metricMatrix gi y * (metricMatrix F y)ᵀ := by
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, metricMatrix, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem congr_entry (J R : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Jᵀ * R * J) i j = ∑ a, ∑ b, J a i * J b j * R a b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private theorem sum_sum_mul_eq_trace (X Y : Matrix (Fin n) (Fin n) ℝ) :
    ∑ a, ∑ b, X a b * Y a b = (X * Yᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]

private theorem trace_congr_pair {J K A B : Matrix (Fin n) (Fin n) ℝ} (hJK : J * K = 1) :
    ((K * A * Kᵀ) * (Jᵀ * B * J)ᵀ).trace = (A * Bᵀ).trace := by
  have h2 : ∀ X : Matrix (Fin n) (Fin n) ℝ, Kᵀ * (Jᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hJK, Matrix.transpose_one, Matrix.one_mul]
  have e : (K * A * Kᵀ) * (Jᵀ * B * J)ᵀ = K * (A * (Bᵀ * J)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, h2]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hJK, Matrix.mul_one]





section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {gV giV : Metric n} {FV : TwoForm n} {g gi : Metric n} {F : TwoForm n}

private theorem raise2_transform (hc : CoordChange U V Φ J K)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix giV (Φ y) * (K y)ᵀ)
    (hF : ∀ y ∈ U, metricMatrix F y = (J y)ᵀ * metricMatrix FV (Φ y) * J y) {y : Pt n} (hy : y ∈ U) :
    Matrix.of (fun a b => raise2 gi F a b y) =
      K y * Matrix.of (fun a b => raise2 giV FV a b (Φ y)) * (K y)ᵀ := by
  have hJK := hc.mul_inv y hy
  have h1 : ∀ X : Matrix (Fin n) (Fin n) ℝ, J y * (K y * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJK, Matrix.one_mul]
  have h2 : ∀ X : Matrix (Fin n) (Fin n) ℝ, (K y)ᵀ * ((J y)ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hJK, Matrix.transpose_one, Matrix.one_mul]
  rw [raise2_matrix, raise2_matrix, hgi y hy, hF y hy]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, h1, h2]

private theorem fieldSq_transform (hc : CoordChange U V Φ J K)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix giV (Φ y) * (K y)ᵀ)
    (hF : ∀ y ∈ U, metricMatrix F y = (J y)ᵀ * metricMatrix FV (Φ y) * J y) {y : Pt n} (hy : y ∈ U) :
    fieldSq gi F y = fieldSq giV FV (Φ y) := by
  have e : ∀ (gi : Metric n) (F : TwoForm n) (z : Pt n), fieldSq gi F z =
      ((Matrix.of fun a b => raise2 gi F a b z) * (metricMatrix F z)ᵀ).trace := by
    intro gi F z
    rw [← sum_sum_mul_eq_trace]
    unfold fieldSq
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [e, e, raise2_transform hc hgi hF hy, hF y hy]
  exact trace_congr_pair (hc.mul_inv y hy)

private theorem ricci_matrix_transform (hc : CoordChange U V Φ J K) (hm : MetricData gV giV V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix gV (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix giV (Φ y) * (K y)ᵀ) {y : Pt n} (hy : y ∈ U) :
    Matrix.of (fun a b => ricciOf g gi a b y) = (J y)ᵀ * Matrix.of (fun a b => ricciOf gV giV a b (Φ y)) * J y := by
  ext i j
  rw [Matrix.of_apply, ricciOf_transform hc hm hg hgi hy i j, congr_entry]
  rfl

private theorem ricciScalar_transform (hc : CoordChange U V Φ J K) (hm : MetricData gV giV V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix gV (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix giV (Φ y) * (K y)ᵀ) {y : Pt n} (hy : y ∈ U) :
    ricciScalar g gi y = ricciScalar gV giV (Φ y) := by
  have e : ∀ (g gi : Metric n) (z : Pt n), ricciScalar g gi z =
      (metricMatrix gi z * (Matrix.of fun a b => ricciOf g gi a b z)ᵀ).trace := by
    intro g gi z
    rw [← sum_sum_mul_eq_trace]
    rfl
  rw [e, e, ricci_matrix_transform hc hm hg hgi hy, hgi y hy]
  exact trace_congr_pair (hc.mul_inv y hy)

end transform

section transform4

variable {U V : Set (Pt 4)} {Φ : Pt 4 → Pt 4} {J K : Pt 4 → Matrix (Fin 4) (Fin 4) ℝ}
  {gV giV : Metric 4} {FV : TwoForm 4} {g gi : Metric 4} {F : TwoForm 4}

private theorem emStress_matrix (g gi : Metric 4) (F : TwoForm 4) (y : Pt 4) :
    Matrix.of (fun a b => emStress g gi F a b y) =
      metricMatrix F y * metricMatrix gi y * (metricMatrix F y)ᵀ - (fieldSq gi F y / 4) • metricMatrix g y := by
  rw [← sandwich_matrix]
  ext a b
  simp only [Matrix.of_apply, emStress, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, metricMatrix]
  ring

private theorem emStress_transform (hc : CoordChange U V Φ J K)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix gV (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix giV (Φ y) * (K y)ᵀ)
    (hF : ∀ y ∈ U, metricMatrix F y = (J y)ᵀ * metricMatrix FV (Φ y) * J y) {y : Pt 4} (hy : y ∈ U) :
    Matrix.of (fun a b => emStress g gi F a b y) =
      (J y)ᵀ * Matrix.of (fun a b => emStress gV giV FV a b (Φ y)) * J y := by
  have hJK := hc.mul_inv y hy
  have h1 : ∀ X : Matrix (Fin 4) (Fin 4) ℝ, J y * (K y * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJK, Matrix.one_mul]
  have h2 : ∀ X : Matrix (Fin 4) (Fin 4) ℝ, (K y)ᵀ * ((J y)ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hJK, Matrix.transpose_one, Matrix.one_mul]
  rw [emStress_matrix, emStress_matrix, fieldSq_transform hc hgi hF hy, hF y hy, hgi y hy, hg y hy]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h1, h2]

private theorem einsteinMaxwell_matrix (g gi : Metric 4) (F : TwoForm 4) (y : Pt 4) :
    Matrix.of (fun a b => einsteinMaxwell g gi F a b y) =
      Matrix.of (fun a b => ricciOf g gi a b y) - (ricciScalar g gi y / 2) • metricMatrix g y -
        (2 : ℝ) • Matrix.of (fun a b => emStress g gi F a b y) := by
  ext a b
  simp only [Matrix.of_apply, einsteinMaxwell, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, metricMatrix]
  ring

end transform4



section closure

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {FV F : TwoForm n}

end closure



end ExactVacuumAtlas.Variation

open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {n : ℕ}
variable {U V : Set (Pt 4)} {Φ : Pt 4 → Pt 4} {J K : Pt 4 → Matrix (Fin 4) (Fin 4) ℝ}
  {gV giV : Metric 4} {FV : TwoForm 4} {g gi : Metric 4} {F : TwoForm 4}
private theorem ExactVacuumAtlas.Variation.einsteinMaxwell_transform (hc : CoordChange U V Φ J K) (hm : MetricData gV giV V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix gV (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix giV (Φ y) * (K y)ᵀ)
    (hF : ∀ y ∈ U, metricMatrix F y = (J y)ᵀ * metricMatrix FV (Φ y) * J y) {y : Pt 4} (hy : y ∈ U) :
    Matrix.of (fun a b => einsteinMaxwell g gi F a b y) =
      (J y)ᵀ * Matrix.of (fun a b => einsteinMaxwell gV giV FV a b (Φ y)) * J y := by
  rw [einsteinMaxwell_matrix, einsteinMaxwell_matrix, ricci_matrix_transform hc hm hg hgi hy,
    ricciScalar_transform hc hm hg hgi hy, emStress_transform hc hg hgi hF hy, hg y hy]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
end


section



















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

end SmoothOn



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy

end rules



end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}



namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

end MetricData







section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end transform

end ExactVacuumAtlas






















open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell

namespace ExactVacuumAtlas.Variation

variable {n : ℕ}







section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {gV giV : Metric n} {FV : TwoForm n} {g gi : Metric n} {F : TwoForm n}

end transform

section transform4

variable {U V : Set (Pt 4)} {Φ : Pt 4 → Pt 4} {J K : Pt 4 → Matrix (Fin 4) (Fin 4) ℝ}
  {gV giV : Metric 4} {FV : TwoForm 4} {g gi : Metric 4} {F : TwoForm 4}

end transform4



section closure

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {FV F : TwoForm n}

end closure



end ExactVacuumAtlas.Variation

open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {n : ℕ}
private theorem ExactVacuumAtlas.Variation.contract_core {Jm Km : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hJK : Jm * Km = 1) (b : Fin n) :
    ∑ a, (∑ e, Jm e a • (Km * X e * Kmᵀ)) a b = ∑ q, Km b q * ∑ e, X e e q := by
  have h1 : ∀ e, ∑ a, Jm e a * (Km * X e * Kmᵀ) a b = (X e * Kmᵀ) e b := by
    intro e
    have : Jm * (Km * X e * Kmᵀ) = X e * Kmᵀ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJK, Matrix.one_mul]
    rw [← this, Matrix.mul_apply]
  calc ∑ a, (∑ e, Jm e a • (Km * X e * Kmᵀ)) a b = ∑ e, ∑ a, Jm e a * (Km * X e * Kmᵀ) a b := by
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        exact Finset.sum_comm
    _ = ∑ e, (X e * Kmᵀ) e b := Finset.sum_congr rfl fun e _ => h1 e
    _ = ∑ e, ∑ q, X e e q * Km b q := by simp only [Matrix.mul_apply, Matrix.transpose_apply]
    _ = ∑ q, Km b q * ∑ e, X e e q := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring
end


section



















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

end SmoothOn



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy

end rules



end ExactVacuumAtlas

open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}
end


section











open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

end ExactVacuumAtlas

















open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
include hU hy

end rules

end ExactVacuumAtlas


















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

end SmoothOn

section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy


end rules



end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}



namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

end MetricData







section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end transform

end ExactVacuumAtlas






















open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell

namespace ExactVacuumAtlas.Variation

variable {n : ℕ}



private theorem div_core {Km Jm Um DJ : Matrix (Fin n) (Fin n) ℝ} {DU Γ : Fin n → Matrix (Fin n) (Fin n) ℝ}
    {c : Fin n → ℝ} (hJK : Jm * Km = 1) :
    (-(Km * DJ * Km) * Um + Km * ∑ e, c e • DU e) * Kmᵀ + Km * Um * (-(Km * DJ * Km))ᵀ +
        (∑ e, c e • (Km * Γ e * Jm) + Km * DJ) * (Km * Um * Kmᵀ) +
        Km * Um * Kmᵀ * (∑ e, c e • (Km * Γ e * Jm) + Km * DJ)ᵀ =
      ∑ e, c e • (Km * (DU e + Γ e * Um + Um * (Γ e)ᵀ) * Kmᵀ) := by
  have h1 : ∀ X : Matrix (Fin n) (Fin n) ℝ, Jm * (Km * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJK, Matrix.one_mul]
  have h2 : ∀ X : Matrix (Fin n) (Fin n) ℝ, Kmᵀ * (Jmᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hJK, Matrix.transpose_one, Matrix.one_mul]
  simp only [Matrix.transpose_add, Matrix.transpose_neg, Matrix.transpose_mul,
    Matrix.transpose_sum, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul,
    Matrix.mul_neg, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
    h1, h2, smul_add, Finset.sum_add_distrib]
  abel



private theorem maxwellDiv_eq_entry (g gi : Metric n) (F : TwoForm n) (b : Fin n) (y : Pt n) :
    maxwellDiv g gi F b y = ∑ a, (pdM a (fun z => Matrix.of fun a b => raise2 gi F a b z) y +
      connMat (christoffel g gi) a y * Matrix.of (fun a b => raise2 gi F a b y) +
      Matrix.of (fun a b => raise2 gi F a b y) * (connMat (christoffel g gi) a y)ᵀ) a b := by
  unfold maxwellDiv
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.add_apply, Matrix.mul_apply, connMat_apply, Matrix.transpose_apply, pdM_apply,
    Matrix.of_apply, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring



section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {gV giV : Metric n} {FV : TwoForm n} {g gi : Metric n} {F : TwoForm n}

end transform

section transform4

variable {U V : Set (Pt 4)} {Φ : Pt 4 → Pt 4} {J K : Pt 4 → Matrix (Fin 4) (Fin 4) ℝ}
  {gV giV : Metric 4} {FV : TwoForm 4} {g gi : Metric 4} {F : TwoForm 4}

end transform4



section closure

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {FV F : TwoForm n}

end closure



end ExactVacuumAtlas.Variation

open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {n : ℕ}
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {gV giV : Metric n} {FV : TwoForm n} {g gi : Metric n} {F : TwoForm n}
private theorem ExactVacuumAtlas.Variation.maxwellDiv_transform (hc : CoordChange U V Φ J K) (hm : MetricData gV giV V)
    (hFs : ∀ i j, ContDiffOn ℝ ∞ (FV i j) V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix gV (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix giV (Φ y) * (K y)ᵀ)
    (hF : ∀ y ∈ U, metricMatrix F y = (J y)ᵀ * metricMatrix FV (Φ y) * J y) {y : Pt n} (hy : y ∈ U)
    (b : Fin n) :
    maxwellDiv g gi F b y = ∑ q, K y b q * maxwellDiv gV giV FV q (Φ y) := by
  have hyV := hc.mapsTo hy
  have hUs : SmoothOn (fun z => Matrix.of fun a b => raise2 giV FV a b z) V := by
    intro a b
    simp only [Matrix.of_apply]
    unfold raise2
    exact ContDiffOn.sum fun c _ => ContDiffOn.sum fun d _ =>
      ((hm.smooth_inv a c).mul (hm.smooth_inv b d)).mul (hFs c d)
  have hKs := hc.smoothOn_inv
  have hUΦ : SmoothOn (fun z => Matrix.of (fun a b => raise2 giV FV a b (Φ z))) U :=
    hUs.comp hc.smooth hc.mapsTo
  have hU' : Set.EqOn (fun z => Matrix.of fun a b => raise2 gi F a b z)
      (fun z => K z * Matrix.of (fun a b => raise2 giV FV a b (Φ z)) * (K z)ᵀ) U :=
    fun z hz => raise2_transform hc hgi hF hz
  have key : ∀ a, pdM a (fun z => Matrix.of fun a b => raise2 gi F a b z) y +
      connMat (christoffel g gi) a y * Matrix.of (fun a b => raise2 gi F a b y) +
      Matrix.of (fun a b => raise2 gi F a b y) * (connMat (christoffel g gi) a y)ᵀ =
      ∑ e, J y e a • (K y * (pdM e (fun z => Matrix.of fun a b => raise2 giV FV a b z) (Φ y) +
        connMat (christoffel gV giV) e (Φ y) * Matrix.of (fun a b => raise2 giV FV a b (Φ y)) +
        Matrix.of (fun a b => raise2 giV FV a b (Φ y)) * (connMat (christoffel gV giV) e (Φ y))ᵀ) * (K y)ᵀ) := by
    intro a
    rw [pdM_congr_of_eqOn hc.isOpen hy a hU', pdM_mul hc.isOpen hy a (hKs.mul hUΦ) hKs.transpose,
      pdM_mul hc.isOpen hy a hKs hUΦ, pdM_transpose, hc.pdM_inv_eq hy a,
      pdM_comp hc.isOpen_target hUs hyV (hc.jacobian y hy) a, christoffel_transform hc hm hg hgi hy a,
      raise2_transform hc hgi hF hy]
    exact div_core (hc.mul_inv y hy)
  rw [maxwellDiv_eq_entry]
  simp only [key]
  rw [contract_core (hc.mul_inv y hy) b]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [maxwellDiv_eq_entry]
end


section











open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

end ExactVacuumAtlas

















open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
include hU hy

end rules

end ExactVacuumAtlas


















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

end SmoothOn



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy

end rules




end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}



namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

end MetricData







section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end transform

end ExactVacuumAtlas






















open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell

namespace ExactVacuumAtlas.Variation

variable {n : ℕ}



section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {gV giV : Metric n} {FV : TwoForm n} {g gi : Metric n} {F : TwoForm n}

end transform

section transform4

variable {U V : Set (Pt 4)} {Φ : Pt 4 → Pt 4} {J K : Pt 4 → Matrix (Fin 4) (Fin 4) ℝ}
  {gV giV : Metric 4} {FV : TwoForm 4} {g gi : Metric 4} {F : TwoForm 4}

end transform4



section closure

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {FV F : TwoForm n}

end closure



end ExactVacuumAtlas.Variation

open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {n : ℕ}
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {FV F : TwoForm n}
private theorem ExactVacuumAtlas.Variation.pd_pullback2 (hc : CoordChange U V Φ J K) (hFs : ∀ i j, ContDiffOn ℝ ∞ (FV i j) V)
    (hF : ∀ y ∈ U, metricMatrix F y = (J y)ᵀ * metricMatrix FV (Φ y) * J y) {y : Pt n} (hy : y ∈ U)
    (a b c : Fin n) :
    pd a (F b c) y = ∑ p, ∑ q, (pdM a J y p b * FV p q (Φ y) * J y q c +
      J y p b * (∑ e, pd e (FV p q) (Φ y) * J y e a) * J y q c + J y p b * FV p q (Φ y) * pdM a J y q c) := by
  have hU := hc.isOpen
  have hJs := hc.smoothOn_jac
  have hFΦ : ∀ p q, ContDiffOn ℝ ∞ (fun z => FV p q (Φ z)) U := fun p q => (hFs p q).comp hc.smooth hc.mapsTo
  have heq : Set.EqOn (F b c) (fun z => ∑ p, ∑ q, J z p b * FV p q (Φ z) * J z q c) U := by
    intro z hz
    have := congrFun (congrFun (hF z hz) b) c
    simp only [metricMatrix, Matrix.of_apply] at this
    rw [this, congr_entry]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by simp only [Matrix.of_apply]; ring
  rw [pd_congr_of_eqOn hU hy heq a]
  rw [pd_sum_of hU hy a Finset.univ fun p _ => ContDiffOn.sum fun q _ => ((hJs p b).mul (hFΦ p q)).mul (hJs q c)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [pd_sum_of hU hy a Finset.univ fun q _ => ((hJs p b).mul (hFΦ p q)).mul (hJs q c)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [pd_mul_of hU hy a ((hJs p b).mul (hFΦ p q)) (hJs q c), pd_mul_of hU hy a (hJs p b) (hFΦ p q),
    pd_comp hc.isOpen_target (hFs p q) (hc.mapsTo hy) (hc.jacobian y hy) a]
  simp only [pdM_apply]
  ring
end


section











open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

end ExactVacuumAtlas

















open Filter Topology
open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
include hU hy

end rules


end ExactVacuumAtlas


















open scoped ContDiff

namespace ExactVacuumAtlas

variable {n : ℕ}

namespace SmoothOn

variable {U V : Set (Pt n)} {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}

end SmoothOn



section rules

variable {U : Set (Pt n)} (hU : IsOpen U) {y : Pt n} (hy : y ∈ U) (i : Fin n)
  {A B : Pt n → Matrix (Fin n) (Fin n) ℝ}
include hU hy

end rules



end ExactVacuumAtlas

























open scoped ContDiff
open Matrix

namespace ExactVacuumAtlas

variable {n : ℕ}



namespace CoordChange

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}


end CoordChange

namespace MetricData

variable {g gi : Metric n} {U : Set (Pt n)}

end MetricData







section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

end transform

end ExactVacuumAtlas






















open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell

namespace ExactVacuumAtlas.Variation

variable {n : ℕ}






private theorem sum_rot3 (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ x, ∑ y, ∑ z, f y z x := by
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]

private theorem sum_rot3_prime (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ x, ∑ y, ∑ z, f z x y :=
  (sum_rot3 f).trans (sum_rot3 fun x y z => f y z x)



section transform

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {gV giV : Metric n} {FV : TwoForm n} {g gi : Metric n} {F : TwoForm n}

end transform

section transform4

variable {U V : Set (Pt 4)} {Φ : Pt 4 → Pt 4} {J K : Pt 4 → Matrix (Fin 4) (Fin 4) ℝ}
  {gV giV : Metric 4} {FV : TwoForm 4} {g gi : Metric 4} {F : TwoForm 4}

end transform4



section closure

variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {FV F : TwoForm n}

end closure



end ExactVacuumAtlas.Variation

open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {n : ℕ}
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {FV F : TwoForm n}
private theorem ExactVacuumAtlas.Variation.faradayCyclic_transform (hc : CoordChange U V Φ J K) (hFs : ∀ i j, ContDiffOn ℝ ∞ (FV i j) V)
    (hFa : ∀ x ∈ V, ∀ i j, FV i j x = -FV j i x)
    (hF : ∀ y ∈ U, metricMatrix F y = (J y)ᵀ * metricMatrix FV (Φ y) * J y) {y : Pt n} (hy : y ∈ U)
    (a b c : Fin n) :
    faradayCyclic F a b c y =
      ∑ e, ∑ p, ∑ q, J y e a * J y p b * J y q c * faradayCyclic FV e p q (Φ y) := by
  have hyV := hc.mapsTo hy
  have pair : ∀ a b c : Fin n, ∑ p, ∑ q, pdM a J y p b * FV p q (Φ y) * J y q c +
      ∑ p, ∑ q, J y p c * FV p q (Φ y) * pdM b J y q a = 0 := by
    intro a b c
    rw [Finset.sum_comm (f := fun p q => J y p c * FV p q (Φ y) * pdM b J y q a), ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [hFa _ hyV q p, hc.pdM_jac_symm hy b a p]
    ring
  have tri : ∀ a b c : Fin n, ∑ p, ∑ q, J y p b * (∑ e, pd e (FV p q) (Φ y) * J y e a) * J y q c =
      ∑ e, ∑ p, ∑ q, J y e a * J y p b * J y q c * pd e (FV p q) (Φ y) := by
    intro a b c
    rw [sum_rot3_prime (fun e p q => J y e a * J y p b * J y q c * pd e (FV p q) (Φ y))]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by ring
  have split : ∀ a b c : Fin n, pd a (F b c) y =
      ∑ p, ∑ q, pdM a J y p b * FV p q (Φ y) * J y q c +
      ∑ e, ∑ p, ∑ q, J y e a * J y p b * J y q c * pd e (FV p q) (Φ y) +
      ∑ p, ∑ q, J y p b * FV p q (Φ y) * pdM a J y q c := by
    intro a b c
    rw [pd_pullback2 hc hFs hF hy, ← tri]
    simp only [Finset.sum_add_distrib]
  have rot1 : ∑ e, ∑ p, ∑ q, J y e b * J y p c * J y q a * pd e (FV p q) (Φ y) =
      ∑ e, ∑ p, ∑ q, J y e a * J y p b * J y q c * pd p (FV q e) (Φ y) := by
    rw [sum_rot3 (fun e p q => J y e b * J y p c * J y q a * pd e (FV p q) (Φ y))]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have rot2 : ∑ e, ∑ p, ∑ q, J y e c * J y p a * J y q b * pd e (FV p q) (Φ y) =
      ∑ e, ∑ p, ∑ q, J y e a * J y p b * J y q c * pd q (FV e p) (Φ y) := by
    rw [sum_rot3_prime (fun e p q => J y e c * J y p a * J y q b * pd e (FV p q) (Φ y))]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have hrhs : ∑ e, ∑ p, ∑ q, J y e a * J y p b * J y q c * faradayCyclic FV e p q (Φ y) =
      ∑ e, ∑ p, ∑ q, J y e a * J y p b * J y q c * pd e (FV p q) (Φ y) +
      ∑ e, ∑ p, ∑ q, J y e a * J y p b * J y q c * pd p (FV q e) (Φ y) +
      ∑ e, ∑ p, ∑ q, J y e a * J y p b * J y q c * pd q (FV e p) (Φ y) := by
    simp only [faradayCyclic, mul_add, Finset.sum_add_distrib]
  rw [hrhs]
  unfold faradayCyclic
  rw [← rot1, ← rot2, split a b c, split b c a, split c a b]
  have p1 := pair a b c
  have p2 := pair b c a
  have p3 := pair c a b
  linarith
end


open scoped ContDiff
open Matrix
namespace ExactVacuumAtlas.EinsteinMaxwell

/-- A regular metric, its inverse and a smooth two-form solving the three Einstein–Maxwell equations on an open coordinate domain. -/
structure ChartSolution (U : Set (Pt 4)) where
  metric : Metric 4
  inverse : Metric 4
  field : TwoForm 4
  regular : MetricData metric inverse U
  smoothField : ∀ i j, ContDiffOn ℝ ∞ (field i j) U
  skew : ∀ p ∈ U, ∀ i j, field i j p = -field j i p
  einstein : ∀ p ∈ U, ∀ i j, einsteinMaxwell metric inverse field i j p = 0
  maxwell : ∀ p ∈ U, ∀ i, maxwellDiv metric inverse field i p = 0
  closed : ∀ p ∈ U, ∀ i j k, faradayCyclic field i j k p = 0

/-- Express a solution in new coordinates, with metric, inverse metric and Faraday coefficients specified on the new domain. -/
noncomputable def ChartSolution.rechart {U V : Set (Pt 4)} {Φ : Pt 4 → Pt 4}
    {J K : Pt 4 → Matrix (Fin 4) (Fin 4) ℝ} (s : ChartSolution V) (hc : CoordChange U V Φ J K)
    (g gi : Metric 4) (F : TwoForm 4)
    (hg : ∀ p ∈ U, metricMatrix g p = (J p)ᵀ * metricMatrix s.metric (Φ p) * J p)
    (hgi : ∀ p ∈ U, metricMatrix gi p = K p * metricMatrix s.inverse (Φ p) * (K p)ᵀ)
    (hF : ∀ p ∈ U, metricMatrix F p = (J p)ᵀ * metricMatrix s.field (Φ p) * J p) : ChartSolution U where
  metric := g
  inverse := gi
  field := F
  regular := MetricData.transport hc s.regular hg hgi
  smoothField i j := by
    have hs : SmoothOn (metricMatrix s.field) V := s.smoothField
    exact ((hc.smoothOn_jac.transpose.mul (hs.comp hc.smooth hc.mapsTo)).mul hc.smoothOn_jac
      |>.congr fun p hp => (hF p hp).symm) i j
  skew p hp i j := by
    have hs : (metricMatrix s.field (Φ p))ᵀ = -metricMatrix s.field (Φ p) := by
      ext a b
      exact s.skew _ (hc.mapsTo hp) b a
    have ht : (metricMatrix F p)ᵀ = -metricMatrix F p := by
      rw [hF p hp,Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,hs]
      simp only [Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_assoc]
    exact congrFun (congrFun ht j) i
  einstein p hp i j := by
    have hz : Matrix.of (fun a b => einsteinMaxwell s.metric s.inverse s.field a b (Φ p)) = 0 := by
      ext a b
      exact s.einstein _ (hc.mapsTo hp) a b
    have he := Variation.einsteinMaxwell_transform hc s.regular hg hgi hF hp
    rw [hz,Matrix.mul_zero,Matrix.zero_mul] at he
    exact congrFun (congrFun he i) j
  maxwell p hp i := by
    rw [Variation.maxwellDiv_transform hc s.regular s.smoothField hg hgi hF hp]
    simp only [s.maxwell _ (hc.mapsTo hp),mul_zero,Finset.sum_const_zero]
  closed p hp i j k := by
    rw [Variation.faradayCyclic_transform hc s.smoothField s.skew hF hp]
    simp only [s.closed _ (hc.mapsTo hp),mul_zero,Finset.sum_const_zero]

end ExactVacuumAtlas.EinsteinMaxwell


