-- Prove2me | Definitions.Def_SparseHamiltonianNorm_Simulation_Coupling
-- name    : SparseHamiltonianNorm_Simulation_Coupling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:57.900907+00:00
-- url     : https://prove2.me/theorems/9c815502-d9eb-482d-ab40-57c62ef1502f
-- title:
--   Continuous Volterra coupling and its transfer family
-- statement:
--   For finite complex system and address spaces, set $a=\sqrt d\,\Lambda$, $\gamma=\sqrt{2a}$, and $\mathcal Q=L^2([0,t];\mathbb C^e)$ with Lebesgue measure. For a system vector $\xi$ and history $q$, define
--   $$\psi(r)=e^{-ar}\xi-i\gamma\int_0^r e^{-a(r-u)}V^\dagger q(u)\,du,\quad g(r)=q(r)-i\gamma V\psi(r).$$
--   The coupling is $W_t(\xi,q)=(\psi(t),g)$. Its four blocks are extracted from this map, with the private Cayley query inserted in $C$ and $A$. The transfer matrix is the actual $D+zC(I-zA)^{-1}B$ on the history space. The inverse is total outside its intended domain; Proposition 9 asserts its bijectivity throughout the open disk.
--
--   The disk-response formula and the rational phase Hamiltonian are separate explicit functions, so their equality to the transfer family is a theorem. The boundary extension equals $\exp(-itH_\theta)$ except at tangent or resolvent singularities in $[-\pi,\pi]$, where it is set to the identity. Finiteness of that exceptional set is a theorem. Histories are genuine $L^2$ classes; the coupling theorem establishes square integrability of its output. The unitarity predicate uses the orthogonal-sum inner product, rather than a maximum product norm.
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), pp.13–15, Eqs. (33)–(49); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_SparseLift

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace SparseHamiltonianNorm.Simulation
open MeasureTheory Filter
open scoped BigOperators ComplexConjugate Topology
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Vec (n : ℕ) := EuclideanSpace ℂ (Fin n)
def historyMeasure (t : ℝ) : Measure ℝ := volume.restrict (Set.Icc 0 t)
abbrev History (e : ℕ) (t : ℝ) := Lp (Vec e) 2 (historyMeasure t)

/-- Rectangular matrix action between Euclidean spaces. -/
def rectAction {I J : Type*} [Fintype I] [Fintype J] (A : Matrix I J ℂ)
    (x : EuclideanSpace ℂ J) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (A.mulVec (WithLp.ofLp x))

/-- Class of an actual square-integrable field. The fallback is outside the intended domain;
the coupling theorem explicitly establishes membership for all its outputs. -/
def historyClass {e : ℕ} (t : ℝ) (f : ℝ → Vec e) : History e t :=
  if h : MemLp f 2 (historyMeasure t) then h.toLp f else 0

/-- Pointwise operator action on L² equivalence classes. -/
def historyLift {e : ℕ} (t : ℝ) (M : Matrix (Fin e) (Fin e) ℂ) (q : History e t) : History e t :=
  historyClass t (fun r => QAlgorithms.act M (q r))

/-- Source Eq. (34), with the integral evaluated on L² representatives. -/
def response {n e : ℕ} (d : ℕ) (Λ : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (ξ : Vec n) (q : ℝ → Vec e) (r : ℝ) : Vec n :=
  let a := Real.sqrt d * Λ
  let γ := Real.sqrt (2 * a)
  (Real.exp (-a * r) : ℂ) • ξ - (Complex.I * (γ : ℂ)) •
    ∫ u in (0 : ℝ)..r, (Real.exp (-a * (r - u)) : ℂ) • (rectAction V.conjTranspose) (q u)

/-- Source Eq. (35)'s private output field. -/
def outputField {n e : ℕ} (d : ℕ) (Λ : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (ξ : Vec n) (q : ℝ → Vec e) (r : ℝ) : Vec e :=
  q r - (Complex.I * (Real.sqrt (2 * (Real.sqrt d * Λ)) : ℂ)) •
    (rectAction V) (response d Λ V ξ q r)

/-- Continuous Volterra coupling W_t, Eqs. (34)--(39), independent of M. -/
def coupling {n e : ℕ} (d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (x : Vec n × History e t) : Vec n × History e t :=
  (response d Λ V x.1 x.2 t, historyClass t (outputField d Λ V x.1 x.2))

/-- Unitary on the orthogonal sum, with its sum inner product (not the max product norm). -/
def IsSumUnitary {n e : ℕ} {t : ℝ}
    (W : (Vec n × History e t) → (Vec n × History e t)) : Prop :=
  Function.Bijective W ∧
  (∀ (c : ℂ) x y, W (c • x + y) = c • W x + W y) ∧
  (∀ x y, inner ℂ (W x).1 (W y).1 + inner ℂ (W x).2 (W y).2 =
    inner ℂ x.1 y.1 + inner ℂ x.2 y.2)

/-- The blocks D,C0,B,A0 of the explicitly computed coupling. -/
def couplingD {n e : ℕ} (d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ) (x : Vec n) : Vec n :=
  (coupling d Λ t V (x, 0)).1
def couplingB {n e : ℕ} (d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ) (x : Vec n) : History e t :=
  (coupling d Λ t V (x, 0)).2
def couplingC {n e : ℕ} (d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (M : Matrix (Fin e) (Fin e) ℂ) (q : History e t) : Vec n :=
  (coupling d Λ t V (0, historyLift t (cayley M) q)).1
def couplingA {n e : ℕ} (d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (M : Matrix (Fin e) (Fin e) ℂ) (q : History e t) : History e t :=
  (coupling d Λ t V (0, historyLift t (cayley M) q)).2

/-- Actual resolvent I-zA, whose invertibility in the disk is asserted, not assumed. -/
def historyResolvent {n e : ℕ} (d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (M : Matrix (Fin e) (Fin e) ℂ) (z : ℂ) (q : History e t) : History e t :=
  q - z • couplingA d Λ t V M q

/-- Transfer function Eq. (42), using the inverse of the actual history resolvent. -/
def transfer {n e : ℕ} (d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (M : Matrix (Fin e) (Fin e) ℂ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (couplingD d Λ t V (QAlgorithms.ket j) + z • couplingC d Λ t V M
    (Function.invFun (historyResolvent d Λ t V M z) (couplingB d Λ t V (QAlgorithms.ket j)))) i

/-- Explicit finite-dimensional response on the right of Eq. (43). -/
def diskResponse {n e : ℕ} (d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (M : Matrix (Fin e) (Fin e) ℂ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp ((-t * Real.sqrt d * Λ : ℝ) •
    (V.conjTranspose * (1 + z • cayley M) * (1 - z • cayley M)⁻¹ * V))

/-- Eq. (44). At singular phases this is only a total extension, never an asserted boundary identity. -/
def phaseH {n e : ℕ} (d : ℕ) (Λ : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (M : Matrix (Fin e) (Fin e) ℂ) (θ : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  let u : ℂ := Real.tan (θ / 2)
  (Real.sqrt d * Λ : ℝ) • (V.conjTranspose * ((2 : ℂ) • M - u • 1) * (1 + (2 * u) • M)⁻¹ * V)

/-- Exceptional phases restricted to the integration interval, so the source finite-set claim applies. -/
def exceptionalPhase {e : ℕ} (M : Matrix (Fin e) (Fin e) ℂ) (θ : ℝ) : Prop :=
  θ ∈ Set.Icc (-Real.pi) Real.pi ∧
    (Real.cos (θ / 2) = 0 ∨ (1 + (2 * (Real.tan (θ / 2) : ℂ)) • M).det = 0)

/-- Defined everywhere, with identity at the finite exceptional set; integrals ignore that set. -/
def boundaryResponse {n e : ℕ} (d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (M : Matrix (Fin e) (Fin e) ℂ) (θ : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  if exceptionalPhase M θ then 1 else evolution t (phaseH d Λ V M θ)

end SparseHamiltonianNorm.Simulation


