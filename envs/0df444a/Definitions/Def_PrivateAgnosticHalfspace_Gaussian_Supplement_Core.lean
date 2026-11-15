-- Prove2me | Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Supplement_Core
-- name    : PrivateAgnosticHalfspace_Gaussian_Supplement_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:05:15.407734+00:00
-- url     : https://prove2.me/theorems/be4b5293-f2c1-4e9c-916e-a5fd5cd6b23d
-- title:
--   Supplement: finite selection, spectral cover operations and costed execution
-- statement:
--   Let $x\in\mathbb R^d$ have its Euclidean norm and Borel structure. A halfspace is a pair $(w,t)$ with classifier $x\mapsto\operatorname{sign}(\langle w,x\rangle+t)$, with positive sign at zero. Ordered samples are cut into public prefix blocks. Finite indexed validation reuses the published exponential-mechanism law, so repeated entries retain their weights.
--
--   The spectral projection at cutoff $a$ is
--   $$\Pi_{\ge a}(M)x=\sum_{\lambda_i\ge a}\langle e_i,x\rangle e_i.$$
--   Coordinate Gram–Schmidt applied to its projected coordinate vectors fixes a basis. A normalized rational-coordinate grid with mesh at most $\gamma/(4\sqrt{k})$ gives a finite $\gamma$-net of its $k$-dimensional unit sphere; at $k=0$ this list is empty. The normal quantile is the infimum definition of $\Phi^{-1}$, used only at probabilities strictly between zero and one.
--
--   These operations support the supplement's sample-only algorithms. A realization predicate identifies a measurable probability mechanism with a specified law; accuracy and privacy are separate theorem conclusions. Accuracy integrates over iid data and the mechanism's own coins.
--
--   **Formalization Note** Cost is accumulated by execution on the published sampling real RAM. The explicit extension charges one operation for sine, cosine, $\pi$, and the inverse normal CDF. Computing a symmetric spectral projection from a $d\times d$ matrix costs $1+d^3$, the source's spectral-operation convention. Scalar instructions retain the published semantics and rational literals. Programs have no population-label or optimum oracle. Halfspace implementations must halt on every tape, respect the work bound, have measurable output, and realize the specified output law. Integer rounding uses public loops; no unit-cost real-to-integer instruction is introduced.
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, Privacy for Free in Efficient Agnostic Halfspace Learning, STOC 2027 submission #1006 (October 2026), canonical held submission (not a proceedings-acceptance claim), pp.9,12,16,28–29,32–34, Algorithms 2–4 and Appendix D.1

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian.Supplement

noncomputable section

abbrev Halfspace (d : ℕ) := Vec d × ℝ

def classifier {d : ℕ} (h : Halfspace d) : Vec d → Bool := affine d h.1 h.2

def axis (d : ℕ) : Vec d := WithLp.toLp 2 fun i => if i.val = 0 then 1 else 0

def normalize {d : ℕ} (v : Vec d) : Vec d := if ‖v‖ = 0 then axis d else ‖v‖⁻¹ • v

def radial {ι : Type*} [Fintype ι] (R : ℝ) (v : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (R / max R ‖v‖) • v

/-- Public prefix/discard blocks; no sample-dependent partition. -/
def block {Z : Type*} (S : List Z) (start len : ℕ) : List Z := (S.drop start).take len

def average {E : Type*} [AddCommGroup E] [Module ℝ E] (xs : List E) : E :=
  (xs.length : ℝ)⁻¹ • xs.sum

/-- Indexed validation retains multiplicities. Nonemptiness and normalization are conclusions. -/
def select {d : ℕ} {A : Type*} [MeasurableSpace A] (hs : List A)
    (decode : A → Vec d → Bool) (ε : ℝ) (S : List (Example d)) : Measure A :=
  let names := fun j : Fin hs.length => hs[j.val]
  (validationLaw (fun j => decode (names j)) ε (fun i : Fin S.length => S[i.val])).map names

def logs (α β ε δ : ℝ) : ℝ :=
  1 + Real.log (1 / α) + Real.log (1 / β) + Real.log (1 / ε) + Real.log (1 / δ)

/-- No default-zero infimum is used as an attained integer schedule without a conclusion
asserting the corresponding condition. -/
def firstSize (condition : ℕ → Prop) : ℕ :=
  by
    classical
    exact if h : ∃ n, condition n then Nat.find h else 0

/-- Measurable probability mechanism equal to a prescribed sample-only law. The DP and
accuracy requirements are subsequent theorem conclusions, never fields of a learner record. -/
def Realizes {d n : ℕ} {Y : Type*} [MeasurableSpace Y]
    (law : List (Example d) → Measure Y)
    (A : PrivateUniformGen.Characterization.Mechanism (Example d) Y n) : Prop :=
  (∀ S, (A S : Measure Y) = law (List.ofFn S)) ∧
  Measurable (fun S => A S)

/-- Accuracy includes the joint law of iid samples and all algorithm coins. -/
def Accurate {d n : ℕ} {Y : Type*} [MeasurableSpace Y]
    (A : PrivateUniformGen.Characterization.Mechanism (Example d) Y n)
    (decode : Y → Vec d → Bool) (P : Measure (Example d)) (bound β : ℝ) : Prop :=
  (Measure.pi (fun _ : Fin n => P)).bind (fun S => (A S : Measure Y))
    {o | error P (decode o) ≤ bound} ≥ ENNReal.ofReal (1 - β)

/-- Symmetrization permits total spectral operations without certificates as inputs. -/
def symmetrize {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => (A i j + A j i) / 2

theorem symmetrize_hermitian {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    (symmetrize A).IsHermitian := by
  ext i j
  simp [symmetrize, Matrix.conjTranspose_apply, add_comm]

/-- Orthogonal spectral projection; independent of the choice of eigenvectors inside
repeated eigenspaces. Gram--Schmidt below fixes a coordinate-based enumeration. -/
def spectralProjection {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (a : ℝ) : Vec d → Vec d :=
  let h := symmetrize_hermitian A
  fun x => ∑ i, if a ≤ h.eigenvalues i then
    (inner ℝ (h.eigenvectorBasis i) x) • h.eigenvectorBasis i else 0

def spectralBasis {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (a : ℝ) : List (Vec d) :=
  let cols := fun i : Fin d => spectralProjection A a (WithLp.toLp 2 (Pi.single i 1))
  (List.ofFn fun i => InnerProductSpace.gramSchmidtNormed ℝ cols i).filter (fun v => v ≠ 0)

/-- Coordinate-grid sphere net. It is empty for a zero-dimensional subspace. Grid spacing
γ/(4√k) and normalization give a γ-net, with log size O(k log(k/γ)). -/
def sphereNet {d : ℕ} (basis : List (Vec d)) (γ : ℝ) : List (Vec d) :=
  let k := basis.length
  let N := max 1 ⌈4 * Real.sqrt (k : ℝ) / γ⌉₊
  let grid := List.ofFn fun j : Fin ((2 * N + 1) ^ k) =>
    ∑ i : Fin k,
      (((((j.val / (2 * N + 1) ^ i.val) % (2 * N + 1) : ℕ) : ℝ) - N) / N) • basis[i.val]
  (grid.filter fun v => 0 < ‖v‖ ∧ ‖v‖ ≤ 1 + γ / 2).map normalize

/-- Gaussian quantile is used only on (0,1); the domain is enforced by the algorithm's clip. -/
def normalQuantile (u : ℝ) : ℝ := sInf {x : ℝ | u ≤ (gaussianReal 0 1).real (Set.Iic x)}

/-- Operational extension of the published RAM: sin/cos/π/normal quantile cost one, and
symmetric spectral projection costs 1+d³ (including writing d² entries). The latter reads
one row-major matrix and a cutoff, and writes its orthogonal spectral projection. This
explicitly adopts the source's O(d³) spectral-operation convention. -/
inductive Instruction where
  | base : PolySampIso.Instr → Instruction
  | sin (dst src : ℕ)
  | cos (dst src : ℕ)
  | pi (dst : ℕ)
  | quantile (dst src : ℕ)
  | spectral (dimension source destination cutoff : ℕ)

abbrev Code := List Instruction

def Admissible (code : Code) : Prop :=
  ∀ op ∈ code, match op with
    | .base (.core (.const _ value)) => ∃ q : ℚ, value = q
    | .base (.core .accept) | .base (.core .reject) => False
    | _ => True

def scalarCode (code : Code) : PolySampIso.Program := code.map fun op =>
  match op with | .base i => i | _ => .core (.const 0 0)

def step (code : Code) (ω : PolySampIso.Streams) (s : PolySampIso.State) : PolySampIso.State :=
  if s.halted then s else
  let setReg := fun dst v => { s with
    core := { s.core with pc := s.core.pc + 1, regs := Function.update s.core.regs dst v }
    work := s.work + 1 }
  match code[s.core.pc]? with
  | some (.base _) | none => PolySampIso.step (scalarCode code) ω s
  | some (.sin dst src) => setReg dst (Real.sin (s.core.regs src))
  | some (.cos dst src) => setReg dst (Real.cos (s.core.regs src))
  | some (.pi dst) => setReg dst Real.pi
  | some (.quantile dst src) => setReg dst (normalQuantile (s.core.regs src))
  | some (.spectral dim src dst cut) =>
    let d := (s.core.ptrs dim).toNat
    let A : Matrix (Fin d) (Fin d) ℝ := fun i j =>
      s.core.mem (s.core.ptrs src + i.val * d + j.val)
    let Q := fun j : Fin d => spectralProjection A (s.core.regs cut) (WithLp.toLp 2 (Pi.single j 1))
    { s with
      core := { s.core with
        pc := s.core.pc + 1
        mem := fun a => if h : 0 ≤ a - s.core.ptrs dst ∧ a - s.core.ptrs dst < d * d then
          Q ⟨((a - s.core.ptrs dst).toNat % d), by
              have : 0 < d := by nlinarith [h.2]
              exact Nat.mod_lt _ this⟩
            ⟨((a - s.core.ptrs dst).toNat / d), by
              have hd : 0 < d := by nlinarith [h.2]
              apply (Nat.div_lt_iff_lt_mul hd).mpr
              omega⟩
          else s.core.mem a }
      work := s.work + 1 + d ^ 3 }

def run (code : Code) (input : ℕ → ℝ) (ω : PolySampIso.Streams) (fuel : ℕ) : PolySampIso.State :=
  (step code ω)^[fuel] (initialState 0 0 0 input)

/-- Fixed public parameters followed by the ordered sample. No population law is available. -/
def input {d : ℕ} (params : List ℝ) (S : List (Example d)) : ℕ → ℝ :=
  let table := params ++ S.flatMap (fun z => (List.ofFn fun i : Fin d => z.1 i) ++ [label z.2])
  fun i => table.getD i 0

def readHalfspace (d : ℕ) (s : PolySampIso.State) : Halfspace d :=
  (PolySampIso.output d s, s.core.mem (-1 - (d : ℤ)))

/-- Exact operational implementation, including measurable output and charged work.
The budget is a bound on execution, not a freely assigned cost on a kernel. -/
def ImplementsHalfspace (code : Code) (fuel cost d : ℕ) (a : ℕ → ℝ)
    (ν : Measure (Halfspace d)) : Prop :=
  Admissible code ∧
  (∀ ω, let s := run code a ω fuel; s.halted = true ∧ s.work ≤ cost) ∧
  Measurable (fun ω => readHalfspace d (run code a ω fuel)) ∧
  PolySampIso.tape.map (fun ω => readHalfspace d (run code a ω fuel)) = ν

end
end PrivateAgnosticHalfspace.Gaussian.Supplement


