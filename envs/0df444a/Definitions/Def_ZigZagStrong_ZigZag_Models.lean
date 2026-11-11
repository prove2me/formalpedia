-- Prove2me | Definitions.Def_ZigZagStrong_ZigZag_Models
-- name    : ZigZagStrong_ZigZag_Models
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:23.132037+00:00
-- url     : https://prove2.me/theorems/ce80c728-e37f-4c8b-8e9d-c2343362137f
-- title:
--   Sampling laws, regular limits and strong convergence
-- statement:
--   For $d=2r$, the permutation model is the uniform law on $r$ independent permutations, with inverse ports in reverse order. The matching model uses independent fixed-point-free involutions at even sizes; the involution model allows fixed points. Their infinite limits use the genuine left regular representations of $F_r$ and $\mathbb Z_2^{*d}$ on complex $\ell^2$ spaces.
--
--   For varying sample spaces with laws $p_n$, convergence in probability is
--   $$\forall\eta>0,\quad p_n\{|X_n-a|>\eta\}\longrightarrow0.$$
--   Strong convergence requires this for the norms of every scalar-coefficient noncommutative star polynomial. Matrix polynomials and permutation objects reuse the published StrongConv definition. The coefficient norm is the sum of the operator norms of the coefficient matrices. Spectral distance is the full Hausdorff distance between complex spectra; self-adjoint spectra lie on the real axis. These objects serve both the qualitative and quantitative results.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Definitions 2.2–2.3, Proposition 2.5 and Theorem 2.6, pp. 8–9; Definitions 3.4, 3.7, pp. 11–12.

import Definitions.Def_ZigZagStrong_ZigZag_Operators

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

abbrev FreeInvolutions (d : ℕ) := Monoid.CoprodI (fun _ : Fin d => Multiplicative (ZMod 2))

def involutionGenerator {d : ℕ} (i : Fin d) : FreeInvolutions d :=
  Monoid.CoprodI.of (Multiplicative.ofAdd (1 : ZMod 2)) (i := i)

def permutationGenerator {r : ℕ} (i : Fin (2*r)) : FreeGroup (Fin r) :=
  if h : i.val < r then FreeGroup.of ⟨i.val, h⟩
  else (FreeGroup.of ⟨2*r-1-i.val, by omega⟩)⁻¹

def permutationPorts {r n : ℕ} (σ : Fin r → Equiv.Perm (Fin n))
    (i : Fin (2*r)) : Equiv.Perm (Fin n) :=
  if h : i.val < r then σ ⟨i.val, h⟩
  else (σ ⟨2*r-1-i.val, by omega⟩)⁻¹

abbrev Involution (n : ℕ) := {τ : Equiv.Perm (Fin n) // ∀ x, τ (τ x) = x}
abbrev Matching (n : ℕ) := {τ : Equiv.Perm (Fin n) // (∀ x, τ (τ x) = x) ∧ ∀ x, τ x ≠ x}

instance (n : ℕ) : Fintype (Involution n) := Fintype.ofFinite _
instance (n : ℕ) : Fintype (Matching n) := Fintype.ofFinite _

/-- Independent uniform tuples, as normalized counts. No law is assigned to odd-size matchings. -/
def finiteLaw {Ω : Type*} [Fintype Ω] (E : Set Ω) : ℝ :=
  StrongConv.uniformProb (fun ω => ω ∈ E)

/-- Convergence in probability for possibly varying sample spaces and their genuine laws. -/
def ProbConverges {Ω : ℕ → Type*} (p : ∀ n, Set (Ω n) → ℝ)
    (X : ∀ n, Ω n → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => p n {ω | ε < |X n ω - a|}) atTop (𝓝 0)

section Convergence
variable {r : ℕ} {Ω E : ℕ → Type*} {F : Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)] [∀ n, CompleteSpace (E n)]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Definition 2.3: every scalar-coefficient noncommutative *-polynomial. -/
def StrongConvergence (p : ∀ n, Set (Ω n) → ℝ)
    (U : ∀ n, Ω n → Fin r → E n →L[ℂ] E n) (u : Fin r → F →L[ℂ] F) : Prop :=
  ∀ P : StrongConv.NCPoly 1 r,
    ProbConverges p (fun n ω => ‖P.eval (U n ω)‖) ‖P.eval u‖

end Convergence

/-- Universal coefficient norm in source Theorem 2.6, not the full C*-norm of the reference. -/
def coefficientNorm {D r : ℕ} (P : StrongConv.NCPoly D r) : ℝ :=
  ∑ w ∈ P.support, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (P w)‖

def permutationLimit {r c : ℕ} (H : Gadget (2*r) c) :=
  zigzag H Fin.revPerm (fun i => StrongConv.leftReg (permutationGenerator i))

def matchingLimit {d c : ℕ} (H : Gadget d c) :=
  zigzag H (Equiv.refl _) (fun i => regularL2 (involutionGenerator i))

def permutationNew {r c n : ℕ} (H : Gadget (2*r) c) (σ : Fin r → Equiv.Perm (Fin n)) :=
  newAdj H Fin.revPerm (permutationPorts σ)

def matchingNew {d c n : ℕ} (H : Gadget d c) (τ : Fin d → Matching n) :=
  newAdj H (Equiv.refl _) (fun i => (τ i).val)

def involutionNew {d c n : ℕ} (H : Gadget d c) (τ : Fin d → Involution n) :=
  newAdj H (Equiv.refl _) (fun i => (τ i).val)

def spectrumDistance {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (T : E →L[ℂ] E) (U : F →L[ℂ] F) : ℝ :=
  Metric.hausdorffDist (spectrum ℂ T) (spectrum ℂ U)

def topEdge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : E →L[ℂ] E) : ℝ :=
  sSup (Complex.re '' spectrum ℂ T)

def bottomEdge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : E →L[ℂ] E) : ℝ :=
  sInf (Complex.re '' spectrum ℂ T)

/-- The unitary tuples themselves carry their Borel probability laws, as on source p. 7. -/
abbrev UnitaryTuple (r : ℕ) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] :=
  {U : Fin r → E →L[ℂ] E // ∀ i, star (U i) * U i = 1 ∧ U i * star (U i) = 1}

instance (r : ℕ) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] : MeasurableSpace (UnitaryTuple r E) :=
  borel _

end ZigZagStrong.ZigZag


