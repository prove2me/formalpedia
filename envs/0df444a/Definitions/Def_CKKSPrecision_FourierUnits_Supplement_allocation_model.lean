-- Prove2me | Definitions.Def_CKKSPrecision_FourierUnits_Supplement_allocation_model
-- name    : CKKSPrecision_FourierUnits_Supplement_allocation_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:24:55.977652+00:00
-- url     : https://prove2.me/theorems/37fd01e9-ab92-4224-9f6b-a27201a48a36
-- title:
--   Algorithm 1, allocation sets and finite root/sign certificates
-- statement:
--   Let the finite circuit analysis produce rational Laurent error bounds $E_{\mathrm{out},j}(t)$, output magnitude bounds $A_{\mathrm{out},j}$, modulus $Q_{\mathrm{out}}$ and positive rational scale $\Delta_{\mathrm{out}}$. For a set $S$ of required slots and rational thresholds $\varepsilon_j$, put
--   $$
--   F(t)=\frac1r\sum_{j=0}^{r-1}E_{\mathrm{out},j}(t),\qquad
--   T=\frac{Q_{\mathrm{out}}}{2\Delta_{\mathrm{out}}}-\frac1r\sum_{j=0}^{r-1}A_{\mathrm{out},j}.
--   $$
--   Both sums include every slot. Define
--   $$
--   J=\{t\ge1:F(t)<T,\ E_{\mathrm{out},j}(t)\le\varepsilon_j\ (j\in S)\}.
--   $$
--   Solve is the exact solution-set interface for a rational Laurent inequality on $t\ge1$, preserving strict and non-strict endpoints. Algorithm 1 performs the node analysis, computes $F,T$, returns the empty set when $T\le0$, otherwise intersects the recovery solution with the finitely many precision solutions and returns their image under $\log_2$.
--
--   Termination is expressed in the theorem by a finite root/sign certificate: a finite cut set, flags for its points, and finitely many flags for the open cells between cuts. Every cut must be a root of a nonzero polynomial obtained by explicitly clearing a defining Laurent constraint, or of the domain-boundary polynomial $X-1$. The certificate's denoted set must equal $J$; it is a conclusion rather than an assumed solver oracle. Point flags retain endpoint inclusion. Zero constraint polynomials cannot certify cuts.
--
--   Success means that centered decryption returns the entire computed restored polynomial, and that the decoded error is at most $\varepsilon_j$ on required slots. This definition supplies the exact-set and recovery interfaces for all three clauses of Theorem 6.1.
-- source:
--   Zhaoyang Liang, Runkun Liu, Jingwei Fang, Dan Ding, STOC 2027 submission #148 (October 2026), pp. 11–12 (PDF pp. 13–14), §6.1, (13)–(15), Algorithm 1 lines 1–9 and its termination argument.

import Definitions.Def_CKKSPrecision_FourierUnits_Supplement_circuit_model

set_option autoImplicit false
noncomputable section

namespace CKKSPrecision.FourierUnits.Supplement

structure Requirements (r : ℕ+) where
  required : Finset (Slot r)
  tolerance : Slot r → ℚ

def outputAnalysis {r : ℕ+} (w : Weights r) (c : Circuit r) : Analysis r :=
  atAnalysis (analyze w c) c.output

def averageError {r : ℕ+} (w : Weights r) (c : Circuit r) : Laurent :=
  lc (1 / (r : ℕ)) * ∑ j, (outputAnalysis w c).error j

def recoveryThreshold {r : ℕ+} (w : Weights r) (c : Circuit r) : ℚ :=
  let out := outputAnalysis w c
  (out.modulus : ℚ) / (2 * out.scale) - (∑ j, out.magnitude j) / (r : ℕ)

/-- Equation (15), preserving the distinct strict and non-strict tests. -/
def feasible {r : ℕ+} (w : Weights r) (c : Circuit r) (req : Requirements r) : Set ℝ :=
  {t | 1 ≤ t ∧ leval (averageError w c) t < (recoveryThreshold w c : ℝ) ∧
    ∀ j ∈ req.required, leval ((outputAnalysis w c).error j) t ≤ (req.tolerance j : ℝ)}

inductive Comparison where
  | strict
  | weak

def Solve (f : Laurent) (b : ℚ) (comparison : Comparison) : Set ℝ :=
  {t | 1 ≤ t ∧ match comparison with
    | .strict => leval f t < (b : ℝ)
    | .weak => leval f t ≤ (b : ℝ)}

def logTwo (t : ℝ) : ℝ := Real.log t / Real.log 2

/-- Algorithm 1 lines 1–9. analyze performs the finite node loop; the early return is explicit.
    Solve is its specified exact-set interface. Termination is certified separately by finite
    root/sign data, rather than claimed from a noncomputable set comprehension. -/
def algorithm1 {r : ℕ+} (w : Weights r) (c : Circuit r) (req : Requirements r) : Set ℝ := by
  classical
  let a := analyze w c
  let out := atAnalysis a c.output
  let f := lc (1 / (r : ℕ)) * ∑ j, out.error j
  let threshold := (out.modulus : ℚ) / (2 * out.scale) - (∑ j, out.magnitude j) / (r : ℕ)
  if threshold ≤ 0 then exact ∅
  else
    let j := Solve f threshold .strict
    let j := req.required.toList.foldl (fun acc k => acc ∩ Solve (out.error k) (req.tolerance k) .weak) j
    exact logTwo '' j

/-- Explicit denominator clearing: the shift dominates every negative Laurent exponent. -/
def clearingShift (f : Laurent) : ℕ := f.coeff.support.sup (fun k => k.natAbs)

def cleared (f : Laurent) (b : ℚ) : Polynomial ℚ :=
  (f - lc b).coeff.sum (fun k q => Polynomial.monomial (k + (clearingShift f : ℤ)).toNat q)

/-- The domain boundary 1 is also a rational polynomial root. Zero constraint polynomials are
    retained in the list but are excluded when certifying a cut. -/
def boundaryPolynomials {r : ℕ+} (w : Weights r) (c : Circuit r) (req : Requirements r) : List (Polynomial ℚ) :=
  [Polynomial.X - 1, cleared (averageError w c) (recoveryThreshold w c)] ++
    req.required.toList.map (fun j => cleared ((outputAnalysis w c).error j) (req.tolerance j))

/-- Finite sign-cell certificate. Point flags preserve endpoint inclusion; cell flags are indexed
    by subsets of the finite cut set, hence there are only finitely many of them. -/
structure RangeCertificate where
  cuts : Finset ℝ
  pointFlag : {x // x ∈ cuts} → Bool
  cellFlag : {s : Finset ℝ // s ⊆ cuts} → Bool

def RangeCertificate.denotes (cert : RangeCertificate) : Set ℝ := by
  classical
  exact {t | if h : t ∈ cert.cuts then cert.pointFlag ⟨t, h⟩ = true else
    cert.cellFlag ⟨cert.cuts.filter (fun x => x < t), Finset.filter_subset _ _⟩ = true}

def RangeCertificate.Valid (cert : RangeCertificate) (polys : List (Polynomial ℚ)) : Prop :=
  ∀ x ∈ cert.cuts, ∃ p ∈ polys, p ≠ 0 ∧ Polynomial.aeval x p = 0

/-- Recovery is equality of entire integral polynomials; precision is tested only on required slots. -/
def Successful {r : ℕ+} (w : Weights r) (c : Circuit r) (req : Requirements r)
    (p s : Scalar r) (noise : ℕ → Noise r) : Prop :=
  let out := outputAnalysis w c
  let logical := atLogical (logicalRun w c p s noise) c.output
  center out.modulus (p * phase s (noise c.output).ct) = logical.message ∧
    ∀ j ∈ req.required,
      ‖decoded out.modulus out.scale p s (noise c.output).ct j - logical.value j‖ ≤ (req.tolerance j : ℝ)

end CKKSPrecision.FourierUnits.Supplement


