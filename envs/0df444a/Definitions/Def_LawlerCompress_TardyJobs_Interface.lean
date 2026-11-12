-- Prove2me | Definitions.Def_LawlerCompress_TardyJobs_Interface
-- name    : LawlerCompress_TardyJobs_Interface
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:26:28.989435+00:00
-- url     : https://prove2.me/theorems/09a6252f-15cf-4be1-8185-fe76c41ef4da
-- title:
--   Input and output encoding and bounded execution specifications
-- statement:
--   The input array begins with m,n and then the triples (p_j,d_j,w_j) in input order. No sorting or maximum-due-date cell is supplied. A returned schedule address points to 2n cells: the pair for input job j contains its machine and its zero-based position on that machine. The entire region must lie inside the execution's space bound. The returned value must be a nonnegative attained optimum.
--
--   Let d=d_max, g=n+d^{m+1}, and B=2+m+n+d+Σ_j w_j. The resource envelopes are
--
--   $$T=Cg(1+\ln g),\quad S_v=C(n+d^m),\quad S_s=C(n+d^m)+Cd^{m+1}(1+\ln d),\quad W=B^c.$$
--
--   Time is rounded down to a natural number of executed steps; space is a natural number of addressed cells. The program enters at procedure zero and returns through local zero. Polynomial word limits and a call-depth limit are conclusion-side execution bounds, not restrictions on input values.
--
--   These specifications connect the scheduling mathematics to the published Light language without assigning time to an abstract solver.
--
--   **Formalization Note** Light counts arithmetic, comparisons, memory operations and control flow. Its operations are addition, subtraction and multiplication. The explicit logarithmic envelopes serialize the proof's bounds on pp. 5, 7–8.
-- source:
--   Klaus Jansen, Björn Schumacher, Corinna Wambsganz, Compressing the Lawler-Moore Dynamic Program for Weighted Tardy Jobs, STOC 2027 submission #354 (October 2026), p. 2, Theorem 1.1 and §1 model; pp. 5, 7–8, proofs of Lemmas 2.3, 3.4, 3.5

import Definitions.Def_LawlerCompress_TardyJobs_DynamicProgram
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

def encode {m : ℕ} (I : Instance m) : List ℤ :=
  [m, I.n] ++ (List.finRange I.n).flatMap (fun j => [I.p j, I.d j, I.w j])

def start {m : ℕ} (I : Instance m) : Light.State :=
  ⟨Light.frame [], Light.memOf (encode I)⟩

def entry : Light.Stmt := .call 0 [] 0

def wordBase {m : ℕ} (I : Instance m) : ℕ :=
  2 + m + I.n + dmax I + totalWeight I

/-- Integer-valued output must be an attained natural-number optimum. -/
def ValueOutput {m : ℕ} (I : Instance m) (σ : Light.State) : Prop :=
  ∃ v : ℕ, σ.loc 0 = v ∧ IsOptValue I v

/-- Address and the entire 2n-cell output region lie within the execution space.
Cells are indexed by original input jobs, with zero-based machine and list position. -/
def OutputSchedule {m : ℕ} (I : Instance m) (S : ℕ)
    (τ : JobLists I) (σ : Light.State) : Prop :=
  0 ≤ σ.loc 0 ∧ (σ.loc 0).toNat + 2 * I.n ≤ S ∧
    ∀ r, ∀ q : Fin (τ r).length,
      let j := (τ r).get q
      σ.mem ((σ.loc 0).toNat + 2 * j.val) = r.val ∧
      σ.mem ((σ.loc 0).toNat + 2 * j.val + 1) = q.val

def EndpointOutput {m : ℕ} (I : Instance m) (S : ℕ) (σ : Light.State) : Prop :=
  0 ≤ σ.loc 0 ∧ (σ.loc 0).toNat + I.n ≤ S ∧
    ∀ j, σ.mem ((σ.loc 0).toNat + j.val) = a I j

def sizeTerm {m : ℕ} (I : Instance m) : ℕ := I.n + dmax I ^ (m + 1)

noncomputable def timeBound {m : ℕ} (I : Instance m) (C : ℕ) : ℕ :=
  ⌊(C : ℝ) * sizeTerm I * (1 + Real.log (sizeTerm I))⌋₊

def baseSpace {m : ℕ} (I : Instance m) (C : ℕ) : ℕ := C * (I.n + dmax I ^ m)

noncomputable def scheduleSpace {m : ℕ} (I : Instance m) (C : ℕ) : ℝ :=
  baseSpace I C + (C : ℝ) * dmax I ^ (m + 1) * (1 + Real.log (dmax I))

def limits {m : ℕ} (I : Instance m) (c S D : ℕ) : Light.Limits :=
  ⟨(wordBase I : ℤ) ^ c, S, D⟩

end LawlerCompress.TardyJobs


